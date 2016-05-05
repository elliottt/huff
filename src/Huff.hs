{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Huff where

import qualified Huff.Compile as I
import qualified Huff.Input as Input
import qualified Huff.FF.Planner as I

import           Control.Monad (forM_,unless,when)
import qualified Data.Map.Strict as Map
import           Data.Maybe (mapMaybe)
import           Data.Proxy (Proxy(..))
import qualified Data.Set as Set
import qualified Data.Text as T
import           GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import           MonadLib (StateT,get,set,runM,Id)


[huff|

domain blocksWorld {

  type object = table | a | b | c

  predicate on(object, object), clear(object)

  operator stack-on-table(x) {
    value: $("Stack " ++ show x ++ " on table")
    requires: clear(x)
    effect: on(x,table)
  }

  operator stack(x : object, y : object) {
    value: $("Stack " ++ show x ++ " on " ++ show y)
    requires: clear(x), clear(y), not(is-table(y))
    effect: on(x,y), not(clear(y))
  }

}

problem blocksWorld1 {
  domain:
    blocksWorld

  init:
    on(a,b)
    on(b,table)
    on(c,table)
    clear(c)
    clear(a)

  goal:
    on(a,b)
    on(b,c)
    on(c,table)
    clear(a)
}

domain shopping {

  type place = supermarket    as "Supermarket"
             | hardware-store as "Hardware Store"
             | home           as "Home"

  type good  = hammer
             | drill
             | banana

  predicate at(place), sells(place,good), has(good)

  operator going(from : place, to : place) {
    value: $("Going from " ++ show from ++ " to " ++ show to ++ ".")
    requires: at(from)
    effect: not(at(from)), at(to)
  }

  operator buy(thing : good, from : place)
    value: $("Buying " ++ show thing ++ " from " ++ show from ++ ".")
    requires: at(from), sells(from,thing)
    effect: has(thing)

}

problem buyHammerAndBanana {

  domain shopping

  init
    at(home)

  goal
    at(home), has(hammer), has(banana)

}


|]


newtype Huff step a = Huff { unHuff :: StateT (RW step) Id a
                           } deriving (Functor,Applicative,Monad)

type Env = Map.Map T.Text (Set.Set T.Text)

data RW step = RW { rwOps :: [I.Operator step]
                    -- ^ Parameter-less operators
                  , rwPreds :: [I.Pred]
                    -- ^ Defined predicates
                  , rwTypes :: Env
                    -- ^ Types, with their inhabitants
                  , rwNext :: !Int
                  , rwInit :: [I.Literal]
                  , rwGoal :: [I.Term]
                  }

runHuff :: Huff step () -> (I.Problem,I.Domain step)
runHuff (Huff m) = (I.Problem { .. }, I.Domain { .. })
  where
  (_,rw) = runM m RW { rwOps   = []
                     , rwPreds = []
                     , rwTypes = Map.empty
                     , rwNext  = 0
                     , rwInit  = []
                     , rwGoal  = []
                     }

  domOperators = rwOps rw

  probObjects = [ I.Typed obj ty | (ty,objs) <- Map.toList (rwTypes rw)
                                 , obj       <- Set.toList objs ]

  -- XXX define the predicates
  probPreds = []

  probInit = rwInit rw

  probGoal = I.mkTAnd (rwGoal rw)


findPlan :: Huff step () -> IO (Maybe [step])
findPlan m =
  do let (prob,dom)   = runHuff m
     mbOps <- uncurry I.findPlan (I.compile prob dom)
     case mbOps of
       Just res -> return (Just (mapMaybe (I.opVal . Input.opVal) (I.resSteps res)))
       Nothing  -> return Nothing



newtype Type (ty :: Symbol) = Type T.Text
                              deriving (Show)

newType :: KnownSymbol sym => Proxy sym -> Huff step (Type sym)
newType p = Huff $
  do RW { .. } <- get
     let val = T.pack (symbolVal p)
     set RW { rwTypes = Map.alter add val rwTypes, .. }
     return (Type val)
  where
  add (Just objs) = Just objs
  add Nothing     = Just Set.empty


newtype Obj (ty :: Symbol) = Obj I.Arg
                             deriving (Show,Eq)

newObj :: T.Text -> Type sym -> Huff step (Obj ty)
newObj str (Type ty) = Huff $
  do RW { .. } <- get
     set RW { rwTypes = Map.alter add ty rwTypes, .. }
     return (Obj (I.AName str))
  where
  add (Just objs) = Just (Set.insert str objs)
  add Nothing     = Just (Set.singleton str)

objValue :: Obj ty -> T.Text
objValue (Obj (I.AName str)) = str
objValue _                   = error "quantified variable escaped"


-- Goal Descriptions -----------------------------------------------------------

class IsGD a where
  toGD :: a -> GD

toTerm :: IsGD a => a -> I.Term
toTerm a = fst (runM (unGD (toGD a)) 0)

newtype GD = GD { unGD :: StateT Int Id I.Term }

instance IsGD GD where
  toGD = id

goal :: IsGD a => a -> Huff step ()
goal gd = Huff $
  do RW { .. } <- get
     set RW { rwGoal = toTerm gd : rwGoal, .. }

orGD :: IsGD a => [a] -> GD
orGD gds = GD (I.mkTOr `fmap` mapM (unGD . toGD) gds)

andGD :: IsGD a => [a] -> GD
andGD gds = GD (I.mkTAnd `fmap` mapM (unGD . toGD) gds)

notGD :: IsGD a => a -> GD
notGD gd = GD (I.TNot `fmap` unGD (toGD gd))

(==>) :: (IsGD a, IsGD b) => a -> b -> GD
a ==> b = GD (I.TImply <$> unGD (toGD a) <*> unGD (toGD b))

exists :: Type sym -> (Obj sym -> GD) -> GD
exists (Type ty) f = GD $
  do i <- get
     set $! i + 1
     let var   = T.concat ["$exists-", ty, T.pack (show i)]
         param = I.Typed var ty
     let GD b = f (Obj (I.AVar var))
     I.TExists [param] `fmap` b

forAll :: Type sym -> (Obj sym -> GD) -> GD
forAll (Type ty) f = GD $
  do i <- get
     set $! i + 1
     let var   = T.concat ["$forall-", ty, T.pack (show i)]
         param = I.Typed var ty
     let GD b = f (Obj (I.AVar var))
     I.TForall [param] `fmap` b


-- | A fully applied predicate.
newtype Atom = Atom { unAtom :: I.Literal }

notA :: Atom -> Atom
notA (Atom (I.LAtom a)) = Atom (I.LNot  a)
notA (Atom (I.LNot  a)) = Atom (I.LAtom a)

instance IsGD Atom where
  toGD (Atom lit) = GD (return (I.TLit lit))

-- | Add an initial assumption.
assume :: Atom -> Huff step ()
assume (Atom lit) = Huff $
  do RW { .. } <- get
     set RW { rwInit = lit : rwInit, .. }


data Sig (sig :: [Symbol]) = Pred

class IsPred (sig :: [Symbol]) where
  type PredFun sig :: *
  predFun :: T.Text -> [T.Text] -> proxy sig -> PredFun sig
  predArgs :: proxy sig -> [T.Text]

instance IsPred '[] where
  type PredFun '[] = Atom

  predFun n as _ = Atom (I.LAtom (I.Atom n (map I.AName (reverse as))))
  predArgs _ = []

instance (KnownSymbol a, IsPred as) => IsPred (a ': as) where
  type PredFun (a ': as) = Obj a -> PredFun as

  predFun n as sig obj = predFun n (objValue obj : as) (Proxy :: Proxy as)

  predArgs _ = T.pack sym : rest
    where
    sym  = symbolVal (Proxy :: Proxy a)
    rest = predArgs (Proxy :: Proxy as)


newPred :: IsPred sig => T.Text -> Sig sig -> Huff step (PredFun sig)
newPred sym sig = Huff $
  do RW { .. } <- get
     set RW { rwPreds = I.Pred sym (predArgs sig) : rwPreds, .. }
     return (predFun sym [] sig)


-- Effects ---------------------------------------------------------------------

class IsEff eff where
  toEff :: eff -> Eff

toEffect :: IsEff eff => eff -> I.Effect
toEffect eff = unEff (toEff eff)

newtype Eff = Eff { unEff :: I.Effect }

instance IsEff Eff where
  toEff = id

instance IsEff Atom where
  toEff (Atom lit) = Eff (I.ELit lit)

cond :: IsGD cond => cond -> [Atom] -> Eff
cond cond as = Eff (I.EWhen (toTerm cond) (map unAtom as))


-- Actions ---------------------------------------------------------------------

newtype Action step a = Action (StateT (PartialAction step) Id a)
                        deriving (Functor,Applicative,Monad)

data PartialAction step = PartialAction { paPre  :: [I.Term]
                                        , paEff  :: [I.Effect]
                                        , paVal  :: Maybe step
                                        } deriving (Show)

emptyPartialAction :: PartialAction step
emptyPartialAction  = PartialAction { paPre = [], paEff = [], paVal = Nothing }

preCond :: IsGD a => a -> Action step ()
preCond gd = Action $
  do PartialAction { .. } <- get
     set PartialAction { paPre = toTerm gd : paPre, .. }

effect :: IsEff eff => eff -> Action step ()
effect eff = Action $
  do PartialAction { .. } <- get
     set PartialAction { paEff = toEffect eff : paEff, .. }

action :: step -> Action step ()
action s = Action $
  do PartialAction { .. } <- get
     set PartialAction { paVal = Just s, .. }

newAction :: Action step () -> Huff step ()
newAction (Action body) = Huff $
  do RW { .. } <- get
     let (_, PartialAction { .. }) = runM body emptyPartialAction
         op = I.Operator { I.opName    = "op-" `T.append` T.pack (show rwNext)
                         , I.opDerived = False
                         , I.opVal     = paVal
                         , I.opParams  = []
                         , I.opPrecond = I.mkTAnd paPre
                         , I.opEffects = I.mkEAnd paEff
                         }
     set RW { rwOps  = op : rwOps
            , rwNext = rwNext + 1
            , .. }


-- Tests -----------------------------------------------------------------------

test1 =
  do place         <- newType (Proxy :: Proxy "place")
     supermarket   <- newObj "supermarket"    place
     hardwareStore <- newObj "hardware-store" place
     home          <- newObj "home"           place

     good          <- newType (Proxy :: Proxy "good")
     hammer        <- newObj "hammer" good
     drill         <- newObj "drill"  good
     banana        <- newObj "banana" good

     sells <- newPred "sells" (Pred :: Sig '["place", "good"])
     at    <- newPred "at"    (Pred :: Sig '["place"])
     has   <- newPred "has"   (Pred :: Sig '["good"])

     forM_ [supermarket,hardwareStore,home] $ \ a ->
       forM_ [supermarket,hardwareStore,home] $ \ b -> newAction $
         do preCond (at a)
            effect  (notA (at a))
            effect  (at b)
            action $ T.unwords [ "Going from", objValue  a
                               , "to", objValue b ]

     let buy x from = newAction $
           do preCond (at from)
              preCond (sells from x)
              effect (has x)
              action $ T.unwords [ "Buy", objValue x
                                 , "from", objValue from ]

     buy banana supermarket
     mapM_ (`buy` hardwareStore) [hammer,drill]

     assume (at home)
     assume (sells supermarket   banana)
     assume (sells hardwareStore drill)
     goal   (has banana)
     goal   (has drill)
     goal   (at home)

test2 =
  do obj <- newType (Proxy :: Proxy "obj")
     a   <- newObj "a" obj
     b   <- newObj "b" obj
     c   <- newObj "c" obj

     isSet <- newPred "is-set" (Pred :: Sig '["obj"])

     newAction $ do preCond (isSet a)
                    effect  (isSet b)
                    effect  (notA (isSet a))
                    action  "step-1"

     newAction $ do preCond (isSet b)
                    effect  (isSet c)
                    action  "step-2"

     assume (isSet a)
     goal   (isSet c)

test3 =
  do obj   <- newType (Proxy :: Proxy "obj")
     a     <- newObj "a" obj
     b     <- newObj "b" obj
     c     <- newObj "c" obj
     table <- newObj "table" obj

     on    <- newPred "on"    (Pred :: Sig  ["obj", "obj"])
     clear <- newPred "clear" (Pred :: Sig '["obj"])

     -- the stacking actions
     forM_ [a,b,c]         $ \ x ->
       forM_ [a,b,c,table] $ \ y ->
       forM_ [a,b,c,table] $ \ z ->
         when (x /= y && y /= z && z /= x) $
         newAction $
           do preCond (clear x)
              preCond (clear z)
              preCond (on x y)
              effect  (on x z)
              unless (y == table) (effect (clear y))
              unless (z == table) (effect (notA (clear z)))
              action $ T.unwords [ "move", objValue x
                                 , "from", objValue y
                                 , "to",   objValue z ]

     -- setup the initial state
     assume (clear a)
     assume (on a table)
     -- assume (clear b)
     assume (on b table)
     assume (clear c)
     assume (on c b)
     assume (clear table)

     goal (andGD [ on a b, on b c, on c table ])
