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
import qualified Huff.Input   as Input
import qualified Huff.Planner as I

import           Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import           Data.Maybe (mapMaybe)
import           Data.Proxy (Proxy(..))
import qualified Data.Set as Set
import qualified Data.Text as T
import           GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import           MonadLib (StateT,get,set,runM,Id)


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


newtype Obj (ty :: Symbol) = Obj T.Text
                             deriving (Show,Eq)

newObj :: T.Text -> Type sym -> Huff step (Obj ty)
newObj str (Type ty) = Huff $
  do RW { .. } <- get
     set RW { rwTypes = Map.alter add ty rwTypes, .. }
     return (Obj str)
  where
  add (Just objs) = Just (Set.insert str objs)
  add Nothing     = Just (Set.singleton str)

objValue :: Obj ty -> T.Text
objValue (Obj str) = str


-- Goal Descriptions -----------------------------------------------------------

class IsGD a where
  toGD :: a -> GD

toTerm :: IsGD a => a -> I.Term
toTerm a = unGD (toGD a)

newtype GD = GD { unGD :: I.Term }

instance IsGD GD where
  toGD = id

goal :: IsGD a => a -> Huff step ()
goal gd = Huff $
  do RW { .. } <- get
     set RW { rwGoal = toTerm gd : rwGoal, .. }

orGD :: IsGD a => [a] -> GD
orGD gds = GD (I.mkTOr (map toTerm gds))

andGD :: IsGD a => [a] -> GD
andGD gds = GD (I.mkTAnd (map toTerm gds))

notGD :: IsGD a => a -> GD
notGD gd = GD (I.TNot (toTerm gd))

(==>) :: (IsGD a, IsGD b) => a -> b -> GD
a ==> b = GD (I.TImply (toTerm a) (toTerm b))


-- | A fully applied predicate.
newtype Atom = Atom { unAtom :: I.Literal }

negA :: Atom -> Atom
negA (Atom (I.LAtom a)) = Atom (I.LNot  a)
negA (Atom (I.LNot  a)) = Atom (I.LAtom a)

instance IsGD Atom where
  toGD (Atom lit) = GD (I.TLit lit)

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

test =
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
            effect  (negA (at a))
            effect  (at b)
            action  $ ("Going from `" ++ show a ++ "` to `" ++ show b ++ "`")

     let buy x from = newAction $
           do preCond (at from)
              preCond (sells from x)
              effect (has x)
              action $ "Buy `" ++ show x ++ "` from " ++ show from

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
                    effect  (negA (isSet a))
                    action  "step-1"

     newAction $ do preCond (isSet b)
                    effect  (isSet c)
                    action  "step-2"

     assume (isSet a)
     goal   (isSet c)
