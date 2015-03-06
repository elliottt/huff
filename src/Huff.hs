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

import qualified Huff.Planner as I
import qualified Huff.Compile as I

import           Control.Applicative (Applicative)
import           Control.Monad (forM_)
import qualified Data.Map.Strict as Map
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

runHuff :: Huff step () -> (I.Domain step,I.Problem)
runHuff (Huff m) = (I.Domain { .. }, I.Problem { .. })
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

  probPreds = []

  probInit = rwInit rw

  probGoal = I.mkTAnd (rwGoal rw)



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


-- | A fully applied predicate.
data Atom = Atom I.Literal

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



newtype Action step a = Action (StateT (PartialAction step) Id a)
                        deriving (Functor,Applicative,Monad)

data PartialAction step = PartialAction { paPre  :: [I.Term]
                                        , paEff  :: [I.Effect]
                                        , paVal  :: Maybe step
                                        } deriving (Show)

emptyPartialAction :: PartialAction step
emptyPartialAction  = PartialAction { paPre = [], paEff = [], paVal = Nothing }

preCond :: Atom -> Action step ()
preCond (Atom a) = Action $
  do PartialAction { .. } <- get
     set PartialAction { paPre = I.TLit a : paPre, .. }

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
  do vehicle <- newType (Proxy :: Proxy "vehicle")
     car     <- newObj "car"  vehicle
     bike    <- newObj "bike" vehicle

     person  <- newType (Proxy :: Proxy "person")
     me      <- newObj "me"  person
     you     <- newObj "you" person

     uses    <- newPred "uses" (Pred :: Sig ["person", "vehicle"])

     forM_ [car,bike] $ \ v ->
       forM_ [me,you] $ \ p -> newAction $
         do preCond (uses p v)
