{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Huff where

import qualified Huff.Planner as I
import qualified Huff.Compile as I

import           Control.Applicative (Applicative)
import qualified Data.Map.Strict as Map
import           Data.Proxy (Proxy(..))
import qualified Data.Set as Set
import qualified Data.Text as T
import           GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import           MonadLib (StateT,get,set,runM,Id)


newtype Huff step a = Huff { unHuff :: StateT (RW step) Id a
                           } deriving (Functor,Applicative,Monad)

data RW step = RW { rwOps :: [I.Operator step]
                    -- ^ Fully instantiated operators
                  , rwPreds :: [I.Pred]
                    -- ^ Defined predicates
                  , rwTypes :: Map.Map T.Text (Set.Set T.Text)
                    -- ^ Types, with their inhabitants
                  }


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


data Pred (args :: [Symbol]) = Pred T.Text

-- | A fully applied predicate.
data Atom = Atom I.Atom

class IsPred (args :: [Symbol]) where
  predArgs :: proxy args -> [T.Text]

  type PredSig args :: *

instance IsPred '[] where
  predArgs _ = []

  type PredSig '[] = Atom

instance (KnownSymbol a, IsPred as) => IsPred (a ': as) where
  predArgs _ = T.pack sym : rest
    where
    sym  = symbolVal (Proxy :: Proxy a)
    rest = predArgs (Proxy :: Proxy as)

  type PredSig (a ': as) = Obj a -> PredSig as

newPred :: IsPred args => T.Text -> Huff step (Pred args)
newPred sym = Huff $
  do let p = Pred sym
     RW { .. } <- get
     set RW { rwPreds = I.Pred sym (predArgs p) : rwPreds, .. }
     return p


data Action (args :: [Symbol]) step

class MakeAction (args :: [Symbol]) where
  type ActionBody args step :: *

instance MakeAction '[] where
  type ActionBody '[] step = Huff step ()

instance MakeAction args => MakeAction (a ': args) where
  type ActionBody (a ': args) step = Obj a -> ActionBody args step


newAction :: MakeAction args => ActionBody args step -> Huff step ()
newAction body = undefined
