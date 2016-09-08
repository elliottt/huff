{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Huff.Compile.AST where

import           Data.Foldable (foldMap)
import qualified Data.Map.Strict as Map
import           Data.Monoid (Monoid(..))
import qualified Data.Text as T


data Domain a = Domain { domName      :: T.Text
                       , domObjects   :: [Object]
                       , domPreds     :: [Pred]
                       , domOperators :: [Operator a]
                       } deriving (Show)

data Problem = Problem { probInit :: [Literal]
                       , probGoal :: Term
                       } deriving (Show)

data Operator a = Operator { opName    :: !T.Text
                           , opDerived :: !Bool
                           , opParams  :: [Param]
                           , opVal     :: Maybe a
                           , opPrecond :: Term
                           , opEffects :: Effect
                           } deriving (Show,Functor,Foldable,Traversable)

type Name = T.Text

type Type = T.Text

data Typed a = Typed { tValue :: a
                     , tType  :: !Type
                     } deriving (Show,Eq,Ord)

-- | Types and all their inhabitants.
newtype TypeMap a = TypeMap { getTypeMap :: Map.Map Type [a]
                            } deriving (Show)

instance Monoid (TypeMap a) where
  mempty =
    TypeMap mempty

  mappend (TypeMap a) (TypeMap b) =
    TypeMap (Map.unionWith (++) a b)

typeMap :: [Typed a] -> TypeMap a
typeMap  = foldMap (\ Typed { .. } -> TypeMap (Map.singleton tType [tValue]) )

lookupType :: Type -> TypeMap a -> [a]
lookupType k (TypeMap m) = Map.findWithDefault [] k m


type Param  = Typed Name
type Object = Typed Name

data Term = TAnd    [Term]
          | TOr     [Term]
          | TNot    !Term
          | TImply  !Term   !Term
          | TExists [Param] !Term
          | TForall [Param] !Term
          | TLit    !Literal
            deriving (Show)

mkTAnd :: [Term] -> Term
mkTAnd [t] = t
mkTAnd ts  = TAnd ts

mkTOr :: [Term] -> Term
mkTOr [t] = t
mkTOr ts  = TOr ts

data Effect = EForall [Param] Effect
            | EWhen Term [Literal]
            | EAnd [Effect]
            | ELit Literal
              deriving (Show)

mkEWhen :: [Term] -> [Literal] -> Effect
mkEWhen [] = mkELitConj
mkEWhen ps = EWhen (mkTAnd ps)

mkELitConj :: [Literal] -> Effect
mkELitConj xs = EAnd (map ELit xs)

mkEAnd :: [Effect] -> Effect
mkEAnd [e] = e
mkEAnd es  = EAnd es

elimEAnd :: Effect -> [Effect]
elimEAnd (EAnd es) = concatMap elimEAnd es
elimEAnd e         = [e]

isELit :: Effect -> Bool
isELit ELit{} = True
isELit _      = False

data Literal = LAtom Atom
             | LNot  Atom
               deriving (Show)

data App a = App !Name [a]
            deriving (Show,Eq,Ord)

type Atom = App Arg

pattern Atom n as = App n as

negAtom :: Atom -> Atom
negAtom (Atom a as) = Atom (T.append "$not-" a) as

type Pred = App Type

pattern Pred n ts = App n ts

data Arg = AName !Name
         | AVar  !Name
           deriving (Show,Eq,Ord)
