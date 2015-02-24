{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Huff.Input where

import qualified Data.Set as Set
import           Data.String ( IsString(..) )
import qualified Data.Text as T


data Problem = Problem { probInit :: [Fact]
                       , probGoal :: [Fact]
                       } deriving (Show)

-- | A collection of named operators.
newtype Domain a = Domain { domOperators :: [Operator a]
                          } deriving (Show)

-- | Operators, consisting of preconditions and effects.
data Operator a = Operator { opName    :: !T.Text
                           , opPre     :: [Fact]
                           , opEffects :: [Effect]
                           , opVal     :: a
                           } deriving (Show)

-- | Effects, optionally guarded by additional conditions.
data Effect = Effect { ePre :: [Fact]
                     , eAdd :: [Fact]
                     , eDel :: [Fact]
                     } deriving (Show,Eq,Ord)

-- | A fact is a predicate, applied to zero or more constants.
data Fact = Fact !T.Text [T.Text]
            deriving (Show,Eq,Ord)

instance IsString Fact where
  fromString str = Fact (fromString str) []


-- Utilities -------------------------------------------------------------------

probFacts :: Problem -> Set.Set Fact
probFacts Problem { .. } = Set.fromList (probInit ++ probGoal)

domFacts :: Domain a -> Set.Set Fact
domFacts Domain { .. } = Set.unions (map opFacts domOperators)

opFacts :: Operator a -> Set.Set Fact
opFacts Operator { .. } =
  Set.unions (Set.fromList opPre : map effFacts opEffects)

effFacts :: Effect -> Set.Set Fact
effFacts Effect { .. } = Set.fromList (ePre ++ eAdd ++ eDel)


-- | Emit effects that have the operator's precondition guarding their effects.
expandEffects :: Operator a -> [Effect]
expandEffects Operator { .. } = map addPrecond opEffects
  where
  addPrecond Effect { .. } = Effect { ePre = opPre ++ ePre, .. }
