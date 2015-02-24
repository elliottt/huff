{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Huff.RefSet where

import           Data.Hashable ( Hashable(..) )
import qualified Data.IntSet as IS
import           Data.Monoid ( Monoid )


-- Reference Sets --------------------------------------------------------------

newtype RefSet a = RefSet IS.IntSet
                   deriving (Show,Eq,Monoid)

instance Hashable (RefSet a) where
  hashWithSalt z (RefSet is) = IS.foldl' hashWithSalt z is


class Ref a where
  toRef   :: Int -> a
  fromRef :: a -> Int

toList :: Ref a => RefSet a -> [a]
toList (RefSet is) = [ toRef r | r <- IS.toList is ]

fromList :: Ref a => [a] -> RefSet a
fromList rs = RefSet (IS.fromList (map fromRef rs))

null :: RefSet a -> Bool
null (RefSet rs) = IS.null rs

empty :: RefSet a
empty  = RefSet IS.empty

singleton :: Ref a => a -> RefSet a
singleton a = RefSet (IS.singleton (fromRef a))

insert :: Ref a => a -> RefSet a -> RefSet a
insert a (RefSet rs) = RefSet (IS.insert (fromRef a) rs)

member :: Ref a => a -> RefSet a -> Bool
member a (RefSet rs) = IS.member (fromRef a) rs

intersection :: RefSet a -> RefSet a -> RefSet a
intersection (RefSet a) (RefSet b) = RefSet (IS.intersection a b)

union :: RefSet a -> RefSet a -> RefSet a
union (RefSet a) (RefSet b) = RefSet (a `IS.union` b)

(\\) :: RefSet a -> RefSet a -> RefSet a
RefSet a \\ RefSet del = RefSet (a IS.\\ del)

isSubsetOf :: RefSet a -> RefSet a -> Bool
isSubsetOf (RefSet a) (RefSet b) = IS.isSubsetOf a b

minView :: Ref a => RefSet a -> Maybe (a,RefSet a)
minView (RefSet rs) =
  do (a,rs') <- IS.minView rs
     return (toRef a,RefSet rs')

foldl' :: Ref a => (b -> a -> b) -> b -> RefSet a -> b
foldl' f z (RefSet rs) = IS.foldl' f' z rs
  where
  f' b a = f b (toRef a)
