{-# LANGUAGE QuasiQuotes #-}

module Huff (
    huff,
    Spec,
    Domain(),
    Problem(),
    Literal(),
    Term(),
    module Huff
  ) where

import           Huff.Compile.AST (Problem,Term(..),Literal(..))
import           Huff.Input (Spec,Domain,Operator(..))
import           Huff.QQ (huff)
import qualified Huff.FF.Planner as FF

import Data.Maybe (mapMaybe)

infixr 3 /\

(/\) :: Term -> Term -> Term
p /\ q = TAnd [p,q]

infixr 4 \/

(\/) :: Term -> Term -> Term
p \/ q = TOr [p,q]

imply :: Term -> Term -> Term
imply  = TImply

class Has_neg a where
  neg :: a -> a

instance Has_neg Literal where
  neg (LAtom a) = LNot  a
  neg (LNot a)  = LAtom a

instance Has_neg Term where
  neg = TNot


findPlan :: Spec a -> IO (Maybe [a])
findPlan (prob,dom) =
  do mb <- FF.findPlan prob dom
     case mb of
       Just xs -> return (Just (mapMaybe opVal (FF.resSteps xs)))
       Nothing -> return Nothing
