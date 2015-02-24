{-# LANGUAGE RecordWildCards #-}
module Huff.Compile (
    compile
  , extractPlan
  , module Huff.Compile.AST
  ) where

import           Huff.Compile.AST
import           Huff.Compile.Operators
import           Huff.Compile.Problem
import qualified Huff.Input as I

import           Data.Maybe (mapMaybe)
import qualified Data.Text as T


compile :: Problem -> Domain a -> (I.Problem,I.Domain (Operator a))
compile prob dom = ( transProblem prob''
                   , transDomain dom { domOperators = ops' } )
  where
  types = typeMap (probObjects prob)

  (prob',goalOp) = genProblemOperators prob

  (prob'',ops') = removeNegation prob' $
    do op        <- goalOp : domOperators dom
       (env,op') <- expandActions types op
       removeDisjunction (removeQuantifiers types env op')


extractPlan :: [I.Operator (Operator a)] -> [a]
extractPlan  = mapMaybe (opVal . I.opVal)


transProblem :: Problem -> I.Problem
transProblem Problem { .. } =
  I.Problem { I.probInit = [ transAtom a | LAtom a <- probInit ]
            , I.probGoal = transPre probGoal
            }

transDomain :: Domain a -> I.Domain (Operator a)
transDomain Domain { .. } =
  I.Domain { I.domOperators = map transOperator domOperators }

transOperator :: Operator a -> I.Operator (Operator a)
transOperator op @ Operator { .. } =
  I.Operator { I.opName    = opName
             , I.opPre     = transPre opPrecond
             , I.opEffects = transEff opEffects
             , I.opVal     = op
             }

transPre :: Term -> [I.Fact]
transPre (TAnd ts)        = concatMap transPre ts
transPre (TLit (LAtom a)) = [transAtom a]
transPre _                = error "transTerm"

transEff :: Effect -> [I.Effect]
transEff eff = simple ++ conditional
  where
  (lits,conds) = splitEffs eff

  simple | null lits = []
         | otherwise = [ foldl addEffect emptyEffect lits ]

  conditional =
    [ foldl addEffect eff' q | (p,q) <- conds
                             , let eff' = emptyEffect { I.ePre = transPre p } ]

  emptyEffect = I.Effect { I.ePre = [], I.eAdd = [], I.eDel = [] }

  addEffect e (LAtom a) = e { I.eAdd = transAtom a : I.eAdd e }
  addEffect e (LNot  a) = e { I.eDel = transAtom a : I.eDel e }

-- | Partition an effect into its simple, and conditional effects.
splitEffs :: Effect -> ([Literal],[(Term,[Literal])])
splitEffs eff = go [] [] (elimEAnd eff)
  where
  go ls cs (EWhen p q : rest) = go    ls ((p,q):cs) rest
  go ls cs (ELit l    : rest) = go (l:ls)       cs  rest
  go ls cs []                 = (ls,cs)
  go _  _  _                  = error "splitEffs"

transAtom :: Atom -> I.Fact
transAtom (Atom a as) = I.Fact a (map transArg as)

transArg :: Arg -> T.Text
transArg (AName n) = n
transArg _         = error "transArg"
