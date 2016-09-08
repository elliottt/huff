{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Huff.Compile (
    compileOperators,
    compileProblem,
    extractPlan,
    module Huff.Compile.AST,
  ) where

import           Huff.Compile.AST
import           Huff.Compile.Operators
import           Huff.Compile.Problem
import qualified Huff.Input as I

import           Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T


-- | Compile operators, but leave off the negation removal step, which must be
-- done in the presence of the problem. The benefit to doing things this way, is
-- that this step can be done at compile time with template-haskell, and the
-- less-complicated negation removal step can be done at runtime, once the
-- problem is known.
compileOperators :: ([Name] -> a -> b) -> TypeMap Name -> [Operator a] -> [Operator b]
compileOperators adjust types ops =
  do op             <- ops
     (env,args,op') <- expandActions types op
     let op'' = op' { opVal = adjust args `fmap` opVal op' }
     removeDisjunction (removeQuantifiers types env op'')


-- | Compile a problem, in the context of the domain.
compileProblem :: TypeMap Name -> [Operator a] -> Problem -> (I.Problem,I.Domain a)
compileProblem types ops prob = (transProblem prob'', I.Domain (map transOperator ops'))
  where
  (prob',goalOp) = genProblemOperators prob
  (negs,ops')    = removeNegation (compileOperators adjust types [goalOp] ++ ops)
  prob''         = addNegativePreconditions negs prob'

  adjust _ _ = undefined


extractPlan :: [I.Operator a] -> [a]
extractPlan  = mapMaybe I.opVal

transProblem :: Problem -> I.Problem
transProblem Problem { .. } =
  I.Problem { I.probInit = [ transAtom a | LAtom a <- probInit ]
            , I.probGoal = transPre probGoal
            }

transDomain :: Domain a -> I.Domain a
transDomain Domain { .. } =
  I.Domain { I.domOperators = map transOperator domOperators }

transOperator :: Operator a -> I.Operator a
transOperator op @ Operator { .. } =
  I.Operator { I.opName    = opName
             , I.opPre     = transPre opPrecond
             , I.opEffects = transEff opEffects
             , I.opVal     = opVal
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
