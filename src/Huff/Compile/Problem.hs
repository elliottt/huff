{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Huff.Compile.Problem (
    genProblemOperators,
    addNegativePreconditions,
  ) where

import Huff.Compile.AST

import qualified Data.Set as Set


-- | Generate operators from the problem description.  This corresponds to the
-- "Initial Conditions and Goals" section.
genProblemOperators :: Problem -> (Problem, Operator a)
genProblemOperators Problem { .. } = (prob, goalOp)
  where

  goalAtom = LAtom (Atom "$goal-achieved" [])

  prob = Problem { probGoal = TLit goalAtom
                 , ..
                 }

  goalOp = Operator { opName    = "$goal-operator"
                    , opDerived = True
                    , opParams  = []
                    , opPrecond = probGoal
                    , opEffects = ELit goalAtom
                    , opVal     = Nothing
                    }


-- | Modify the initial state to include assumptions about negative
-- preconditions.
addNegativePreconditions :: Set.Set Atom -> Problem -> Problem
addNegativePreconditions negs Problem { .. } =
  Problem { probInit = initNegs negs probInit, .. }


-- | Generate the initial state, given the set of atoms that show up as negative
-- preconditions, and the existing initial state.
initNegs :: Set.Set Atom -> [Literal] -> [Literal]

-- pass non-negative atoms through, that are mentioned in the initial state
initNegs negs (LAtom a : ls)
  | a `Set.member` negs = LAtom a : initNegs (Set.delete a negs) ls
  | otherwise           = LAtom a : initNegs               negs  ls

-- we can safely remove negative initial conditions that aren't used as negative
-- preconditions
initNegs negs (LNot a : ls)
  | a `Set.member` negs = LAtom (negAtom a) : initNegs (Set.delete a negs) ls
  | otherwise           =                     initNegs (Set.delete a negs) ls

-- the remaining set of atoms are depended on as negative preconditions, but
-- unset in the initial state.  their negative variants are set.
initNegs negs [] =
  [ LAtom (negAtom a) | a <- Set.toList negs ]
