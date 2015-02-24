{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Huff.Compile.Problem where

import Huff.Compile.AST


-- | Generate operators from the problem description.  This corresponds to the
-- "Initial Conditions and Goals" section.
genProblemOperators :: Problem -> (Problem, Operator)
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
                    }
