{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Huff.Fixpoint (
    buildFixpoint
  ) where

import           Huff.ConnGraph
import qualified Huff.RefSet as RS

import           Control.Monad ( foldM )
import           Data.IORef ( readIORef, writeIORef )
import           Data.Monoid ( mconcat )
import           Data.Struct


-- Predicates ------------------------------------------------------------------

-- | Loop until the goal state is activated in the connection graph.  As the
-- connection graph should only be built from domains that can activate all
-- facts, and delete effects are ignored, this operation will terminate.  The
-- set of effects returned is the set of effects that are immediately applicable
-- to the initial state.
buildFixpoint :: ConnGraph a -> State -> Goals -> IO Int
buildFixpoint gr s0 g =
  do resetConnGraph gr
     loop 0 s0
  where
  loop level facts =
    do effs <- mconcat `fmap` mapM (activateFact gr level) (RS.toList facts)
       done <- allGoalsReached gr g
       if done
          then return level
          else do facts' <- mconcat `fmap` mapM (activateEffect gr level)
                                                (RS.toList effs)
                  if RS.null facts'
                     then return level
                     else loop (level + 1) facts'


-- | All goals have been reached if they are all activated in the connection
-- graph.
allGoalsReached :: ConnGraph a -> Goals -> IO Bool
allGoalsReached cg g = go goals
  where
  goals     = RS.toList g

  -- require that all goals have a level that isn't infinity.
  go (r:rs) = do fact <- getFact cg r
                 l <- getField fLevel fact
                 if l < maxBound
                    then go rs
                    else return False

  go []     =    return True


-- | Set a fact to true at this level of the relaxed graph.  Return any effects
-- that were enabled by adding this fact.
activateFact :: ConnGraph a -> Level -> FactRef -> IO Effects
activateFact cg level ref =
  do fact <- getFact cg ref
     setField fLevel fact level
     preCond <- getField fPreCond fact
     foldM addedPrecond RS.empty (RS.toList preCond)

  where

  addedPrecond effs eff =
    do effect <- getEffect cg eff

       -- skip effects that are already activated
       l <- getField eLevel effect
       if l < maxBound
          then return effs
          else do pcs <- getField eActivePre effect
                  let pcs' = pcs + 1
                  setField eActivePre effect $! pcs'

                  numPre <- getField eNumPre effect
                  if pcs' >= numPre
                     then return (RS.insert eff effs)
                     else return effs

-- | Add an effect at level i, and return all of its add effects.
activateEffect :: ConnGraph a -> Level -> EffectRef -> IO Facts
activateEffect cg level ref =
  do effect <- getEffect cg ref
     setField eLevel effect level
     getField eAdds effect
