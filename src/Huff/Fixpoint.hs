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


-- Predicates ------------------------------------------------------------------

-- | Loop until the goal state is activated in the connection graph.  As the
-- connection graph should only be built from domains that can activate all
-- facts, and delete effects are ignored, this operation will terminate.  The
-- set of effects returned is the set of effects that are immediately applicable
-- to the initial state.
buildFixpoint :: ConnGraph -> State -> Goals -> IO Int
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
allGoalsReached :: ConnGraph -> Goals -> IO Bool
allGoalsReached cg g = go goals
  where
  goals     = RS.toList g

  -- require that all goals have a level that isn't infinity.
  go (r:rs) = do Fact { .. } <- getNode cg r
                 l <- readIORef fLevel
                 if l < maxBound
                    then go rs
                    else return False

  go []     =    return True


-- | Set a fact to true at this level of the relaxed graph.  Return any effects
-- that were enabled by adding this fact.
activateFact :: ConnGraph -> Level -> FactRef -> IO Effects
activateFact cg level ref =
  do Fact { .. } <- getNode cg ref
     writeIORef fLevel level

     foldM addedPrecond RS.empty (RS.toList fPreCond)

  where

  addedPrecond effs eff =
    do Effect { .. } <- getNode cg eff

       -- skip effects that are already activated
       l <- readIORef eLevel
       if l < maxBound
          then return effs
          else do pcs <- readIORef eActivePre
                  let pcs' = pcs + 1
                  writeIORef eActivePre $! pcs'

                  if pcs' >= eNumPre
                     then return (RS.insert eff effs)
                     else return effs

-- | Add an effect at level i, and return all of its add effects.
activateEffect :: ConnGraph -> Level -> EffectRef -> IO Facts
activateEffect cg level ref =
  do Effect { .. } <- getNode cg ref
     writeIORef eLevel level
     return eAdds
