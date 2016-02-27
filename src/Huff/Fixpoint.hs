{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Huff.Fixpoint (
    buildFixpoint
  ) where

import           Huff.ConnGraph

import           Data.Foldable (foldlM)
import           Data.IORef ( readIORef, writeIORef )
import           Data.Monoid ( mconcat )
import qualified Data.Set as Set


-- Predicates ------------------------------------------------------------------

-- | Loop until the goal state is activated in the connection graph.  As the
-- connection graph should only be built from domains that can activate all
-- facts, and delete effects are ignored, this operation will terminate.  The
-- set of effects returned is the set of effects that are immediately applicable
-- to the initial state.
buildFixpoint :: ConnGraph a -> State a -> Goals a -> IO Int
buildFixpoint gr s0 g =
  do resetConnGraph gr
     loop 0 s0
  where
  loop level facts =
    do effs <- mconcat `fmap` traverse (activateFact level) (Set.toList facts)
       done <- allGoalsReached g
       if done
          then return level
          else do facts' <- mconcat `fmap` mapM (activateEffect level)
                                                (Set.toList effs)
                  if Set.null facts'
                     then return level
                     else loop (level + 1) facts'


-- | All goals have been reached if they are all activated in the connection
-- graph.
allGoalsReached :: Goals a -> IO Bool
allGoalsReached g = go goals
  where
  goals = Set.toList g

  -- require that all goals have a level that isn't infinity.
  go (fact:rs) =
    do mb <- getLevel fact
       case mb of
         Just{}  -> go rs
         Nothing -> return False

  go [] = return True


-- | Set a fact to true at this level of the relaxed graph.  Return any effects
-- that were enabled by adding this fact.
activateFact :: Level -> Fact a -> IO (Effects a)
activateFact level fact =
  do activate fact level
     foldlM addedPrecond Set.empty (requiresFact fact)

  where

  addedPrecond effs eff =
    do -- skip effects that are already activated
       mb <- getLevel eff
       case mb of

         Just{}  ->
             return effs

         Nothing ->
           do activated <- activatePrecondition eff
              if activated
                 then return (Set.insert eff effs)
                 else return effs


-- | Add an effect at level i, and return all of its add effects.
activateEffect :: Level -> Effect a -> IO (Facts a)
activateEffect level e =
  do activate e level
     return (effectAdds e)
