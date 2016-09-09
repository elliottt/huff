{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}

module Huff.FF.Extract where

import           Huff.ConnGraph

import           Control.Monad ( foldM, filterM, guard )
import           Data.IORef ( readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.Maybe ( isNothing )
import           Data.Monoid ( mappend )
import qualified Data.Set as Set


-- | A map from fact level to the goals that appear there.
type GoalSet a = IM.IntMap (Goals a)

-- | Construct the initial goal set for a set of presumed solved goals in the
-- connection graph.  If the goals have not been solved, the level returned will
-- be Nothing.
--
-- NOTE: in fast-forward, when a goal with level INFINITY is encountered, this
-- process returns immediately the value INFINITY, and doesn't complete the goal
-- set.
goalSet :: Goals a -> IO (Maybe (Level,GoalSet a))
goalSet goals = go 0 IM.empty (Set.toList goals)
  where
  go !m !gs (fact:fs) =
    do mb <- getLevel fact
       case mb of

         Nothing ->
              return Nothing

         Just i  ->
           do markGoal fact
              go (max m i) (IM.insertWith mappend i (Set.singleton fact) gs) fs

  go !m !gs [] = return (Just (m,gs))


-- | The difficulty heuristic for an effect: the lowest level where one of the
-- effect's preconditions appears.
difficulty :: Effect a -> IO Level
difficulty eff = foldM minPrecondLevel maxBound (Set.toList (effectPre eff))
  where
  minPrecondLevel l fact =
    do mb <- getLevel fact
       case mb of
         Just l' -> return $! min l l'
         Nothing -> return l

-- | Extract a plan from a fixed connection graph.
extractPlan :: Goals a -> IO (Maybe (Int,GoalSet a))
extractPlan goals0 =
  do mb <- goalSet goals0
     case mb of
       Just (m,gs) -> solveGoals 0 m gs
       Nothing     -> return Nothing
  where

  -- solve goals that are added at this fact level.
  solveGoals plan level gs
    | level > 0 =
      do (plan',gs') <-
           case IM.lookup level gs of
             Just goals -> foldM (solveGoal level) (plan,gs) (Set.toList goals)
             Nothing    -> return (plan,gs)

         solveGoals plan' (level - 1) gs'

    | otherwise =
         return (Just (plan,gs))

  solveGoal level acc@(plan,gs) f =
    do -- the goal was solved by something else at this level
       mb <- isTrue f
       case mb of
         Just trueLevel | trueLevel == level ->
              return acc

         _ ->
           do eff <- pickBest (level - 1) (Set.toList (addsFact f))
              markInPlan eff
              gs' <- foldM (filterGoals level) gs (Set.toList (effectPre eff))
              mapM_ (markAdd level) (Set.toList (effectAdds eff))
              let plan' = 1 + plan
              plan' `seq` return (plan',gs')

  -- insert goals into the goal set for the level where they become true
  filterGoals level gs fact =
    do true   <- isTrue   fact
       goal   <- isGoal   fact
       Just l <- getLevel fact

       let existingGoal =
             or [ maybe False (== level) true
                  -- the fact was added by something else at this level

                , goal
                  -- the fact is already a goal

                , l == 0
                  -- the fact exists in the initial layer
                ]

       if existingGoal
          then    return gs
          else do markGoal fact
                  return (IM.insertWith mappend l (Set.singleton fact) gs)


  -- mark the fact as being added at level i
  markAdd i fact = markTrue fact i


  -- pick the best effect that achieved this goal in the given layer, using the
  -- difficulty heuristic
  pickBest _ []     = fail "extractPlan: invalid connection graph"
  pickBest _ [e]    = return e
  pickBest level es = snd `fmap` foldM check (maxBound,error "pickBest") es
    where
    check acc@(d,_) eff =
      do mb <- getLevel eff
         case mb of

           Just l | l == level ->
             do d' <- difficulty eff
                let acc' | d' < d    = (d',eff)
                         | otherwise = acc
                return $! acc'

           _ -> return acc


-- Helpful Actions -------------------------------------------------------------

-- | All applicable actions from the state.
allActions :: State a -> IO (Effects a)
allActions s = foldM enabledEffects Set.empty (Set.toList s)
  where
  enabledEffects effs fact =
       foldM checkEffect effs (Set.toList (requiresFact fact))

  checkEffect effs eff =
    do mb <- getLevel eff
       case mb of
         Just 0 -> return $! Set.insert eff effs
         _      -> return effs

-- | Helpful actions are those in the first layer of the relaxed plan, that
-- contribute something directly to the next layer.
helpfulActions :: Effects a -> Goals a -> IO [Effect a]
helpfulActions effs goals
  | Set.null goals = return (Set.toList effs)
  | otherwise      = filterM isHelpful (Set.toList effs)
  where
  isHelpful eff =
    do inPlan <- isInPlan eff
       return (inPlan && not (Set.null (Set.intersection goals (effectAdds eff))))


-- Added Goal Deletion ---------------------------------------------------------

-- | True when the plan currently represented in the graph deletes a goal along
-- the way.
addedGoalDeletion :: Goals a -> IO Bool
addedGoalDeletion goals = go Set.empty (Set.toList goals)
  where
  go seen (fact : gs) =
    do (seen',mb) <- foldM checkDels (seen,Just Set.empty)
                                     (Set.toList (addsFact fact))
       case mb of
         Just gs' -> go seen' (Set.toList gs' ++ gs)
         Nothing  -> return True

  go _ [] = return False

  checkDels acc@(seen,next) eff

    | isNothing next || eff `Set.member` seen =
         return acc

    | otherwise =
      do inPlan <- isInPlan eff

         let next'
               | inPlan =
                 do guard (Set.null (goals `Set.intersection` effectDels eff))
                    facts <- next
                    return (effectPre eff `Set.union` facts)

               | otherwise =
                    next


         next' `seq` return (Set.insert eff seen, next')
