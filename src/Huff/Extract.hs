{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}

module Huff.Extract where

import           Huff.ConnGraph
import qualified Huff.RefSet as RS

import           Control.Monad ( foldM, filterM, guard )
import           Data.IORef ( readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.Maybe ( isNothing )
import           Data.Monoid ( mappend )


-- | A map from fact level to the goals that appear there.
type GoalSet = IM.IntMap Goals

-- | Construct the initial goal set for a set of presumed solved goals in the
-- connection graph.  If the goals have not been solved, the level returned will
-- be maxBound.
--
-- NOTE: in fast-forward, when a goal with level INFINITY is encountered, this
-- process returns immediately the value INFINITY, and doesn't complete the goal
-- set.
goalSet :: ConnGraph -> Goals -> IO (Maybe (Level,GoalSet))
goalSet cg goals = go 0 IM.empty (RS.toList goals)
  where
  go !m !gs (g:rest) =
    do Fact { .. } <- getNode cg g
       i <- readIORef fLevel

       if i == maxBound
          then return Nothing
          else do writeIORef fIsGoal True
                  go (max m i) (IM.insertWith mappend i (RS.singleton g) gs) rest

  go !m !gs [] = return (Just (m,gs))


-- | The difficulty heuristic for an effect: the lowest level where one of the
-- effect's preconditions appears.
difficulty :: ConnGraph -> EffectRef -> IO Level
difficulty cg e =
  do Effect { .. } <- getNode cg e
     if RS.null ePre
        then return 0
        else foldM minPrecondLevel maxBound (RS.toList ePre)
  where
  minPrecondLevel l ref =
    do Fact { .. } <- getNode cg ref
       l' <- readIORef fLevel
       return $! min l l'

-- | Extract a plan from a fixed connection graph.
extractPlan :: ConnGraph -> Goals -> IO (Maybe (Int,GoalSet))
extractPlan cg goals0 =
  do mb <- goalSet cg goals0
     case mb of
       Just (m,gs) -> solveGoals 0 m gs
       Nothing     -> return Nothing
  where

  -- solve goals that are added at this fact level.
  solveGoals plan level gs
    | level > 0 =
      do (plan',gs') <-
           case IM.lookup level gs of
             Just goals -> foldM (solveGoal level) (plan,gs) (RS.toList goals)
             Nothing    -> return (plan,gs)

         solveGoals plan' (level - 1) gs'

    | otherwise =
         return (Just (plan,gs))

  solveGoal level acc@(plan,gs) g =
    do Fact { .. } <- getNode cg g

       -- the goal was solved by something else at this level
       isTrue <- readIORef fIsTrue
       if isTrue == level
          then return acc
          else do e             <- pickBest (level - 1) (RS.toList fAdd)
                  Effect { .. } <- getNode cg e
                  writeIORef eInPlan True
                  gs'           <- foldM (filterGoals level) gs (RS.toList ePre)
                  mapM_ (markAdd level) (RS.toList eAdds)
                  let plan' = 1 + plan
                  plan' `seq` return (plan',gs')

  -- insert goals into the goal set for the level where they become true
  filterGoals level gs f =
    do Fact { .. } <- getNode cg f

       isTrue <- readIORef fIsTrue
       isGoal <- readIORef fIsGoal
       l      <- readIORef fLevel

       let existingGoal =
             or [ isTrue == level
                  -- ^ the fact was added by something else at this level
                , isGoal
                  -- ^ the fact is already a goal
                , l == 0
                  -- ^ the fact exists in the initial layer
                ]

       if existingGoal
          then    return gs
          else do writeIORef fIsGoal True
                  return (IM.insertWith mappend l (RS.singleton f) gs)


  -- mark the fact as being added at level i
  markAdd i f =
    do Fact { .. } <- getNode cg f
       writeIORef fIsTrue i


  -- pick the best effect that achieved this goal in the given layer, using the
  -- difficulty heuristic
  pickBest _ []     = fail "extractPlan: invalid connection graph"
  pickBest _ [ref]  = return ref
  pickBest level es = snd `fmap` foldM check (maxBound,error "pickBest") es
    where
    check acc@(d,_) r =
      do Effect { .. } <- getNode cg r
         l <- readIORef eLevel
         if level /= l
            then return acc
            else do d' <- difficulty cg r
                    let acc' | d' < d    = (d',r)
                             | otherwise = acc
                    return $! acc'


-- Helpful Actions -------------------------------------------------------------

-- | All applicable actions from the state.
allActions :: ConnGraph -> State -> IO Effects
allActions cg s = foldM enabledEffects RS.empty (RS.toList s)
  where
  enabledEffects effs ref =
    do Fact { .. } <- getNode cg ref
       foldM checkEffect effs (RS.toList fPreCond)

  checkEffect effs ref =
    do Effect { .. } <- getNode cg ref
       l <- readIORef eLevel
       if l == 0
          then return $! RS.insert ref effs
          else return effs

-- | Helpful actions are those in the first layer of the relaxed plan, that
-- contribute something directly to the next layer.
helpfulActions :: ConnGraph -> Effects -> Goals -> IO [EffectRef]
helpfulActions cg refs goals
  | RS.null goals = return (RS.toList refs)
  | otherwise     = filterM isHelpful (RS.toList refs)
  where
  isHelpful ref =
    do Effect { .. } <- getNode cg ref
       inPlan        <- readIORef eInPlan
       return (inPlan && not (RS.null (RS.intersection goals eAdds)))


-- Added Goal Deletion ---------------------------------------------------------

-- | True when the plan currently represented in the graph deletes a goal along
-- the way.
addedGoalDeletion :: ConnGraph -> Goals -> IO Bool
addedGoalDeletion cg goals = go RS.empty (RS.toList goals)
  where
  go seen (ref : gs) =
    do Fact { .. } <- getNode cg ref
       (seen',mb)  <- foldM checkDels (seen,Just RS.empty) (RS.toList fAdd)
       case mb of
         Just gs' -> go seen' (RS.toList gs' ++ gs)
         Nothing  -> return True

  go _ [] = return False

  checkDels acc@(seen,next) ref

    | isNothing next || ref `RS.member` seen =
         return acc

    | otherwise =
      do Effect { .. } <- getNode cg ref

         inPlan <- readIORef eInPlan

         let next'
               | inPlan =
                 do guard (RS.null (goals `RS.intersection` eDels))
                    facts <- next
                    return (ePre `RS.union` facts)

               | otherwise =
                    next

             seen' = RS.insert ref seen


         next' `seq` return (RS.insert ref seen, next')
