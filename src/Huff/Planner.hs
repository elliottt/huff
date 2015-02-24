{-# LANGUAGE RecordWildCards #-}
module Huff.Planner where

import           Huff.ConnGraph
import           Huff.Extract ( extractPlan, allActions, helpfulActions
                              , addedGoalDeletion )
import           Huff.Fixpoint
import qualified Huff.Input as I
import qualified Huff.RefSet as RS

import           Control.Monad ( unless )
import           Data.Function ( on )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.Heap as Heap
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.List ( sortBy )
import           Data.Maybe ( isJust, fromMaybe, catMaybes )
import           Data.Ord ( comparing )
import qualified Data.Text as T


type Plan a = [T.Text]

data Result a = EnforcedHillClimbing (Plan a)
              | GreedyBFS (Plan a)
                deriving (Show)

findPlan :: I.Problem -> I.Domain a -> IO (Maybe (Result a))
findPlan prob dom =
  do (s0,goal,cg) <- buildConnGraph dom prob
     hash         <- newHash
     mbRoot       <- rootNode cg s0 goal
     case mbRoot of
       Nothing   -> return Nothing
       Just root ->
         do mb <- enforcedHillClimbing hash cg root goal
            if isJust mb
               then mkPlan cg EnforcedHillClimbing mb
               else do res <- greedyBestFirst hash cg root goal
                       mkPlan cg GreedyBFS res
  where

  mkPlan cg m (Just effs) = (Just . m) `fmap` mapM (getOper cg) effs
  mkPlan _  _ Nothing     = return Nothing

  getOper cg eref =
    do Effect { .. } <- getNode cg eref
       Oper { .. }   <- getNode cg eOp
       return oName


-- Enforced Hill Climbing ------------------------------------------------------

type Steps = [EffectRef]

enforcedHillClimbing :: Hash -> ConnGraph -> Node -> Goals -> IO (Maybe Steps)
enforcedHillClimbing hash cg root goal =
  loop root

  where

  loop n =
    do mb <- findBetterState hash cg n goal
       case mb of

         Just n'
           | nodeMeasure n' == 0 -> return (Just (extractPath n'))
           | otherwise           -> loop n'

         Nothing -> return Nothing

-- | Find a state whose heuristic value is strictly smaller than the current
-- state.
findBetterState :: Hash -> ConnGraph -> Node -> Goals -> IO (Maybe Node)
findBetterState hash cg n goal =
  do let Heuristic { .. } = nodeHeuristic n
     acts  <- helpfulActions cg hActions hGoals
     succs <- successors True hash cg n goal acts
     case filter (not . deletesGoal) succs of
       n' : _ | nodeMeasure n' < nodeMeasure n -> return (Just n')
       _                                       -> return Nothing


-- Greedy Best-first Search ----------------------------------------------------

greedyBestFirst :: Hash -> ConnGraph -> Node -> Goals -> IO (Maybe Steps)
greedyBestFirst hash cg root goal =
  go HS.empty $ Heap.singleton root
      { nodeHeuristic = (nodeHeuristic root) { hMeasure = maxBound }}

  where

  go seen queue = case Heap.uncons queue of

    Just (n @ Node { .. }, rest)
      | nodeMeasure n == 0 ->
           return (Just (extractPath n))

        -- don't generate children for nodes that have already been visited
      | nodeState `HS.member` seen ->
           go seen rest

      | otherwise ->
        do children <- successors False hash cg n goal (RS.toList (hActions nodeHeuristic))
           go (HS.insert nodeState seen) (foldr Heap.insert rest children)

    Nothing ->
      return Nothing


-- Utilities -------------------------------------------------------------------

-- | Search nodes.
data Node = Node { nodeState :: State
                   -- ^ The state after the effect was applied
                 , nodePathMeasure :: !Int
                   -- ^ The cost of this path
                 , nodeParent :: Maybe (Node,EffectRef)
                   -- ^ The state before this one in the plan, and the effect
                   -- that caused the difference
                 , nodeHeuristic :: !Heuristic
                   -- ^ The actions applied in the first and second layers of
                   -- the relaxed graph for this node.
                 } deriving (Show)

instance Eq Node where
  (==) = (==) `on` nodeState
  {-# INLINE (==) #-}

-- NOTE: changing the implementation of compare for Node will result in
-- different search strategies.  For example, changing it from 'aStarMeasure' to
-- just 'nodeMeasure' will switch from A* to greedy-best-first search.
instance Ord Node where
  compare = compare `on` aStarMeasure
  {-# INLINE compare #-}

rootNode :: ConnGraph -> State -> Goals -> IO (Maybe Node)
rootNode cg nodeState goal =
  do mbH <- measureState False cg nodeState goal
     case mbH of
       Just nodeHeuristic ->
            return $ Just Node { nodeParent      = Nothing
                               , nodePathMeasure = 0
                               , ..
                               }

       Nothing ->
            return Nothing

childNode :: Node -> State -> EffectRef -> Heuristic -> Node
childNode parent nodeState ref nodeHeuristic =
  Node { nodeParent      = Just (parent,ref)
       , nodePathMeasure = nodePathMeasure parent + 1
       , ..
       }

deletesGoal :: Node -> Bool
deletesGoal Node { nodeHeuristic = Heuristic { .. } } = hDeletesGoal

aStarMeasure :: Node -> Int
aStarMeasure n = nodePathMeasure n + nodeMeasure n

-- | The distance that this node is from the goal state.
nodeMeasure :: Node -> Int
nodeMeasure Node { nodeHeuristic = Heuristic { .. } } = hMeasure

-- | Extract the set of effects applied to get to this state.  This ignores the
-- root node, as it represents the initial state.
extractPath :: Node -> [EffectRef]
extractPath  = go []
  where
  go plan Node { .. } =
    case nodeParent of
      Just (p,op) -> go (op : plan) p
      Nothing     -> plan


-- | Apply effects to the current state, returning the valid choices ordered by
-- their heuristic value.
successors :: Bool -> Hash -> ConnGraph -> Node -> Goals -> [EffectRef]
           -> IO [Node]
successors checkGD hash cg parent goal refs =
  do mbs <- mapM heuristic refs
     return $! sortBy (comparing nodeMeasure) (catMaybes mbs)

  where

  heuristic nodeOp =
    do nodeState <- applyEffect cg nodeOp (nodeState parent)
       mbH       <- computeHeuristic checkGD hash cg nodeState goal
       return $ do h <- mbH
                   return (childNode parent nodeState nodeOp h)


data Heuristic = Heuristic { hMeasure :: !Int
                             -- ^ The heuristic value for this state.
                           , hActions :: Effects
                             -- ^ All actions from the first layer of the
                             -- relaxed planning graph
                           , hGoals   :: Goals
                             -- ^ The goals generated by layer 1 of the relaxed
                             -- planning graph
                           , hDeletesGoal :: Bool
                             -- ^ True when this state will cause a goal to be
                             -- deleted (it fails the added goal deletion
                             -- heuristic).  If this check has been disabled,
                             -- this value simply shows up as 'False'.
                           } deriving (Show)

-- | The Heuristic value that suggests no action.
badHeuristic :: Heuristic
badHeuristic  = Heuristic { hMeasure     = maxBound
                          , hActions     = RS.empty
                          , hGoals       = RS.empty
                          , hDeletesGoal = False
                          }

-- compute the heuristic value for the state that results after applying the
-- given effect, and hash it.
computeHeuristic :: Bool -> Hash -> ConnGraph -> State -> Goals
                 -> IO (Maybe Heuristic)
computeHeuristic checkGD hash cg s goal =
  do mb <- lookupState hash s
     case mb of
       -- return the cached heuristic
       Just h' ->    return (Just h')

       -- compute and cache the heuristic
       Nothing -> do mbH <- measureState checkGD cg s goal
                     hashState hash s (fromMaybe badHeuristic mbH)
                     return mbH

-- | Compute the size of the relaxed plan produced by the given starting state
-- and goals.
measureState :: Bool -> ConnGraph -> State -> Goals -> IO (Maybe Heuristic)
measureState checkGD cg s goal =
  do _        <- buildFixpoint cg s goal
     mb       <- extractPlan cg goal
     hActions <- allActions cg s

     hDeletesGoal <-
       if checkGD
          then addedGoalDeletion cg goal
          else return False

     return $! do (hMeasure,gs) <- mb
                  let hGoals = fromMaybe RS.empty (IM.lookup 1 gs)
                  return Heuristic { .. }


-- State Hashing ---------------------------------------------------------------

data Hash = Hash { shHash :: !(IORef (HM.HashMap State Heuristic))
                 }

newHash :: IO Hash
newHash  =
  do shHash <- newIORef HM.empty
     return Hash { .. }

-- | Add a new entry in the hash for a state.
hashState :: Hash -> State -> Heuristic -> IO ()
hashState h s val =
  do mb <- lookupState h s
     unless (isJust mb) $
       do states <- readIORef (shHash h)
          writeIORef (shHash h) $! HM.insert s val states

lookupState :: Hash -> State -> IO (Maybe Heuristic)
lookupState Hash { .. } s =
  do states <- readIORef shHash
     return $! HM.lookup s states
