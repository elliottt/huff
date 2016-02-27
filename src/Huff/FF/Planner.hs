{-# LANGUAGE RecordWildCards #-}
module Huff.FF.Planner (
    Plan, Result(..), resSteps,
    findPlan
  ) where

import           Huff.ConnGraph
import           Huff.FF.Extract
                     ( extractPlan, allActions, helpfulActions
                     , addedGoalDeletion )
import           Huff.FF.Fixpoint
import qualified Huff.Input as I

import           Control.Monad ( unless )
import           Data.Foldable (foldl')
import           Data.Function ( on )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable (Hashable(..))
import qualified Data.Heap as Heap
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.List ( sortBy )
import           Data.Maybe ( isJust, fromMaybe, catMaybes )
import           Data.Ord ( comparing )
import qualified Data.Set as Set


type Plan a = Result (I.Operator a)

data Result a = EnforcedHillClimbing [a]
              | GreedyBFS [a]
                deriving (Show)

resSteps :: Result a -> [a]
resSteps (EnforcedHillClimbing as) = as
resSteps (GreedyBFS as)            = as

findPlan :: I.Problem -> I.Domain a -> IO (Maybe (Plan a))
findPlan prob dom =
  do (s0,goal,cg) <- buildConnGraph dom prob
     hash         <- newHash
     mbRoot       <- rootNode cg (mkKey s0) goal
     case mbRoot of
       Nothing   -> return Nothing
       Just root ->
         do mb <- enforcedHillClimbing hash cg root goal
            if isJust mb
               then return $! mkPlan cg EnforcedHillClimbing mb
               else do res <- greedyBestFirst hash cg root goal
                       return $! mkPlan cg GreedyBFS res
  where

  mkPlan cg m (Just effs) = Just (m (map effectOp effs))
  mkPlan _  _ Nothing     = Nothing

  getOper cg eff = return (effectOp eff)


-- Enforced Hill Climbing ------------------------------------------------------

type Steps a = [Effect a]

enforcedHillClimbing :: Hash a -> ConnGraph a -> Node a -> Goals a
                     -> IO (Maybe (Steps a))
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
findBetterState :: Hash a -> ConnGraph a -> Node a -> Goals a
                -> IO (Maybe (Node a))
findBetterState hash cg n goal =
  do let Heuristic { .. } = nodeHeuristic n
     acts  <- helpfulActions hActions hGoals
     succs <- successors True hash cg n goal acts
     case filter (not . deletesGoal) succs of
       n' : _ | nodeMeasure n' < nodeMeasure n -> return (Just n')
       _                                       -> return Nothing


-- Greedy Best-first Search ----------------------------------------------------

greedyBestFirst :: Hash a -> ConnGraph a -> Node a -> Goals a
                -> IO (Maybe (Steps a))
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
        do children <- successors False hash cg n goal (Set.toList (hActions nodeHeuristic))
           go (HS.insert nodeState seen) (foldr Heap.insert rest children)

    Nothing ->
      return Nothing


-- Utilities -------------------------------------------------------------------

-- | Search nodes.
data Node a = Node { nodeState :: Key a
                     -- ^ The state after the effect was applied
                   , nodePathMeasure :: !Int
                     -- ^ The cost of this path
                   , nodeParent :: Maybe (Node a,Effect a)
                     -- ^ The state before this one in the plan, and the effect
                     -- that caused the difference
                   , nodeHeuristic :: !(Heuristic a)
                     -- ^ The actions applied in the first and second layers of
                     -- the relaxed graph for this node.
                   } deriving (Show)

instance Eq (Node a) where
  (==) = (==) `on` nodeState
  {-# INLINE (==) #-}

-- NOTE: changing the implementation of compare for Node will result in
-- different search strategies.  For example, changing it from 'aStarMeasure' to
-- just 'nodeMeasure' will switch from A* to greedy-best-first search.
instance Ord (Node a) where
  compare = compare `on` aStarMeasure
  {-# INLINE compare #-}

rootNode :: ConnGraph a -> Key a -> Goals a -> IO (Maybe (Node a))
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

childNode :: Node a -> Key a -> Effect a -> Heuristic a -> Node a
childNode parent nodeState ref nodeHeuristic =
  Node { nodeParent      = Just (parent,ref)
       , nodePathMeasure = nodePathMeasure parent + 1
       , ..
       }

deletesGoal :: Node a -> Bool
deletesGoal Node { nodeHeuristic = Heuristic { .. } } = hDeletesGoal

aStarMeasure :: Node a -> Int
aStarMeasure n = nodePathMeasure n + nodeMeasure n

-- | The distance that this node is from the goal state.
nodeMeasure :: Node a -> Int
nodeMeasure Node { nodeHeuristic = Heuristic { .. } } = hMeasure

-- | Extract the set of effects applied to get to this state.  This ignores the
-- root node, as it represents the initial state.
extractPath :: Node a -> [Effect a]
extractPath  = go []
  where
  go plan Node { .. } =
    case nodeParent of
      Just (p,op) -> go (op : plan) p
      Nothing     -> plan


-- | Apply effects to the current state, returning the valid choices ordered by
-- their heuristic value.
successors :: Bool -> Hash a -> ConnGraph a -> Node a -> Goals a -> [Effect a]
           -> IO [Node a]
successors checkGD hash cg parent goal refs =
  do mbs <- mapM heuristic refs
     return $! sortBy (comparing nodeMeasure) (catMaybes mbs)

  where

  heuristic nodeOp =
    do let key = mkKey (applyEffect nodeOp (keyState (nodeState parent)))
       mbH <- computeHeuristic checkGD hash cg key goal
       return $ do h <- mbH
                   return (childNode parent key nodeOp h)


data Heuristic a = Heuristic { hMeasure :: !Int
                               -- ^ The heuristic value for this state.
                             , hActions :: Effects a
                               -- ^ All actions from the first layer of the
                               -- relaxed planning graph
                             , hGoals   :: Goals a
                               -- ^ The goals generated by layer 1 of the relaxed
                               -- planning graph
                             , hDeletesGoal :: Bool
                               -- ^ True when this state will cause a goal to be
                               -- deleted (it fails the added goal deletion
                               -- heuristic).  If this check has been disabled,
                               -- this value simply shows up as 'False'.
                             } deriving (Show)

-- | The Heuristic value that suggests no action.
badHeuristic :: Heuristic a
badHeuristic  = Heuristic { hMeasure     = maxBound
                          , hActions     = Set.empty
                          , hGoals       = Set.empty
                          , hDeletesGoal = False
                          }

-- compute the heuristic value for the state that results after applying the
-- given effect, and hash it.
computeHeuristic :: Bool -> Hash a -> ConnGraph a -> Key a -> Goals a
                 -> IO (Maybe (Heuristic a))
computeHeuristic checkGD hash cg key goal =
  do mb <- lookupState hash key
     case mb of
       -- return the cached heuristic
       Just h' ->    return (Just h')

       -- compute and cache the heuristic
       Nothing -> do mbH <- measureState checkGD cg key goal
                     hashState hash key (fromMaybe badHeuristic mbH)
                     return mbH

-- | Compute the size of the relaxed plan produced by the given starting state
-- and goals.
measureState :: Bool -> ConnGraph a -> Key a -> Goals a
             -> IO (Maybe (Heuristic a))
measureState checkGD cg (Key s _) goal =
  do _        <- buildFixpoint cg s goal
     mb       <- extractPlan goal
     hActions <- allActions s

     hDeletesGoal <-
       if checkGD
          then addedGoalDeletion goal
          else return False

     return $! do (hMeasure,gs) <- mb
                  let hGoals = fromMaybe Set.empty (IM.lookup 1 gs)
                  return Heuristic { .. }


-- State Hashing ---------------------------------------------------------------

data Key a = Key (State a) !Int
             deriving (Show)

mkKey :: State a -> Key a
mkKey s = Key s (foldl' hashWithSalt (-2578643520546668380) s)

keyState :: Key a -> State a
keyState (Key s _) = s

instance Eq (Key a) where
  Key s1 h1 == Key s2 h2 = h1 == h2 && s1 == s2

instance Hashable (Key a) where
  hashWithSalt s (Key _ i) = hashWithSalt s i

data Hash a =
  Hash { shHash :: !(IORef (HM.HashMap (Key a) (Heuristic a))) }

newHash :: IO (Hash a)
newHash  =
  do shHash <- newIORef HM.empty
     return Hash { .. }

-- | Add a new entry in the hash for a state.
hashState :: Hash a -> Key a -> Heuristic a -> IO ()
hashState h key val =
  do mb <- lookupState h key
     unless (isJust mb) $
       do states <- readIORef (shHash h)
          writeIORef (shHash h) $! HM.insert key val states

lookupState :: Hash a -> Key a -> IO (Maybe (Heuristic a))
lookupState Hash { .. } key =
  do states <- readIORef shHash
     return $! HM.lookup key states
