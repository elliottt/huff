{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

module Huff.ConnGraph (
    -- * Connection Graph
    ConnGraph()
  , resetConnGraph
  , buildConnGraph
  , IsNode(..)

    -- ** Facts
  , Fact()
  , markTrue, isTrue
  , markGoal, isGoal
  , requiresFact
  , addsFact
  , delsFact

    -- ** Effects
  , Effect()
  , isInPlan, markInPlan
  , activatePrecondition
  , effectAdds
  , effectDels
  , effectPre
  , effectOp

  , Level

  , State, applyEffect
  , Goals
  , Facts
  , Effects

    -- * Debugging
  , printConnGraph
  , printEffects, printEffect
  , printFacts, printFact
  ) where

import qualified Huff.Input as I

import           Control.Monad (zipWithM,foldM,unless)
import           Data.Function (on)
import           Data.Hashable (Hashable(..))
import           Data.IORef
                     (IORef,newIORef,readIORef,writeIORef,atomicModifyIORef')
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T


-- Connection Graph ------------------------------------------------------------

type Facts   a = Set.Set (Fact a)
type Goals   a = Set.Set (Fact a)
type State   a = Set.Set (Fact a)
type Effects a = Set.Set (Effect a)

type Level = Int

data ConnGraph a = ConnGraph { cgFacts        :: !(Facts a)
                             , cgEffects      :: !(Effects a)
                             , cgDirtyFacts   :: !(IORef [Fact a])
                             , cgDirtyEffects :: !(IORef [Effect a])
                             }


data Fact a = Fact { fId    :: !Int
                   , fProp  :: !I.Fact
                   , fLevel :: !(IORef (Maybe Level))

                   , fIsTrue:: !(IORef (Maybe Level))
                   , fIsGoal:: !(IORef Bool)

                   , fDirty     :: !(IORef Bool)
                   , fDirtyList :: !(IORef [Fact a])

                   , fPreCond :: Effects a
                     -- ^ Effects that require this fact
                   , fAdd   :: Effects a
                     -- ^ Effects that add this fact
                   , fDel   :: Effects a
                     -- ^ Effects that delete this fact
                   }

instance Show (Fact a) where
  showsPrec p Fact { .. } = showParen (p >= 10)
    $ showString "Fact "
    . shows fId
    . showString " "
    . showParen True (shows fProp)

instance Hashable (Fact a) where
  hashWithSalt s Fact { .. } = hashWithSalt s fId

markTrue :: Fact a -> Level -> IO ()
markTrue f l =
  do dirty f
     writeIORef (fIsTrue f) (Just l)

isTrue :: Fact a -> IO (Maybe Level)
isTrue Fact { .. } = readIORef fIsTrue


markGoal :: Fact a -> IO ()
markGoal f =
  do dirty f
     writeIORef (fIsGoal f) True

isGoal :: Fact a -> IO Bool
isGoal Fact { .. } = readIORef fIsGoal


instance Eq (Fact a) where
  (==) = (==) `on` fId
  (/=) = (/=) `on` fId
  {-# INLINE (==) #-}
  {-# INLINE (/=) #-}

instance Ord (Fact a) where
  compare = compare `on` fId
  {-# INLINE compare #-}

data Effect a = Effect { eId        :: !Int
                       , ePre       :: Facts a
                       , eNumPre    :: !Int
                       , eAdds      :: Facts a
                       , eDels      :: Facts a
                       , eOp        :: !(I.Operator a)
                         -- ^ The operator that this effect came from

                       , eDirty     :: !(IORef Bool)
                       , eDirtyList :: !(IORef [Effect a])

                       , eInPlan    :: !(IORef Bool)
                         -- ^ Whether or not this effect is a member of the
                         -- current relaxed plan

                       , eIsInH     :: !(IORef Bool)
                         -- ^ If this action is part of the helpful action set

                       , eLevel     :: !(IORef (Maybe Level))
                         -- ^ Membership level for this effect
                       , eActivePre :: !(IORef Level)
                         -- ^ Active preconditions for this effect
                       }

instance Show (Effect a) where
  showsPrec p Effect { .. } = showParen (p >= 10)
    $ showString "Effect: "
    . showParen True (shows eId)


markInPlan :: Effect a -> IO ()
markInPlan e =
  do dirty e
     writeIORef (eInPlan e) True

isInPlan :: Effect a -> IO Bool
isInPlan Effect { .. } = readIORef eInPlan

effectOp :: Effect a -> I.Operator a
effectOp Effect { .. } = eOp


instance Eq (Effect a) where
  (==) = (==) `on` eId
  (/=) = (/=) `on` eId
  {-# INLINE (==) #-}
  {-# INLINE (/=) #-}

instance Ord (Effect a) where
  compare = compare `on` eId
  {-# INLINE compare #-}


-- Node Operations -------------------------------------------------------------

class IsNode node where
  dirty    :: node a -> IO ()
  activate :: node a -> Level -> IO ()
  getLevel :: node a -> IO (Maybe Level)

instance IsNode Fact where
  dirty f =
    do isDirty <- readIORef (fDirty f)
       unless isDirty (atomicModifyIORef' (fDirtyList f) (\fs -> (f:fs, ())))

  activate f l =
    do dirty f
       writeIORef (fLevel f) (Just l)

  getLevel Fact { .. } = readIORef fLevel

instance IsNode Effect where
  dirty e =
    do isDirty <- readIORef (eDirty e)
       unless isDirty (atomicModifyIORef' (eDirtyList e) (\xs -> (e:xs, ())))

  activate e l =
    do dirty e
       writeIORef (eLevel e) (Just l)

  getLevel Effect { .. } = readIORef eLevel


-- | The effects that have this fact as a precondition.
requiresFact :: Fact a -> Effects a
requiresFact Fact { .. } = fPreCond

-- | The effects that add this fact to the state.
addsFact :: Fact a -> Effects a
addsFact Fact { .. } = fAdd

-- | The effects that delete this fact from the state.
delsFact :: Fact a -> Effects a
delsFact Fact { .. } = fDel

-- | Increment the number of activated preconditions, and return a boolean that
-- indicates whether or not the effect has been activated.
activatePrecondition :: Effect a -> IO Bool
activatePrecondition eff =
  do dirty eff
     atomicModifyIORef' (eActivePre eff) $ \ n ->
       let n' = n + 1
        in (n', n' >= eNumPre eff)

effectAdds :: Effect a -> Facts a
effectAdds Effect { .. } = eAdds
{-# INLINE effectAdds #-}

effectDels :: Effect a -> Facts a
effectDels Effect { .. } = eDels
{-# INLINE effectDels #-}

effectPre :: Effect a -> Facts a
effectPre Effect { .. } = ePre
{-# INLINE effectPre #-}


-- Utility Functions -----------------------------------------------------------

-- | Apply an effect to the state given, returning a new state.
applyEffect :: Effect a -> State a -> State a
applyEffect Effect { .. } s = (s Set.\\ eDels) `Set.union` eAdds


-- Input Processing ------------------------------------------------------------

-- | Translate a domain and problem into a description of the initial state, the
-- goal state, and the connection graph.  The translation process includes
-- adding a special empty fact that all effects with no preconditions will have
-- as a precondition.  The empty fact is also added to the initial state, in the
-- event that the problem has an empty initial state.
buildConnGraph :: I.Domain a -> I.Problem -> IO (State a,Goals a,ConnGraph a)
buildConnGraph dom prob =
  do cgDirtyFacts   <- newIORef []
     cgDirtyEffects <- newIORef []

     rec (pres,adds,dels,effs) <-
             foldM (mkEffect cgDirtyEffects emptyFact factMap)
                 (Map.empty,Map.empty,Map.empty,[]) allEffs

         emptyFact <- mkFact cgDirtyFacts pres adds dels 0 (I.Fact "<empty>" [])

         facts <- zipWithM (mkFact cgDirtyFacts pres adds dels) [1 ..] allFacts
         let factMap = Map.fromList (zip allFacts facts)


     let resolveFacts fs = Set.fromList (map (factMap Map.!) fs)

         -- translate the initial state and goal
         state = Set.insert emptyFact (resolveFacts (I.probInit prob))
         goal  =                       resolveFacts (I.probGoal prob)

         cgFacts   = Set.fromList facts
         cgEffects = Set.fromList effs


     return (state, goal, ConnGraph { .. })

  where

  -- all ground facts
  allFacts = Set.toList (I.probFacts prob `Set.union` I.domFacts dom)

  -- all ground effects, extended with the preconditions from their operators
  allEffs = [ (ix, op, eff) | ix  <- [0 .. ]
                            | op  <- I.domOperators dom
                            , eff <- I.expandEffects op ]


  mkFact fDirtyList pres adds dels fId fProp =
    do fLevel  <- newIORef Nothing
       fIsTrue <- newIORef Nothing
       fIsGoal <- newIORef False
       fDirty  <- newIORef False

       return Fact { fPreCond = Map.findWithDefault Set.empty fProp pres
                   , fAdd     = Map.findWithDefault Set.empty fProp adds
                   , fDel     = Map.findWithDefault Set.empty fProp dels
                   , .. }

  mkEffect eDirtyList emptyFact facts (pres,adds,dels,effs) (eId,op,e) =
    do eLevel     <- newIORef Nothing
       eActivePre <- newIORef 0
       eInPlan    <- newIORef False
       eIsInH     <- newIORef False

       eDirty     <- newIORef False

       let refs fs = Set.fromList (map (facts Map.!) fs)

           -- When the preconditions for this fact are empty, make it depend on
           -- the special empty fact.
           ePre | null (I.ePre e) = Set.singleton emptyFact
                | otherwise       = refs (I.ePre e)

           eff     =  Effect { eNumPre = length (I.ePre e)
                             , eAdds   = refs (I.eAdd e)
                             , eDels   = refs (I.eDel e)
                             , eOp     = op
                             , .. }

           eff'      = Set.singleton eff
           merge f m = Map.insertWith Set.union f eff' m


       return ( foldr merge pres (I.ePre e)
              , foldr merge adds (I.eAdd e)
              , foldr merge dels (I.eDel e)
              , eff : effs )


-- Resetting -------------------------------------------------------------------

-- | Reset dirty references in the plan graph to their initial state.
resetConnGraph :: ConnGraph a -> IO ()
resetConnGraph ConnGraph { .. } =
  do facts <- atomicModifyIORef' cgDirtyFacts (\xs -> ([], xs))
     mapM_ resetFact facts

     effs <- atomicModifyIORef' cgDirtyEffects (\xs -> ([], xs))
     mapM_ resetEffect effs

resetFact :: Fact a -> IO ()
resetFact Fact { .. } =
  do writeIORef fLevel  Nothing
     writeIORef fIsTrue Nothing
     writeIORef fIsGoal False
     writeIORef fDirty  False

resetEffect :: Effect a -> IO ()
resetEffect Effect { .. } =
  do writeIORef eLevel Nothing
     writeIORef eActivePre 0
     writeIORef eInPlan False
     writeIORef eIsInH False
     writeIORef eDirty False


-- Utilities -------------------------------------------------------------------

printConnGraph :: ConnGraph a -> IO ()
printConnGraph cg =
  do printFacts cg
     printEffects cg

printFacts :: ConnGraph a -> IO ()
printFacts ConnGraph { .. } = mapM_ printFact cgFacts

printFact :: Fact a -> IO ()
printFact Fact { .. } =
  do putStrLn ("Fact: (" ++ show fId ++ ") " ++ show fProp)

     lev  <- readIORef fLevel
     true <- readIORef fIsTrue
     goal <- readIORef fIsGoal

     putStr $ unlines
       [ "  level:      " ++ show lev
       , "  is true:    " ++ show true
       , "  is goal:    " ++ show goal
       , "  required by:" ++ show (map eId (Set.toList fPreCond))
       , "  added by:   " ++ show (map eId (Set.toList fAdd))
       , "  deleted by: " ++ show (map eId (Set.toList fDel))
       ]

printEffects :: ConnGraph a -> IO ()
printEffects cg = mapM_ printEffect (cgEffects cg)

printEffect :: Effect a -> IO ()
printEffect Effect { .. } =
  do let I.Operator { .. } = eOp
     putStrLn ("Effect (" ++ show eId ++ ") " ++ T.unpack opName)

     lev <- readIORef eLevel

     putStr $ unlines
       [ " level:    " ++ show lev
       , " requires: " ++ show (map fProp (Set.toList ePre))
       , " adds:     " ++ show (map fProp (Set.toList eAdds))
       , " dels:     " ++ show (map fProp (Set.toList eDels))
       ]
