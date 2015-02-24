{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

module Huff.ConnGraph (
    ConnGraph()
  , resetConnGraph
  , buildConnGraph

  , Key

  , FactRef(),   Fact(..),   getFact
  , EffectRef(), Effect(..), getEffect

  , Level

  , State, applyEffect
  , Goals
  , Facts
  , Effects

    -- * Debugging
  , printEffects, printEffect
  , printFacts, printFact
  ) where

import qualified Huff.Input as I
import qualified Huff.RefSet as RS

import           Control.Monad ( zipWithM, unless, (<=<) )
import           Data.Array.IO
import           Data.IORef
                     ( IORef, newIORef, readIORef, writeIORef, modifyIORef )
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T


-- Connection Graph ------------------------------------------------------------

type Facts   = RS.RefSet FactRef
type Goals   = RS.RefSet FactRef
type State   = RS.RefSet FactRef
type Effects = RS.RefSet EffectRef

type Level   = Int

data ConnGraph a = ConnGraph { cgFacts        :: !(IOArray FactRef Fact)
                             , cgEffects      :: !(IOArray EffectRef (Effect a))
                             , cgDirtyFacts   :: !(IORef [FactRef])
                             , cgDirtyEffects :: !(IORef [EffectRef])
                             }


newtype FactRef = FactRef Int
                  deriving (Show,Eq,Ord,Ix,Enum)

newtype EffectRef = EffectRef Int
                    deriving (Show,Eq,Ord,Ix,Enum)


data Fact = Fact { fProp  :: !I.Fact
                 , fLevel :: !(IORef Level)

                 , fIsTrue:: !(IORef Level)
                 , fIsGoal:: !(IORef Bool)

                 , fDirty :: !(IORef Bool)

                 , fPreCond :: !Effects
                   -- ^ Effects that require this fact
                 , fAdd   :: !Effects
                   -- ^ Effects that add this fact
                 , fDel   :: !Effects
                   -- ^ Effects that delete this fact
                 }

data Effect a = Effect { ePre       :: !Facts
                       , eNumPre    :: !Int
                       , eAdds      :: !Facts
                       , eDels      :: !Facts
                       , eOp        :: !(I.Operator a)
                         -- ^ The operator that this effect came from

                       , eDirty     :: !(IORef Bool)

                       , eInPlan    :: !(IORef Bool)
                         -- ^ Whether or not this effect is a member of the
                         -- current relaxed plan

                       , eIsInH     :: !(IORef Bool)
                         -- ^ If this action is part of the helpful action set

                       , eLevel     :: !(IORef Level)
                         -- ^ Membership level for this effect
                       , eActivePre :: !(IORef Level)
                         -- ^ Active preconditions for this effect
                       }


instance RS.Ref FactRef where
  toRef               = FactRef
  fromRef (FactRef r) = r

instance RS.Ref EffectRef where
  toRef                 = EffectRef
  fromRef (EffectRef r) = r


-- Utility Functions -----------------------------------------------------------

-- | Apply an effect to the state given, returning a new state.
applyEffect :: ConnGraph a -> EffectRef -> State -> IO State
applyEffect cg ref s =
  do Effect { .. } <- readArray (cgEffects cg) ref
     return $! (s RS.\\ eDels) `RS.union` eAdds


-- Input Processing ------------------------------------------------------------

-- | Translate a domain and problem into a description of the initial state, the
-- goal state, and the connection graph.  The translation process includes
-- adding a special empty fact that all effects with no preconditions will have
-- as a precondition.  The empty fact is also added to the initial state, in the
-- event that the problem has an empty initial state.
buildConnGraph :: I.Domain a -> I.Problem -> IO (State,Goals,ConnGraph a)
buildConnGraph dom prob =
  do emptyFact <- mkFact (I.Fact "<empty>" [])
     facts     <- mapM mkFact allFacts
     cgFacts   <- newListArray (FactRef 0, FactRef (length facts))
                      (emptyFact : facts)

     effs      <- zipWithM (mkEffect cgFacts) (map EffectRef [0 ..]) allEffs
     cgEffects <- newListArray (EffectRef 0, EffectRef (length effs - 1)) effs

     cgDirtyFacts   <- newIORef []
     cgDirtyEffects <- newIORef []

     return (RS.insert (FactRef 0) state,goal,ConnGraph { .. })

  where
  -- translated goal and initial state
  state = RS.fromList (map (factRefs Map.!) (I.probInit prob))
  goal  = RS.fromList (map (factRefs Map.!) (I.probGoal prob))

  -- all ground facts
  allFacts = Set.toList (I.probFacts prob `Set.union` I.domFacts dom)
  factRefs = Map.fromList (zip allFacts (map FactRef [1 ..]))

  -- all ground effects, extended with the preconditions from their operators
  allEffs = [ (op, eff) | op  <- I.domOperators dom, eff <- I.expandEffects op ]
  mkFact fProp =
    do fLevel  <- newIORef maxBound
       fIsTrue <- newIORef 0
       fIsGoal <- newIORef False
       fDirty  <- newIORef False
       return Fact { fPreCond = RS.empty
                   , fAdd     = RS.empty
                   , fDel     = RS.empty
                   , .. }

  mkEffect facts ix (op,e) =
    do eLevel     <- newIORef maxBound
       eActivePre <- newIORef 0
       eInPlan    <- newIORef False
       eIsInH     <- newIORef False

       eDirty     <- newIORef False

       let refs fs = RS.fromList (map (factRefs Map.!) fs)

           -- when the preconditions for this fact are empty, make it reference
           -- special fact 0, which represents the empty state.
           ePre | null (I.ePre e) = RS.singleton (FactRef 0)
                | otherwise       = refs (I.ePre e)

           eff     =  Effect { eNumPre = length (I.ePre e)
                             , eAdds   = refs (I.eAdd e)
                             , eDels   = refs (I.eDel e)
                             , eOp     = op
                             , .. }

       mapM_ pre (RS.toList  ePre)
       mapM_ add (RS.toList (eAdds eff))
       mapM_ del (RS.toList (eDels eff))

       return eff

    where
    pre ref =
      do Fact { .. } <- readArray facts ref
         writeArray facts ref Fact { fPreCond = RS.insert ix fPreCond, .. }

    add ref =
      do Fact { .. } <- readArray facts ref
         writeArray facts ref Fact { fAdd = RS.insert ix fAdd, .. }

    del ref =
      do Fact { .. } <- readArray facts ref
         writeArray facts ref Fact { fDel = RS.insert ix fDel, .. }


-- Graph Interaction -----------------------------------------------------------

type family Key node :: * where
  Key Fact       = FactRef
  Key (Effect a) = EffectRef

getFact :: ConnGraph a -> FactRef -> IO Fact
getFact ConnGraph { .. } ref =
  do fact @ Fact { .. } <- readArray cgFacts ref
     isDirty            <- readIORef fDirty
     unless isDirty $
       do writeIORef fDirty True
          modifyIORef cgDirtyFacts (ref :)
     return fact

getEffect :: ConnGraph a -> EffectRef -> IO (Effect a)
getEffect ConnGraph { .. } ref =
  do eff @ Effect { .. } <- readArray cgEffects ref
     isDirty             <- readIORef eDirty
     unless isDirty $
       do writeIORef eDirty True
          modifyIORef cgDirtyEffects (ref :)
     return eff


-- Resetting -------------------------------------------------------------------

-- | Reset dirty references in the plan graph to their initial state.
resetConnGraph :: ConnGraph a -> IO ()
resetConnGraph cg =
  do mapM_ (resetFact   <=< getFact   cg) =<< readIORef (cgDirtyFacts   cg)
     mapM_ (resetEffect <=< getEffect cg) =<< readIORef (cgDirtyEffects cg)
     writeIORef (cgDirtyFacts   cg) []
     writeIORef (cgDirtyEffects cg) []

resetFact :: Fact -> IO ()
resetFact Fact { .. } =
  do writeIORef fLevel maxBound
     writeIORef fIsTrue 0
     writeIORef fIsGoal False
     writeIORef fDirty False

resetEffect :: Effect a -> IO ()
resetEffect Effect { .. } =
  do writeIORef eLevel maxBound
     writeIORef eActivePre 0
     writeIORef eInPlan False
     writeIORef eIsInH False
     writeIORef eDirty False


-- Utilities -------------------------------------------------------------------

printFacts :: ConnGraph a -> IO ()
printFacts ConnGraph { .. } = amapWithKeyM_ printFact cgFacts

printFact :: FactRef -> Fact -> IO ()
printFact ref Fact { .. } =
  do putStrLn ("Fact: (" ++ show ref ++ ") " ++ show fProp)

     lev    <- readIORef fLevel
     isTrue <- readIORef fIsTrue
     isGoal <- readIORef fIsGoal

     putStr $ unlines
       [ "  level:      " ++ show lev
       , "  is true:    " ++ show isTrue
       , "  is goal:    " ++ show isGoal
       , "  required by:" ++ show fPreCond
       , "  added by:   " ++ show fAdd
       , "  deleted by: " ++ show fDel
       ]

printEffects :: ConnGraph a -> IO ()
printEffects cg = amapWithKeyM_ printEffect (cgEffects cg)

printEffect :: EffectRef -> Effect a -> IO ()
printEffect ref Effect { .. } =
  do let I.Operator { .. } = eOp
     putStrLn ("Effect (" ++ show ref ++ ") " ++ T.unpack opName)

     lev <- readIORef eLevel

     putStr $ unlines
       [ " level:    " ++ show lev
       , " requires: " ++ show ePre
       , " adds:     " ++ show eAdds
       , " dels:     " ++ show eDels
       ]

amapWithKeyM_ :: (Enum i, Ix i) => (i -> e -> IO ()) -> IOArray i e -> IO ()
amapWithKeyM_ f arr =
  do (lo,hi) <- getBounds arr

     let go i | i > hi    =    return ()
              | otherwise = do f i =<< readArray arr i
                               go (succ i)

     go lo
