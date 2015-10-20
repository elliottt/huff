{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Huff.ConnGraph (
    ConnGraph()
  , resetConnGraph
  , buildConnGraph

  , Key

  , FactRef(),   Fact,   getFact , fProp , fLevel , fIsTrue , fIsGoal , fDirty , fPreCond , fAdd , fDel
  , EffectRef(), Effect, getEffect , ePre , eAdds , eDels , eOp , eDirty , eInPlan , eIsInH , eNumPre , eLevel , eActivePre

  , Level

  , State, applyEffect
  , Goals
  , Facts
  , Effects

  , true, false

    -- * Debugging
  , printEffects, printEffect
  , printFacts, printFact
  ) where

import qualified Huff.Input as I
import qualified Huff.RefSet as RS

import           Control.Monad ( zipWithM, unless, (<=<) )
import           Data.IORef
                     ( IORef, newIORef, readIORef, writeIORef, modifyIORef )
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T

import           Data.Struct
import           Data.Struct.TH
import           Data.Vector (Vector)
import qualified Data.Vector as Vector
import           Control.Monad.Primitive
import           Data.Foldable (traverse_)


-- Connection Graph ------------------------------------------------------------

type Facts   = RS.RefSet FactRef
type Goals   = RS.RefSet FactRef
type State   = RS.RefSet FactRef
type Effects = RS.RefSet EffectRef

type Level   = Int

newtype FactRef = FactRef Int
                  deriving (Show,Eq,Ord,Enum)

newtype EffectRef = EffectRef Int
                    deriving (Show,Eq,Ord,Enum)

makeStruct [d|

  data ConnGraph' a s0 s = ConnGraph'
    { cgFacts        :: Vector (Fact' s0)
    , cgEffects      :: Vector (Effect' a s0)
    , cgDirtyFacts   :: [FactRef]
    , cgDirtyEffects :: [EffectRef]
    }

  data Fact' s = Fact'
    { fProp  :: I.Fact
    , fLevel :: {-# UNPACK #-} !Int -- Level
    , fIsTrue:: {-# UNPACK #-} !Int -- Level

    , fIsGoal:: {-# UNPACK #-} !Int -- Bool
    , fDirty :: {-# UNPACK #-} !Int -- Bool

    , fPreCond :: Effects
      -- ^ Effects that require this fact
    , fAdd   :: Effects
      -- ^ Effects that add this fact
    , fDel   :: Effects
      -- ^ Effects that delete this fact
    }

  data Effect' a s = Effect'
    { ePre       :: Facts
    , eAdds      :: Facts
    , eDels      :: Facts
    , eOp        :: I.Operator a
      -- ^ The operator that this effect came from

    , eDirty     :: {-# UNPACK #-} !Int -- Bool
    , eInPlan    :: {-# UNPACK #-} !Int -- Bool
      -- ^ Whether or not this effect is a member of the
      -- current relaxed plan

    , eIsInH     :: {-# UNPACK #-} !Int -- Bool
      -- ^ If this action is part of the helpful action set

    , eNumPre    :: {-# UNPACK #-} !Int
    , eLevel     :: {-# UNPACK #-} !Int -- Level
      -- ^ Membership level for this effect
    , eActivePre :: {-# UNPACK #-} !Int -- Level
      -- ^ Active preconditions for this effect
    }

  type Effect a  = Effect' a  (PrimState IO)
  type Fact      = Fact'      (PrimState IO)
  type ConnGraph a = ConnGraph' a (PrimState IO) (PrimState IO)

  |]


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
  do effects <- getField cgEffects cg
     effect <- Vector.indexM effects (fromEnum ref)
     adds <- getField eAdds effect
     dels <- getField eDels effect
     return $! (s RS.\\ dels) `RS.union` adds


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
     let facts' = Vector.fromList (emptyFact:facts)
     effs      <- zipWithM (mkEffect facts') (map EffectRef [0 ..]) allEffs
     cg <- newConnGraph' facts' (Vector.fromList effs) [] []
     return (RS.insert (FactRef 0) state,goal,cg)

  where
  -- translated goal and initial state
  state = RS.fromList (map (factRefs Map.!) (I.probInit prob))
  goal  = RS.fromList (map (factRefs Map.!) (I.probGoal prob))

  -- all ground facts
  allFacts = Set.toList (I.probFacts prob `Set.union` I.domFacts dom)
  factRefs = Map.fromList (zip allFacts (map FactRef [1 ..]))

  -- all ground effects, extended with the preconditions from their operators
  allEffs = [ (op, eff) | op  <- I.domOperators dom, eff <- I.expandEffects op ]
  mkFact prop = newFact'
     prop
     maxBound -- fLevel
     0 -- fIsTrue

     false -- fIsGoal
     false -- fDirty

     RS.empty -- fPreCond
     RS.empty -- fAdd
     RS.empty -- fDel

  mkEffect facts ix (op,e) =
    do let refs fs = RS.fromList (map (factRefs Map.!) fs)

           -- when the preconditions for this fact are empty, make it reference
           -- special fact 0, which represents the empty state.
           pre | null (I.ePre e) = RS.singleton (FactRef 0)
               | otherwise       = refs (I.ePre e)

           adds = refs (I.eAdd e)
           dels = refs (I.eDel e)

       eff <- newEffect' pre adds dels
                  op false false false (length (I.ePre e)) maxBound 0

       mapM_ dopre (RS.toList pre)
       mapM_ add (RS.toList adds)
       mapM_ del (RS.toList dels)

       return eff

    where
    dopre ref =
      do fact  <- Vector.indexM facts (fromEnum ref)
         modifyField fPreCond fact (RS.insert ix)

    add ref =
      do fact <- Vector.indexM facts (fromEnum ref)
         modifyField fAdd fact (RS.insert ix)

    del ref =
      do fact <- Vector.indexM facts (fromEnum ref)
         modifyField fDel fact (RS.insert ix)


-- Graph Interaction -----------------------------------------------------------

type family Key node :: * where
  Key (Fact' s)  = FactRef
  Key (Effect' a s) = EffectRef

getFact :: ConnGraph a -> FactRef -> IO Fact
getFact cg ref =
  do facts <- getField cgFacts cg
     fact <- Vector.indexM facts (fromEnum ref)
     isDirty <- (0/=) <$> getField fDirty fact
     unless isDirty $
       do setField fDirty fact true
          modifyField cgDirtyFacts cg (ref :)
     return fact

getEffect :: ConnGraph a -> EffectRef -> IO (Effect a)
getEffect connGraph ref =
  do v <- getField cgEffects connGraph
     eff <- Vector.indexM v (fromEnum ref)
     isDirty <- (0/=) <$> getField eDirty eff
     unless isDirty $
       do setField eDirty eff true
          modifyField cgDirtyEffects connGraph (ref :)
     return eff


modifyField :: (Struct o, PrimMonad m) => Field o a -> o (PrimState m) -> (a -> a) -> m ()
modifyField s = \o f -> setField s o . f =<< getField s o
{-# INLINE modifyField #-}


-- Resetting -------------------------------------------------------------------

-- | Reset dirty references in the plan graph to their initial state.
resetConnGraph :: ConnGraph a -> IO ()
resetConnGraph cg =
  do mapM_ (resetFact   <=< getFact   cg) =<< getField cgDirtyFacts   cg
     mapM_ (resetEffect <=< getEffect cg) =<< getField cgDirtyEffects cg
     setField cgDirtyFacts   cg []
     setField cgDirtyEffects cg []

resetFact :: Fact -> IO ()
resetFact fact =
  do setField fLevel fact maxBound
     setField fIsTrue fact 0
     setField fIsGoal fact false
     setField fDirty fact false

resetEffect :: Effect a -> IO ()
resetEffect effect =
  do setField eLevel effect maxBound
     setField eActivePre effect 0
     setField eInPlan effect false
     setField eIsInH effect false
     setField eDirty effect false

false = 0 :: Int
true  = 1 :: Int

-- Utilities -------------------------------------------------------------------

printFacts :: ConnGraph a -> IO ()
printFacts connGraph =
  do facts <- getField cgFacts connGraph
     amapWithKeyM_ printFact facts

printFact :: FactRef -> Fact -> IO ()
printFact ref fact =
  do prop <- getField fProp fact
     putStrLn ("Fact: (" ++ show ref ++ ") " ++ show prop)

     lev     <- getField fLevel fact
     isTrue  <- (/=0) <$> getField fIsTrue fact
     isGoal  <- (/=0) <$> getField fIsGoal fact
     add     <- getField fAdd fact
     del     <- getField fDel fact
     preCond <- getField fPreCond fact

     putStr $ unlines
       [ "  level:      " ++ show lev
       , "  is true:    " ++ show isTrue
       , "  is goal:    " ++ show isGoal
       , "  required by:" ++ show preCond
       , "  added by:   " ++ show add
       , "  deleted by: " ++ show del
       ]

printEffects :: ConnGraph a -> IO ()
printEffects cg = amapWithKeyM_ printEffect =<< getField cgEffects cg

printEffect :: EffectRef -> Effect a -> IO ()
printEffect ref effect =
  do I.Operator { .. } <- getField eOp effect
     putStrLn ("Effect (" ++ show ref ++ ") " ++ T.unpack opName)

     lev <- getField eLevel effect
     pre <- getField ePre effect
     adds <- getField eAdds effect
     dels <- getField eDels effect

     putStr $ unlines
       [ " level:    " ++ show lev
       , " requires: " ++ show pre
       , " adds:     " ++ show adds
       , " dels:     " ++ show dels
       ]

amapWithKeyM_ :: Enum i => (i -> e -> IO ()) -> Vector e -> IO ()
amapWithKeyM_ f arr = traverse_ (\(i,x) -> f (toEnum i) x) (Vector.indexed arr)
