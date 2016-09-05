{-# LANGUAGE QuasiQuotes #-}

module Huff where

import qualified Huff.Compile as I
import qualified Huff.Input as Input
import           Huff.QQ (huff)
import qualified Huff.FF.Planner as I

import           Control.Monad (forM_,unless,when)
import qualified Data.Map.Strict as Map
import           Data.Maybe (mapMaybe)
import           Data.Proxy (Proxy(..))
import qualified Data.Set as Set
import qualified Data.Text as T
import           GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import           MonadLib (StateT,get,set,runM,Id)


[huff|

  domain BlocksWorld {

    object Object = Table | A | B | C

    predicate isTable(Object), on(Object, Object), clear(Object)

    operator StackOnTable(x:Object) {
      requires: clear(x)
      effect:   on(x,Table)
    }

    operator Stack(x : Object, y : Object) {
      requires: clear(x), clear(y), !isTable(y)
      effect:   on(x,y), !clear(y)
    }
  
  }

|]

{-
  }
  
  problem blocksWorld1 {
    domain:
      blocksWorld
  
    init:
      on(a,b),
      on(b,table),
      on(c,table),
      clear(c),
      clear(a)
  
    goal:
      on(a,b),
      on(b,c),
      on(c,table),
      clear(a)
  }
  
  domain shopping {
  
    type place = supermarket    as "Supermarket"
               | hardware-store as "Hardware Store"
               | home           as "Home"
  
    type good  = hammer
               | drill
               | banana
  
    predicate at(place), sells(place,good), has(good)
  
    operator going(from : place, to : place) {
      value: $("Going from " ++ show from ++ " to " ++ show to ++ ".")
      requires: at(from)
      effect: not(at(from)), at(to)
    }
  
    operator buy(thing : good, from : place)
      value: $("Buying " ++ show thing ++ " from " ++ show from ++ ".")
      requires: at(from), sells(from,thing)
      effect: has(thing)
  
  }
  
  problem buyHammerAndBanana {
  
    domain shopping
  
    init
      at(home)
  
    goal
      at(home), has(hammer), has(banana)
  
  }
  
  
|]
-}
