{-# LANGUAGE QuasiQuotes #-}

module Main where

import Huff

[huff|

  domain BlocksWorld {

    object Obj = A | B | C | Table

    predicate on(Obj,Obj), clear(Obj)

    operator MoveTo(b: Obj, x: Obj, y: Obj) {
      requires: on(b,x), clear(b), clear(y)
      effect:   on(b,y), clear(x), !clear(y)
    }

    operator MoveToTable(b: Obj, x: Obj) {
      requires: on(b,x), clear(b)
      effect:   on(b,Table), clear(x)
    }
  }

|]

main =
  do mb <- findPlan $ blocksWorld [ on A Table, on B Table, on C Table
                                  , clear A, clear B, clear C ]
                                  [ on A B, on B C ]

     print mb
