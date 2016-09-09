Huff
====

Huff is an implementation of the fast-forward forward-chaining planner in
Haskell. The main interface is the quasi-quoter `huff`, which allows the user to
define re-usable domains that can be used with the planner to solve different
problems.


Example
-------

Consider the blocks world planning domain from [Chapter
11](http://aima.cs.berkeley.edu/2nd-ed/newchap11.pdf) of "Artificial
Intelligence: A Modern Approach". The domain includes two actions, `Move` and
`MoveToTable`, four objects, `A`, `B`, `C`, `Table`, and two predicates, `On`
and `Clear`. Embedding the domain in Haskell using `huff` looks like this:

```haskell
module Main where

import Huff

[huff|

  domain BlocksWorld {
    object Obj = A | B | C | Table

    predicate on(Obj,Obj), clear(Obj)

    operator Move(b: Obj, x: Obj, y: Obj) {
      requires: on(b,x), clear(b), clear(y)
      effect:   on(b,y), clear(x), !clear(y)
    }

    operator MoveToTable(b: Obj, x: Obj) {
      requires: on(b,x), clear(b)
      effect:   on(b,Table), clear(x)
    }
  }

|]

```

The quasi-quoter will introduce the following declarations:
* A data declaration for the `Obj` object
* A data declaration for the `BlocksWorld` domain, that will consist of two
  constructors `Move :: Obj -> Obj -> Obj -> BlocksWorld` and `MoveToTable ::
  Obj -> Obj -> BlocksWorld`
* Two classes called `Has_on` and `Has_clear`, that define the `on` and `clear`
  functions, respectively
* Instances of the two `Has` classes for `Literal` and `Term`
* The `blocksWorld` function of the type `[Literal] -> [Term] -> Spec BlocksWorld`

The `blocksWorld` function accepts the initial state and goal, and produces a
`Spec BlocksWorld` value that can be used in conjunction with the `findPlan`
function to attempt to find a plan. For example, the problem specified in
chapter 11 Russel and Norvig can be solved as follows:

```haskell
main =
  do mb <- findPlan $ blocksWorld [ on A Table, on B Table, on C Table, clear A
                                  , clear B, clear C ]
                                  [on A B, n B C]
     print mb
```

Running the example will produce the output:

```shell
$ find dist-newstyle -name blocksWorld -type f -exec {} \;
Just [MoveTo B Table C, MoveTo A Table B]
```
