{-@ LIQUID "--higherorder"@-}
module LogicalConstraints where

import Unsafe.Coerce

{- This section of the code is meant to deal with
   logical constraints and how they apply with
   a variety of data structures. -}

-- This data structures will require 3 constaints

{-@ data TreeList a <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool> =
        TEmpty
      | TNode {tvalue :: a<p>
              ,tright :: [a<r tvalue>]
              ,tleft  :: [a<g tvalue>]}
@-}
data TreeList a =
    TEmpty
  | TNode {tvalue :: a
          ,tright :: [a]
          ,tleft  :: [a]}

{-@ newTreeList
      :: forall <p:: a -> Bool
                ,r:: a -> a -> Bool
                ,g:: a -> a -> Bool>.
    {x :: a<p> |- a<r x> <: a<p>}
    {x :: a<p> |- a<g x> <: a<r x>}
    {x :: a<p> |- {v:a<p> | v = x} <: a<g x>}
    a<p> -> TreeList <p,r,g> a @-}
-- a -> TreeList <p,r,g> a @-}
{- The case above ^ fails because you need to
   somehow introduce the proposition p because it
   cannot be provided by the output type. -}

newTreeList :: a -> TreeList a
newTreeList x = TNode x [] []

{- Let's try two things:
     - add non-empty as a field for the list
     - more arguments to check out where invariants appear
         and how they interact (probably through application) -}
-- Trying out empty fields --
{-@ newTreeList2
      :: forall <p:: a -> Bool
                ,r:: a -> a -> Bool
                ,g:: a -> a -> Bool>.
    {x :: a<p> |- a<r x> <: a<p>}
    {x :: a<p> |- a<g x> <: a<p>}
    {x :: a<p> |- {v:a | v = x} <: a<p>}
    a<p> -> TreeList <p,r,g> a @-}
{- In this case, {v:a | r x v} and {v:a | g x v} must
   be a subtype of <p>

   So in one case, if something is an equality
     say {\x -> x = 0} this would have hold for
     other predicates, so {\x -> x >= 0} should hold
-}
newTreeList2 :: a -> TreeList a
newTreeList2 x = TNode x [] []

{-@ createList :: TreeList <{\x -> x > 0},{\x y -> x > y},{\x y -> y > x}> Int @-}
createList :: TreeList Int
createList = undefined action
  where
    {-@ action :: TreeList <{\x -> x = 0},{\x y -> x > y},{\x y -> x < y}>Int@-}
    action :: TreeList Int
    action = newTreeList2 0
    refinedAdd :: Int -> TreeList Int -- an addition that needs to preserve invariants
    refinedAdd v = undefined

{- also you could have something like
   {x:: a<p> |- a<r x>} instead of {x:: a<p> |- a<r x> <: a<p>}
     so does that mean, for a<r x> <: a<p>, that it needs to
     satisfy a<p> and a<r x>

    I will need to test this later
-}

-- In this case, you will need to test how logical implication works within
-- a variety of situations

-- Let's make a lot of data structures.

-- Standard Tree
{-@
data STree a <p:: a -> Bool
             ,r:: a -> a -> Bool
             ,g:: a -> a -> Bool> =
    SEmpty
  | SNode {svalue :: a<p>
          ,sright :: STree a<r svalue>
          ,sleft  :: STree a<g svalue>}
@-}
data STree a =
    SEmpty
  | SNode {svalue :: a
          ,sright :: STree a
          ,sleft  :: STree a}

{-@ createSTree
      :: forall <p :: a -> Bool
                ,r :: a -> a -> Bool
                ,g :: a -> a -> Bool>.
   {x::a<p> |- a<r x> <: a<p>}
   {x::a<p> |- a<g x> <: a<p>}
   {x::a<p> |- {v:a | v = x} <: a<p>}
   a<p> -> STree<p,r,g> a @-}
createSTree :: a -> STree a
createSTree x = SNode x SEmpty SEmpty

{- The refinement above makes no sense to me
   because you can have x > 1 be a subtype of
   x > 0, which means it is implied. But the
   thing is that there is an implicit subtyping
   that occurs within LiquidHaskell
-}

{-@ createSomeTree :: Int<{\x -> x > 0}> -> STree<{\x -> x > 0},{\x y-> x > 2},{\x y -> x > 2}> Int @-}
createSomeTree :: Int -> STree Int
createSomeTree x = runTree x
  where
    {-@ runTree :: Int<{\x -> x > 0}> -> STree<{\x -> x > 0},{\x y -> x > 2},{\x y -> x > 2}> Int @-}
    runTree :: Int -> STree Int
    runTree = createSTree

-- Mod is going to be the example
-- Multiplication invariants
-- Category theory invariants
-- Fibonacci sequence invariants
subtypeInType :: Int -> Int -> Int
subtypeInType x y = undefined

{- how does subtyping work in Liquid. It almost seems
   to something else. This seems to be implicit
-}

{-@ startSystem
      :: forall <p:: a -> Bool
                ,r:: a -> a -> Bool>.
    {xx::a |- a<r xx> <: a<p>}
    {xx::a |- a<p> <: a<r xx>}
    x:a<p> -> a<r x>
@-}
startSystem :: a -> a
startSystem x = x

{-@ propFunct :: Int<{\x -> x > -2}> -> Int<{\x -> x > -3}> @-}
propFunct :: Int -> Int
propFunct x = value
  where
    {-@ value :: Int<{\x -> x > -2}> @-}
    value :: Int
    value = x

-- Try an example from the paper --
 -- The paper is Refinement Types for Haskell --

---- This doesn't work
-- {-@ createValue :: Int<{\x -> x >= 0}> -> Int<{\x -> x > 0}> @-}
{-@ createValue :: Int<{\x -> x > 0}> -> Int<{\x -> x >= 0}> @-}
createValue :: Int -> Int
createValue = \x -> x

-- subtyping in liquid haskell
 -- {xx:: a<p> |- a<r xx> <: a<p>}
subtypeExample :: Int -> Int -> Int
subtypeExample x y = undefined

-- modular arithmetic
{-@ additionMod
   :: Int<{\x -> x mod 12 == 0}>
   -> Int<{\x -> x mod 12 == 0}>
   -> Int<{\x -> x mod 12 == 0}> @-}
additionMod :: Int -> Int -> Int
additionMod x y = x - y

{-@ boundedQ
      :: forall <p :: a -> Bool
                ,r :: a -> a -> Bool
                ,g :: a -> Bool>.
    {xx:: a<p> |- a<r xx> <: a<p>}
    {xx:: a<p> |- a<g> <: a<p>}
    {xx:: a<p> |- a<g> <: a<r xx> }
    {xx:: a<p> |- {v:a | v = xx} <: a<g>}
    x:a<p> -> a @-}
boundedQ :: a -> a
boundedQ x = x

{-@ type Incr = Int @-}

-- functions that take in certain values --
-- functions that provide certain operations --
-- with abstract refinements we can define it later --

{-@ modAbstraction
      :: forall <p :: Int -> Bool
                ,r :: Int -> Bool>.
    {xx::Int<p> |- Int<r> <: Int<p>}
    {xx::Int<p> |- {v:Int | v = xx} <: Int<r>}
    Int<p> -> Int<r> @-}
modAbstraction :: Int -> Int
modAbstraction x = x

{-@ newInvariant :: Int<{\x -> x mod 6 == 0}> -> Int<{\x -> x mod 7 == 0}> @-}
newInvariant :: Int -> Int
newInvariant x = x * 21

-- oh higher order functions....

{-@ higherOrder
      :: forall <p :: a -> Bool
                ,r :: a -> Bool>.
    {xx :: a<p> |- a<r> <: a<p>}
    {xx :: a<p> |- {v:a | v = xx} <: a<r>}
    a<p> -> (a<p> -> a<r>) -> a<r> @-}
higherOrder :: a -> (a -> a) -> a
higherOrder x f = f x

{-@ mustbeModular :: Int<{\x -> x mod 8 = 0}> -> Int<{\x -> x mod 16 = 0}> @-}
mustbeModular :: Int -> Int
mustbeModular x = higherOrder x mult4
  where
    {-@ mult4 :: forall <p:: Int -> Bool
                        ,r:: Int -> Bool>.
        {xx :: Int<p> |- Int<r> <: Int<p>}
        {xx :: Int<p> |- {v:Int | v = xx} <: Int<r>}
        Int<p> -> Int<r> @-}
    mult4 :: Int -> Int
    mult4 x = x*2
