module LogicalConstraints where

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
