{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-termination" @-}
module BoundedAbstract where

import Prelude hiding (filter, find, (.), (++))
import Language.Haskell.Liquid.Prelude

{-@
find
  :: forall <p:: Int -> Bool>.
  {x :: Int<p> |- {v:Int | v == x + 1} <: Int<p>}
  (Int -> Bool) -> (Int -> a) -> Int<p> -> a
@-}
find :: (Int -> Bool) -> (Int -> a) -> Int -> a
find q k i | q i       = k i
           | otherwise = find q k (i + 1)

{-@
(.)
  :: forall <p :: b -> c -> Bool
            ,q :: a -> b -> Bool
            ,r :: a -> c -> Bool>.
     {x :: a, w :: b<q x> |- c<p w> <: c<r x>}
     f:(y:b -> c<p y>)
  -> g:(z:a -> b<q z>)
  -> x:a -> c<r x>
@-}
(.) f g x = f (g x)

{-@
checksome
  :: forall <p :: Int -> Bool
            ,r :: Int -> Bool>.
  {x::Int<p> |- {v:Int | v == x + 2} <: Int<r>}
  Int<p> -> Int -> Int<r>
@-}
checksome :: Int -> Int -> Int
checksome x y = x + 2

{-@ filter
      :: forall <p :: a -> Bool
                ,w :: a -> Bool -> Bool>.
      {y :: a, b::{v:Bool<w y> | v} |- {v:a | v == y} <: a<p>}
      (x:a -> Bool<w x>) -> [a] -> [a<p>]
@-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x = x : filter f xs
  | otherwise = filter f xs
filter _ [] = []

{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v = (m - x) + n} @-}
plusminus :: Int -> Int -> Int -> Int
plusminus n m = (n+) . (m-)

{-@ constraints
      :: forall <p:: Int -> Bool
                ,r:: Int -> Bool
                ,g:: Int -> Bool>.
    {x::Int<g> |- Int<r> <: Int<p>}
    {x::Int<r> |- {v:Int | v > x + 2} <: Int<r>}
    Int<r> -> Int<r> -> Int<r> @-}
constraints :: Int -> Int -> Int
constraints x y = x + 3

-- so from my understanding {v:Int | v == x + y} refers
-- to the output of the function

{- Ok, so subtyping seems to make more sense now,
   so I will need to start getting these and implementing -}

{-@ data STree a <s :: a -> Bool, t :: a -> Bool, u :: a -> Bool> =
        SEmpty
      | SNode {svalue :: a<s>
              ,sright :: STree a<t>
              ,sleft  :: STree a<u>} @-}
data STree a =
    SEmpty
  | SNode {svalue :: a
          ,sleft  :: STree a
          ,sright :: STree a}

{-@ createNewTree ::
    Ord a => a -> STree a -> STree a @-}
createNewTree :: Ord a => a -> STree a -> STree a
createNewTree v SEmpty = SNode v SEmpty SEmpty
createNewTree v (SNode sv slt srt) =
  if (v > sv) then
    SNode sv slt (createNewTree v srt)
  else
    SNode sv (createNewTree v slt) srt

{- Now that you understand more about refinement types, abstract refinements, and bounded refinements, you can probably get
started on the RGRef verification -}
-- You should probably draft up a question about certain mechanics in LH. Maybe a in-depth analysis of LH

{-@ type SortedList = STree<{\x -> x > 0}, {\x -> x > 2}, {\x -> x > 3}> a @-}

--{-@ useConstraint :: {v:Int | v > 0} -> Int<{\x -> x > 0},{\x -> x > -1}> @-} -- this should not work unless it is inference
{-@ bound recProp @-}
recProp hdProp tlProp recProp
  = \hd tl -> hdProp hd ==> tlProp tl ==> recProp hd tl

-- {-@ (++) :: forall < hdprop :: a -> Bool
--                    , tlprop :: a -> Bool
--                    , p :: a -> a -> Bool>.
--         (RecProp a hdprop tlprop p) =>
--         [a< hdprop >]< p > -> [a< tlprop >]< p > -> [a]< p > @-}
-- (++) []      ys = ys
-- (++) (x:xs) ys = x:(xs ++ ys)



-- {-@
-- (.-.) :: forall < p :: b -> c -> Bool
--                , q :: a -> b -> Bool
--                , r :: a -> c -> Bool>.
--        (Chain b c a p q r) =>
--        (y:b -> c< p y >)
--     -> (z:a -> b< q z >)
--     ->  x:a -> c< r x >
-- @-}
(.-.) f g x = f (g x)

{-@ bound chain @-}
chain p q r = (\ x y z -> q x y ==> p y z ==> r x z)
