{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
--{-@ LIQUID "--prune-unsorted" @-}
module LogicalConstraintsReflection where

{-@
data Tree [ht] a <p :: a -> Bool> =
    Empty
  | Node {value :: a<p>
         ,right :: Tree a
         ,left  :: Tree a}
@-}
data Tree a =
    Empty
  | Node {value :: a
         ,right :: Tree a
         ,left  :: Tree a}

-- Logical constraints on subtyping --

{-@ tempFunct ::
  Int -> Int -> Int -> Tree <{\x -> x > 0}> Int @-}
tempFunct :: Int -> Int -> Int -> Tree Int
tempFunct x y z = undefined

{-@
tempSubtyping
  :: forall <p :: Int -> Bool, r :: Int -> Bool>.
  {x::Int<p>, y::Int<r> |- Int<r> <: Int<p>}
Int<p> -> Int<r> -> Int<r> @-}
tempSubtyping :: Int -> Int -> Int
tempSubtyping x y = y --funct x y
--  where
--    {-@ funct ::
--          forall <p :: Int -> Bool, r :: Int -> Bool>.
--        {x::Int<p>, y::Int<r> |- Int<r> <: Int<p>}
--        Int<p> -> Int<r> -> Int<r> @-}
--    funct :: Int -> Int -> Int
--    funct v z = z
{- The one below is better -}
--    {-@ funct ::
--          forall <p:: a -> Bool,r::a -> Bool>.
--        {x::a<p>, y::a<r> |- a<r> <: a<p>}
--        {x::a<p>, y::a<r> |- {v:a<r> | v == x + y} <: a<r>}
--        Num a => a<p> -> a<r> -> a<r> @-}
--    funct x y = y
{-@ class Multi a where
      multiple :: a -> a -> a @-}
class Multi a where
  multiple :: a -> a -> a

instance Multi Int where
{-@ instance Multi Nat where
    multiple :: Nat -> Nat -> Nat @-}
  multiple x y = x * y

refFunct :: Multi a => a -> a -> a
refFunct x y = multiple x y

refValue = refFunct value value2
  where
    {-@ value :: Int @-}
    value :: Int
    value = 3
    {-@ value2 :: Int @-}
    value2 :: Int
    value2 = 1

{-@ bin ::
      forall <p:: Int -> Bool,r:: Int -> Bool>.
    {x:: Int<p>, y::Int<r> |- Int<r> <: Int<p>}
    Int<p> -> Int<r> -> Int<r> @-}
bin :: Int -> Int -> Int
bin x y = undefined --x + y

-- '+' does not have the correct traits from reasoning
-- typeclasses seem to be a solution

{-@ addModulus :: v:Int<{\x -> x mod 3 = 0}> -> d:Int<{\x -> x mod 3 = 0}> -> Int<{\x -> ((v mod 3) * (d mod 3)) mod 3 == 0}> @-}
addModulus :: Int -> Int -> Int
addModulus x y =  x * y

-- Fast Modular Multiplication

{-@ measure ht @-}
{-@ ht :: Tree a -> Nat @-}
ht :: Tree a -> Int
ht Empty = 0
ht (Node v rt lt) = 1 + ht rt + ht lt

{-@ generateTreeof3 :: Nat -> {v: Tree Int | ht v == 3} @-}
generateTreeof3 :: Int -> Tree Int
generateTreeof3 x = Node 3 (Node 2 (Node 2 Empty Empty) Empty) Empty

-- And there is no computing for the size

{-@ reflect balanced @-}
balanced :: Tree a -> Int
balanced Empty = 0
balanced (Node v lt rt) = 1 + balanced lt
