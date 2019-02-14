{-# LANGUAGE GADTs #-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--higherorder" @-}
--{-@ LIQUID "--reflection" @-}
--{-@ LIQUID "--ple" @-}
module InsertRefinement where

{-@
data IList a <p :: a -> a -> Bool> where
    INil :: IList <p> a
  | ICons :: h:a -> IList <p> a<p h> -> IList <p> a<p h>
 @-}
data IList a where
  INil :: IList a
  ICons :: a -> IList a -> IList a

{-@ insertI :: Ord a => a -> IList <{\x y -> x <= y}> a -> IList <{\x y -> x <= y}> a @-}
insertI :: Ord a => a -> IList a -> IList a
insertI x INil = ICons x INil
insertI x t@(ICons y ys)
  | x <= y = ICons x (ICons y ys)
  | otherwise = ICons y (insertI x ys)

{- Insertion abstract refinement -}
{- I think the next thing is to make a general refined functions
   with bounded constraints -}

{-@ range :: lo:Int -> hi:Int -> [Int] / [hi - lo] @-}
range :: Int -> Int -> [Int]
range lo hi
  | lo < hi = lo : range (lo + 1) hi
  | otherwise = []

{-@ ack :: m:Nat -> n:Nat -> Nat / [m, n] @-}
ack :: Int -> Int -> Int
ack m n
  | m == 0 = n + 1
  | n == 0 = ack (m - 1) 1
  | otherwise = ack (m - 1) (ack m (n - 1))

{-@ trymap :: (a -> b) -> xs:[a] -> [b] / [len xs] @-}
trymap :: (a -> b) -> [a] -> [b]
trymap f [] = []
trymap f (x:xs) = f x : trymap f xs

{-@ nmerge :: Ord a => xs:[a] -> ys:[a] -> [a] / [len xs + len ys] @-}
nmerge :: Ord a => [a] -> [a] -> [a]
nmerge xs [] = xs
nmerge [] ys = ys
nmerge (x:xs) (y:ys)
  | x < y = x : nmerge xs (y:ys)
  | otherwise = y : nmerge (x:xs) ys

--{-@
--data AList a <p :: a -> a -> Bool> [mlen] where
--    ANil :: AList <p> a
--  | ACons :: h:a -> AList <p> a<p h> -> AList <p> a<p h>
-- @-}
{-@ measure mlen @-}
{-@ mlen :: AList a -> Nat @-}
mlen :: AList a -> Int
mlen (ANil) = 0
mlen (ACons x xs) = 1 Prelude.+ mlen xs

{-@
data AList [mlen] a <p :: a -> a -> Bool> where
    ANil :: AList <p> a
  | ACons :: h:a -> AList <p> a<p h> -> AList <p> a<p h>
 @-}
data AList a where
  ANil :: AList a
  ACons :: a -> AList a -> AList a

--{-@ data AList [mlen] a = ANil | ACons { x::a, xs:: AList a} @-}
--data AList a = ANil | ACons { x::a, xs:: AList a}

{-@ insertAL :: Ord a => a -> xs:AList a -> AList a / [mlen xs] @-}
insertAL :: Ord a => a -> AList a -> AList a
insertAL x ANil   = ACons x ANil
insertAL x (ACons y ys)
  | x > y = ACons y (insertAL x ys)
  | otherwise = ACons x (ACons y ys)

{-@ reverseAcc :: xs:AList a -> ys:AList a -> AList a / [mlen ys] @-}
reverseAcc :: AList a -> AList a -> AList a
reverseAcc ANil ANil = ANil
reverseAcc acc ANil = acc
reverseAcc acc (ACons x xs) = reverseAcc (ACons x acc) xs


{-@ merge :: Ord a => xs:AList a -> ys:AList a -> AList a / [mlen xs + mlen ys] @-}
merge :: Ord a => AList a -> AList a -> AList a
merge ANil ys   = ys
merge xs   ANil = xs
merge (ACons x xs) (ACons y ys)
  | x < y    = ACons x (merge xs (ACons y ys))
  | otherwise = ACons y (merge (ACons x xs) ys)

{- Create generalized list -}
{-@ genInsert :: forall <p :: a -> a -> Bool>.
    (Eq a, Ord a) => a -> ys:AList <{\x y -> x <= y}> a -> AList <{\x y -> x <= y}> a @-}
genInsert :: (Ord a, Eq a) => a -> AList a -> AList a
genInsert x ANil = ACons x ANil
genInsert x (ACons y ys)
  | x <= y = ACons x (genInsert y ys)
  | otherwise = ACons y (genInsert x ys)


-- predicates need to subtypes of increasing
-- how do we enforcing increasing values
-- how do we enforcing patterns

-- Attempt weird pattern with last
{-@ genPattern :: (Ord a, Eq a) => a -> ys:AList a -> AList a @-}
genPattern :: (Ord a, Eq a) => a -> AList a -> AList a
genPattern x ANil = ACons x ANil
genPattern x (ACons y ys)
  | x <= y = ACons x (ACons y ys)
  | otherwise = ACons y (genPattern x ys)

{-@
genIdea :: forall <p :: a -> a -> Bool>.
a -> AList <p> a -> AList <p> a
@-}
genIdea :: a -> AList a -> AList a
genIdea x xs = undefined

-- invariant for a data structures --
-- increasing refinements --

{-@
absFunction ::
forall <p :: a -> a -> Bool,r :: a -> a -> Bool, s :: a -> a -> Bool>.
a -> a -> a
@-}
absFunction :: a -> a -> a
absFunction x y = x

-- would instances would help with polymorphism
-- if you had a good season, I would try to have another good season
