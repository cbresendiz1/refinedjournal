{-# LANGUAGE ScopedTypeVariables #-}
--{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--prune-unsorted" @-}
--{-@ LIQUID "--reflection" @-}

--{-@ LIQUID "--ple" @-}
module RG where

import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators
import Data.IORef
import Prelude hiding (IO)
import GHC.Base
import Unsafe.Coerce

{-@
data RGRef a <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>
     = Wrap (IORef a<p>)
@-}
data RGRef a =
  Wrap (IORef a)
  deriving Eq

{-@ newRGRef :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>.
    {x :: a<p> |- a<r x> <: a<p>}
    {x :: a<p> |- a<g x> <: a<r x>}
    {x :: a<p> |- {v:a | v = x} <: a<g x>}
    e:a<p> -> IO (RGRef <p,r,g> a) @-}
newRGRef :: a -> IO (RGRef a)
newRGRef e =
  (>>=) (newIORef e) (\ref -> return (Wrap ref))

--{-@ stuff :: x:a<p> -> RGRef a<v x> (Equalitiy) @-}

{- These have to be assumed -}
{-@ measure pastValue :: Eq a => RGRef a -> a -> Bool @-}
{-@ measure terminalValue :: RGRef a -> a @-}
{-@ measure shareValue :: RGRef a -> a @-}

-- axiom_pastIsTerminal
-- the problem with axiom_pastIsTerminal is that
-- it uses RGRef and comparing values is never useful
-- because we can never use IORef internally because of
-- the IO monad
{-
For example, to check if past values are the same, you will
need to make a read and compare the two values. This would
lead to the function entering the IO context

So, in this case, the invariants or structure of the program can
be assumed. How would one prove the values are the same without
any heap access?

So what does axiom_pastIsTerminal prove? Better question
what does axiom_pastIsTerminal take and what can we figure
out from it...

It takes:
  - ref:RGRef a  -- takes a RGRef reference
  -> v:a       -- takes a value that was the past value
  -> (a -> a -> a) -- takes the value 'a' as the pastValue and checks with the rely predicate
  -> (a -> a -> a) -- takes the value 'a' as the pastValue and checks with the guarantee predicate
  -> Bool
-}

{-@ assume axiom_pastIsTerminal
      :: forall <p :: a -> Bool,r :: a -> a -> Bool, g :: a -> a -> Bool>.
      ref : RGRef <p,r,g> a ->
      v: {v:a | (pastValue ref v)} ->
      (x:{x:a | x = v} -> y:a<r x> -> {z:a | (z = y) && (z = x)}) ->
      (x:{x:a | x = v} -> y:a<g x> -> {z:a | (z = y) && (z = x)}) ->
      {b:Bool | ((terminalValue ref) = v) <=> (pastValue ref v)} @-}
axiom_pastIsTerminal :: RGRef a -> a -> (a -> a -> a) -> (a -> a -> a) -> Bool
axiom_pastIsTerminal = undefined

grabValues :: IO ()
grabValues = do
  ref <- newIORef 1
  checkIfValueSame 1 ref
--  modifyIORef' ref (\x -> x + 1)
  return ()

proofForIORef :: Int -> IORef Int -> Proof
proofForIORef x yref = ()

--{-@ reflect fib @-}
--{-@ fib :: i:Nat -> Nat / [i] @-}
--fib :: Int -> Int
--fib i | i == 0 = 0
--      | i == 1 = 1
--      | otherwise = fib (i-1) + fib (i-2)
--
--{-@ fibTwoPretty :: { fib 2 == 1 } @-}
--fibTwoPretty
--  =   fib 2
--  === fib 1 + fib 0
--  === 1 + 0
--  *** QED
--
--{-@ fibTree :: _ -> { fib 3 == 2 } @-}
--fibTree _
--  =   fib 3
--  === fib 2 + fib 1
--  === 1 + 1
--  === 2
--  *** QED
--
---- {-@ incMutate :: _ -> { incMutate 1 xref -> IORef Int } @-}
--
--data Tree a
--  = FEmpty
--  | FNode a (Tree a) (Tree a)
--  deriving Eq
--
--{-@ reflect rotateTreeNode @-}
--rotateTreeNode :: Eq a => Tree a -> Tree a
--rotateTreeNode FEmpty = FEmpty
--rotateTreeNode (FNode v lt rt)
--  | lt == FEmpty = FEmpty
--  | otherwise = FEmpty
--
--treesEq :: Eq a => Tree a -> Tree a -> Bool
--treesEq xts yts = xts == yts
--
--{-@ provenRotation :: Eq a => t:Tree a -> { FEmpty = (rotateTreeNode t) } @-}
--provenRotation :: Eq a => Tree a -> Proof
--provenRotation = undefined -- ok so this is pretty useless unless you satisfy the proof
----provenRotation i
----  | i == FEmpty
----  =   rotateTreeNode i
----  *** QED
----  | otherwise
----  = rotateTreeNode i
----  *** QED
--
{-@ modABCProof :: a:Nat -> b:Nat -> n:Nat ->
      {(a * b) mod n == ((a mod n) * (b mod n)) mod n} @-}
modABCProof :: Int -> Int -> Int -> Proof
modABCProof = undefined

{- let's lie -}
{-@ tellingLies :: v:{v:Nat | v == 2} -> x:{x:Nat | x == 3} -> {v = x} @-}
tellingLies :: Int -> Int -> ()
tellingLies x y = undefined

provingIORef :: a -> IORef a -> ()
provingIORef x xref = undefined

{-@ checkIfValueSame :: x:Int -> IORef Int<{\y -> y = x}> -> IO () @-}
checkIfValueSame :: Int -> IORef Int -> IO ()
checkIfValueSame xr x = return ()

{-@ createNewIORRef :: Nat -> IO (IORef Nat) @-}
createNewIORRef :: Int -> IO (IORef Int)
createNewIORRef x = newIORef x

--{-@ strictMod :: IORef Nat -> (i:Nat -> Nat<{\x -> x = i + 1}>) -> IO () @-}
--strictMod :: IORef Int -> (Int -> Int) -> IO ()
--strictMod ref f = modifyIORef' ref f

{-@ modifyValue :: v:Nat -> IO Nat<{\x -> x == v + 1}> @-}
modifyValue :: Int -> IO Int
modifyValue val =
  do refd <- createNewIORRef val
     strictMod refd (+1)
     readIORef refd
  where
    {-@ strictMod :: IORef Nat -> (Nat -> Nat) -> IO () @-}
    strictMod :: IORef Int -> (Int -> Int) -> IO ()
    strictMod ref f = dmod ref f

--{-@ sameValue :: y:Nat -> x:Nat -> {x = y} @-}
--sameValue :: Int -> Int -> IO ()
--sameValue r x =
--  do val <- newIORef r
--     dmod val (+1)

{-@ job :: IO Bool @-}
job = do
  p <- newIORef (0 :: Int)
  writeIORef p 10
  v <- readIORef p
  return (v == 10)

{-@ mods :: IORef Int -> (Int -> Int) -> IO () @-}
mods :: IORef Int -> (Int -> Int) -> IO ()
mods = undefined

{-@ assume dmod :: IORef Nat -> (Nat -> Nat) -> IO () @-}
dmod :: IORef Int -> (Int -> Int) -> IO ()
dmod = modifyIORef'

modifyIORefE :: IORef a -> (a -> a) -> IO ()
modifyIORefE ref f =
  (>>=) (readIORef ref) (\x -> writeIORef ref (f x))

{-@ rgcheck :: Nat -> Proof @-}
rgcheck :: Int -> Proof
rgcheck i
  | i == 0 =
    (>>=) (modifyValue i) (\x -> return x)
  *** QED
  | otherwise = () *** Admit

someFunct :: Int -> (Int, Double)
someFunct x = (x, 1.0)

atomicModifyIORefE :: IORef a -> (a -> (a, b)) -> IO b
atomicModifyIORefE ref fTup = atomicModifyIORef' ref fTup

{-@ measure pastValueb :: IORef a -> b -> b @-}

--{-@ assume downcast ::
--    forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool
--                { x::b |- b <: a }
--                { x::b |- b<r x> <: b<p> }
--                ref:RGRef<p,r,g> a ->
--                {v:b | pastValue ref v } ->
--                {r : RGRef<p,r,g> b | ref = r } @-}
--downcast :: RGRef a -> b -> RGRef b
--downcast r v =  (unsafeCoerce r)

{-@
data Tree a <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool> =
    Empty
  | Node {value :: a<p>
         ,left  :: Tree a
         ,right :: Tree a}
@-}
data Tree a =
    Empty
  | Node a (Tree a) (Tree a)

{-@ measure pastValuebr :: Tree a -> b -> Bool @-}



--{-@ assume dcast :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>.
--                { x::b |- b <: a }
--                { x::b |- b<r x> <: b<p> }
--                ref:Tree<p,r,g> a ->
--                {v:b | pastValuebr ref v } ->
--                {r : Tree<p,r,g> b | ref = r } @-}
--dcast :: Tree a -> b -> Tree b
--dcast r v =  (unsafeCoerce r)

proofs :: Int -> IO ()
proofs v =
  do x <- newIORef v
     atomicModifyIORef' x (\n -> (n + 1, ()))

atomicMod :: Int -> IO Int
atomicMod x =
  do n <- newIORef x
     atomicModifyIORef n (\_ -> (x + 1, x + 1))

--{-@ createRef :: v:Nat -> IO (IORef Nat<{\x -> x = v}>) @-}
--createRef :: Int -> IO (IORef Int)
--createRef v =
--  (>>=) (newIORef nt) (\r -> return r)
--  where
--    {-@ nt :: Nat @-}
--    nt :: Int
--    nt = 1

{-@ natt :: Nat @-}
natt :: Int
natt = 1

--{-@ crr :: IO (IORef Nat) @-}
--crr :: IO (IORef Int)
--crr = createRef recc
--  where
--    {-@ recc :: Nat @-}
--    recc :: Int
--    recc = 3

--{-@ proofOfTerminal :: x:Int -> IORef Int<{\y -> x = y}> -> (Int -> Int -> Int) -> (Int -> Int -> Int) -> IO Int<{\z -> z = x + 1}> @-}
--proofOfTerminal :: Int -> IORef Int -> (Int -> Int -> Int) -> (Int -> Int -> Int) -> IO Int
--proofOfTerminal x yref f g = atomicModifyIORef yref (\y -> (y, y + 1))

{- Take a look at the small laptop proof -}

{-@ measure extVal :: IO Int -> Int @-}

nice :: IO ()
nice = do a <- return 0
          liquidAssert (a == 0) (return ())

{-@ checkVal :: x:IO Int -> y:IO Int -> {x = y} @-}
checkVal :: IO Int -> IO Int -> Proof
checkVal x y = undefined

stuff :: ()
stuff = checkVal (return 1) (return 3)

{-@ assume injectStable2 :: forall <p :: a -> Bool,
                                         q :: a -> Bool,
                                         r :: a -> a -> Bool,
                                         g :: a -> a -> Bool>.
                    pf:(j:a<q> -> k:a<r j> -> {z:a<q> | z = k}) ->
                    ref:RGRef<p,r,g> a ->
                    {v:a<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> a) | (ref = r)} @-}
injectStable2 :: (a -> a -> a) -> RGRef a -> a -> RGRef a
injectStable2 pf ref v = liquidAssume undefined ref


{-@ assume injectStable :: forall <p :: a -> Bool,
                                   q :: a -> Bool,
                                   r :: a -> a -> Bool,
                                   g :: a -> a -> Bool>.
                    {x::a<q> |- a<r x> <: a<q>}
                    ref:RGRef<p,r,g> a ->
                    {v:a<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> a) | (ref = r)} @-}
injectStable :: RGRef a -> a -> RGRef a
injectStable ref v = liquidAssume undefined ref

test = liquidAssert (1 == 1) 1

--liquidAssume :: b:Bool -> a -> a
test2 = liquidAssume True 1

inject :: Int -> Int
inject x = liquidAssume False 10

injectmore :: Int -> Int
injectmore x
  | x == 10 = liquidAssert (x == 10) x
  | otherwise = x

tryoutUnsafe = unsafeCoerce



--
