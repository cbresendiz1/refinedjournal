module AbstractRefinements where

import Data.IORef

{- The main point of this section is to provide some insight
   into the application of abstract refinements and good
   practices for applying this method of programming -}

-- Let's first create a data structures
-- Probably an binary tree : AVL Tree, maybe?

{-@
data PTree a =
    Pempty
  | Pnode {dvalue :: a
          ,dleft  :: PTree {v:a | dvalue >= v}
          ,dright :: PTree {v:a | dvalue <= v}}
@-}
data PTree a =
    Pempty
  | Pnode {dvalue :: a
          ,dleft  :: PTree a
          ,dright :: PTree a}

-- There has to be a way to automate this... --
{-
data BTree a =
    BEmpty
  | BNode {bvalue :: a
          ,bleft  :: BTree {v:a | bvalue > v}
          ,bright  :: BTree {v:a | bvalue < v}}
-}

{- This section is meant to look into how abstract refinements
   can be propagated through a liquidhaskell program. In the
   case above, there are no abstract refinements since there
   are no forall's -}

-- This example with abstract refinements --

{-@
data BTree a <p:: a -> Bool> =
    BEmpty
  | BNode {bvalue :: a
          ,bleft  :: BTree <p> a
          ,bright :: BTree <p> a}
@-}
data BTree a =
    BEmpty
  | BNode {bvalue :: a
          ,bleft  :: BTree a
          ,bright :: BTree a}

{-@ newBTree    :: x:a -> BTree<{\y -> x > y}> a @-}
newBTree :: a -> BTree a
newBTree x = BNode x BEmpty BEmpty

{-@ insertBTree :: x:a -> BTree a -> BTree <{\y -> x > y}>a  @-}
insertBTree :: a -> BTree a -> BTree a
insertBTree x yts = newBTree x

{- The problem you are having relates to how insertBTree
   is meant to express the invariants. You want to craete
   something really similar to Colin's example.

   You will need to work with logical constraints and
   inferences. These are important since they are used
   heavily with RGHaskell.

   Let's look at an example. Basic refinement types
   are meant to abstract and defer encoding of constraints
   on datatypes and functions for LH.
     EX: Int<p> -> Int<p> -> Int<p>
   The above example is a classic example that the LH
   community should know because of its usage in basic
   deferred refinement. Now when I look at it more. I
   wonder one thing... Does this allow implication.
   -- Question on implication without subtyping
     For example:
       Int<{\x -> x > 0}> -> Int<{\x -> x > 2}> -> Int<{\x -> x > 3}>
-}

{-@ build3OrAbove :: Int<{\x -> x > 0}> -> Int<{\x -> x > 2}> -> Int<{\x -> x > 3}> @-}
build3OrAbove :: Int -> Int -> Int
build3OrAbove x y = x + y

{- So in the case above, the Question about implication without
   subtyping turns out to be true. Or so it seems....
-}

{-EX
{-@ build4OrAbove :: Int<{\x -> x > 0}> -> Int<{\x -> x > 2}> -> Int<{\x -> x < 20}> @-}
{-@ build4OrAbove :: {v:Int | v > 0} -> Int<{\x -> x > 2}> -> Int<{\x -> x < 20}> @-}
build4OrAbove :: Int -> Int -> Int
build4OrAbove x y = x + y

--Error: Liquid Type Mismatch
--
--91 | build4OrAbove x y = x + y
--                         ^^^^^
--
--  Inferred type
--    VV : {v : GHC.Types.Int | v == x + y}
--
--  not a subtype of Required type
--    VV : {VV : GHC.Types.Int | VV < 20}
--
--  In Context
--    x : {v : GHC.Types.Int | v > 0}
--
--    y : {y : GHC.Types.Int | y > 2}
-}

{-
{-@ build20OrAbove :: Int<{\x -> x > 0}> -> Int<{\x -> x > 2}> -> Int<{\x -> x > 20}> @-}
{-@ build20OrAbove :: {v:Int | v > 0} -> Int<{\x -> x > 2}> -> Int<{\x -> x > 20}> @-}
build20OrAbove :: Int -> Int -> Int
build20OrAbove x y = x + y

--Error: Liquid Type Mismatch
--
--113 | build20OrAbove x y = x + y
--                           ^^^^^
--
--  Inferred type
--    VV : {v : GHC.Types.Int | v == x + y}
--
--  not a subtype of Required type
--    VV : {VV : GHC.Types.Int | VV > 20}
--
--  In Context
--    x : {v : GHC.Types.Int | v > 0}
--
--    y : {y : GHC.Types.Int | y > 2}
-}

{- So this gets into an interesting area, this enoding seems to work
   naturally, but actually only provides constraints and requires the
   programmer to input the correct values. This does not provide an
   invariants and check whether it works. For example, this example
   doesn't check if the previous constraints allow x + y > 20
   One example is 9 + 11, which returns 20.

   One thing I haven't tried out is the idea of pre and post
   conditions.
-}
-- Three Tests --
{-@ build20 :: x:Int <{\y -> y > 10}> -> Int<{\y -> y > 8 && y + x > 20}> -> Int<{\y -> y > 20}> @-}
build20 :: Int -> Int -> Int
build20 x y = x + y

test = build20 11 10

{-@ build202 :: x:Int<{\y -> y > 100}> -> Int<{\y -> y > 100}> -> Int<{\y -> y > 201}> @-}
build202 :: Int -> Int -> Int
build202 x y = x + y

{-@ build203 :: x:Int<{\y -> y > 0}> -> y:Int<{\y -> x + y > 200}> -> Int @-}
build203 :: Int -> Int -> Int
build203 x y = x + y

test2 = build203 200 1

{- This is an interesting case because this is only a post
   condition. This should be able to come up with a set of
   constraints and evaluate in the wrong answer

   I think the answer is that there are not enough
   constraints to construct the implications. -}
{-@ build204 :: x:Int -> y:Int -> Int<{\z -> z == 200}> @-}
build204 :: Int -> Int -> Int
build204 x y = x + y

--Error: Liquid Type Mismatch
--
--170 | build204 x y = x + y
--                     ^^^^^
--
--  Inferred type
--    VV : {v : GHC.Types.Int | v == x + y}
--
--  not a subtype of Required type
--    VV : {VV : GHC.Types.Int | VV == 200}
--
--  In Context
--    x : GHC.Types.Int
--
--    y : GHC.Types.Int

{- interesting... the "y" is not in scope for this one
{-@ build204 :: x:Int<{\z -> z + y == 200}> -> y:Int -> Int @-}
build204 :: Int -> Int -> Int
build204 x y = x + y -}
-- Still not good enough because logically you can prove this --
{- build2042 :: x:Int<{\y -> y > 0}> -> y:Int -> Int<{\z -> x + y == 200}>
build2042 :: Int -> Int -> Int
build2042 x y = x + y -}

{- In this case you would need to first define x:Int
     x:Int ->
   Next, you will need to add the constraint of y being
   the compliment or 200 - x
     y:Int<{\z -> z == 200 - x}> ->
   Finally, you can add the post condition
     d:Int<{\e -> e == 200}>

   So, these constraints and decisions should yield a
   constraint for the function below -}
{-@ build2045 :: x:Int -> Int<{\z -> z == 200 - x}> -> a:Int<{\e -> e == 200}> @-}
build2045 :: Int -> Int -> Int
build2045 x y = x + y

{- One thing I should mention is that can the first argument can
   take on the constraint of the second argument
   The examples above have shown that might not be possible do
   to the need to have y in scope

   So, the condition will need to be in the second argument -}

{- So in this case, I believe providing mathematical proofs
   with LiquidHaskell will be worthwhile -}

-- What about reflections and abstract refinements--
-- What about reflections and bounded quantification --

{- I think the best thing to do is figure out how
   reflections and abstract refinements work interact
   since bounded quantification doesn't seem to be
   easy to find. -}

-- This isn't helpful alone
starterFunction :: a -> a
starterFunction = undefined

-- This gets more interesting --
{-@ starterFunction
      :: forall <p :: a -> Bool
                ,r :: a -> Bool>.
     a<p> -> a<r> @-}

{- In this case, we want to create some invariants and
   constraints -}
{-@ upperFunction :: x:Int<{\z -> z == 200}> -> Int<{\y -> y == x + 2}> @-}
upperFunction :: Int -> Int
upperFunction = starterFunction

{- There is only one thing I should mention
   and is that implementation and types can provide
   the constraints and guideline. In the above
   case, the inductions are irrelevant and
   don't help us at all

   The other thing is that forall is the user's
   interface to provide the underlying logic for
   functions.
-}

-- In this case, I want to test my understanding of
-- forall with Lists that cannot be undone
-- This is important for cases about singletons
{-@ createList :: () -> [a] @-}
createList :: () -> [a]
createList () = undefined

{- I seem to be at a deadend. This does not help
   with thinking about types or singleton.
   Though, this might be really helpful in constructing
   functions with multiple things. This might be good
   for where clauses

   Also, this might be helpful for producers and consumers,
   such as, all created data structures will exhibit certain
   behavior...
-}


-- This time without a forall --
data GTree a =
    GEmpty
  | GNode {gvalue :: a
          ,gleft  :: BTree a
          ,gright :: BTree a}

{-@ createGTree :: GTree Int<{\x -> x > 0}> @-}
createGTree :: GTree Int
createGTree = undefined

{- Wierd, you you have two meanings with:
    GTree <{\x -> x > 0}> Int
    GTree Int <{\x -> x > 0}>

    This might because one handles:
      - GTree a, because it is between
      - GTree Int, because it is with the Int -}

{- ---------------------
   --- Important v ------
   --------------------- -}


-- What about reflexivity (checking out the difference of the two) --
{-@ createGTree2 :: GTree <{\y -> y == y}> Int @-}
createGTree2 :: GTree Int
createGTree2 = GEmpty

-- This does not work --
{- createGTree3 :: GTree <{\y -> y > 0}> Int @-
createGTree3 :: GTree Int
createGTree3 = GEmpty -}

-- This does work --
{-@ createGTree3 :: GTree Int<{\y -> y > 0}> @-}
createGTree3 :: GTree Int
createGTree3 = GEmpty

{- Now, coming back from what we were trying to do -}
--{-@ createTree :: GTree Int -> GTree Int -> GTree Int<{\y -> y > 1}> @-}
{-@ createTree :: GTree Int -> GTree Int -> GTree Int<{\y -> y > 0}> @-}
createTree :: GTree Int -> GTree Int -> GTree Int
createTree xts yts = createGTree3

{- Now, this is straight-forward and reiterates that
   constraints can be determined with the implementation
   and type system. So what are we getting at?

   Well, we are getting at how do predicates interact...
   This is how the logical constraints/bounded
   quantification might play.

   One thing I should mention is that this case has the
   constraint of being greater than 0, but is a distribution
   or constraints that applies to all or better yet a forall.
     "All elements must be greater than 0"

   This does not provide logical deduction or reasoning about
   multiple invariants, such as quicksort or computation that
   cannot be done correctly, such as permutation

   Let's think up some cases...
   What is something that isn't normally a subtype...
   Unlike { y > 0 => y > -1} -- oh that's nice I think this is useful

   Like why does:
   GTree a<{\y -> y > 0}> -> GTree a<{\y -> y > 10}>
     imply (that the sum of each node from each tree would be)
   GTree a<{\y -> y > 11}>
     and *not*
   GTree a<{\y -> y > 12}>
-}

-- Is it even possible for a function to have logical implication --
{-@ inject2 :: x:Int -> Int<{\y -> y == x + 2}> @-}
inject2 :: Int -> Int
inject2 x = x + 2

-- Maybe we aren't digging deep enough --
{-@ inject3 :: x:Int -> Int<{\y -> y == x + 3}> @-}
inject3 :: Int -> Int
inject3 x = join x numbah3
  where
    {-@ numbah3 :: Int<{\y -> y == 3}> @-}
    numbah3 :: Int
    numbah3 = 3
    {-@ join :: x:Int -> Int<{\z -> z == 3}> -> Int<{\y -> y == x + 3}> @-} -- added the post-condition
    join :: Int -> Int -> Int
    join value number = value + number

-- Oh my, I think I see the problem
-- If the predicate isn't mentioned at all, this could
-- lead to predicates having to be repeated

-- In inject3's case, the programs doesn't have
-- enough to deduce y == x + 3

-- After adding a post condition, the burden of proof is in
-- value

-- This is an cool practice problem

{- The next thing I need to do is look into how forall might be
   able to cut down in the amount of code I might need to right -}

{-@ orderedInvariants
      :: forall <p :: a -> Bool
                ,r :: a -> Bool>.
    {xx::a<p>, w::a<r> |- a<r> <: a<p>}
    a -> a<r> -> a<p> @-}
orderedInvariants :: a -> a -> a
orderedInvariants x y = undefined

{- This case is hard because we might not be getting all the
   invariants figured -}
-- construct a value that supports all invariants and logic --

-- with subtyping, you can consider subtyping as logical implication
{- ordered :: Int<p> -> Int<r> -> Int<g> -> Int<p,r,g>
ordered :: Int -> Int -> Int -> Int
ordered x y z = orderedInvariants x 0
-}

-- Let's make a record for understanding how invariants
 -- get passed

{-@ data Record a <p:: a -> Bool, r:: a -> Bool, g:: a -> Bool>
      = Record
      { pfield :: a<p>
      , rfield :: a<r>
      , gfield :: a<g>} @-}
data Record a = Record
  { pfield :: a
  , rfield :: a
  , gfield :: a}

{-@ assignRecord ::
      Int<{\x -> x > 0}> ->
      Int<{\x -> x > 1}> ->
      Int<{\x -> x == 1}> ->
      Record <{\x-> x > 0},{\x -> x > 1}, {\x -> x == 1}>Int @-}
{- Record Int<{\x-> x > 0},{\x -> x > 1}, {\x -> x == 1}> -}
-- the final type encoding doesn't work because of the way it reads
 -- predicates are applied to the interger instead of the whole
 -- one thing to note is that the predicates aren't enforced in
 -- this case, but are more like slots for creating the data structure
assignRecord :: Int -> Int -> Int -> Record Int
assignRecord p r g = Record p r g

{- Well, the problem right now is that you still don't
   understand the problem. What is the problem?

   Learning about implication
   -}

-- You need to assign the implication
  -- try data type
  -- try functions

{-@ functionTest
      :: forall <p :: a -> Bool
                ,r :: a -> Bool
                ,g :: a -> a -> Bool>.
   {xx::a |- a<g xx> <: a<p>}
   Int -> Int -> Int @-}
functionTest :: Int -> Int -> Int
functionTest x y = undefined

{- Ok, so you need to devise the logical implication
   and try to devise it yourself. -}

{- Inequality has subtyping, but there has to be
   some thing that allows logical implication
   Let's try creating some thing with mathematics

   What about the fibonacci sequence
   -}

{- Some ideas for figuring out the implication within
   functions. This can be invariants within data structures.
   What sort of invariants would be relevant.

   Combinatorics, Insertion sort, permutation.
   { if x => y, then there must exist an x such that x -> y }

   The problem is that a function needs to construct
   that logical transition. In the case of a reference
   it needs to satisfy that it follows the rely-guarantee
   logic. But the thing is it only applies to its creation
-}

{-@ data RGRef a <p:: a -> Bool, r:: a -> a -> Bool, g:: a -> a -> Bool> =
     Wrap (IORef a<p>) @-}
data RGRef a = Wrap (IORef a)
  deriving Eq
-- In this case, p is applied to RGRef and a

{- The next thing is that RGRef to follow rely-guarentee logic -}

{- This section is important since it will rely on the invariants
   you define here -}
{-@ newRGRef
      :: forall <p :: a -> Bool
                ,r :: a -> a -> Bool
                ,g :: a -> a -> Bool>.
    a<p> -> IO (RGRef <p,r,g> a) @-}
newRGRef :: a -> IO (RGRef a)
newRGRef e = do
  x <- newIORef e
  return $ Wrap x

--
{-@ createRef
      :: forall <p :: a -> Bool
                ,r :: a -> a -> Bool
                ,g :: a -> a -> Bool>.
    {x :: a<p> |- a<r x> <: a<p>}
    {x :: a<p> |- a<g x> <: a<r x>}
    {x :: a<p> |- {v:a | v = x} <: a<g x>}
    e: a ->  IO (RGRef a)
@-}
-- In this line (a<r x>) is suppose to have it's invariants and the p invariants
 -- But what is p in this case. x :: a<p> is meant to be the value that would
 -- make this possible.
 -- this will need to be translated
createRef :: a -> IO (RGRef a)
createRef x = newRGRef x

{-
  {xx::s<pre>, w::s<postg xx> |- s<postf w> <: s<post xx>}
    what does this even mean... this is not documented

   Here are a couple links that will be really handy

   - https://github.com/ucsd-progsys/liquidhaskell/pull/289
   - https://github.com/ucsd-progsys/liquidhaskell/issues/291
   - http://web.eecs.umich.edu/~weimerw/students/anish-ms-pres.pdf
   - http://goto.ucsd.edu/~nvazou/presentations/iohk17/11-bounded-refinements.html
   - http://web.eecs.umich.edu/~weimerw/students/anish-ms-pres.pdf
   - https://ranjitjhala.github.io/static/bounded_refinement_types.pdf
   - [old] https://github.com/ucsd-progsys/liquidhaskell/blob/1465a5cfd54c3077ce85306bfd2361ef4c6caab8/tests/pos/Constraints.hs
   - https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/filterAbs.hs#L3
   - https://github.com/ucsd-progsys/liquidhaskell/issues/178
   - https://github.com/ucsd-progsys/liquidhaskell/issues/296
   - https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/StateConstraints.hs
   - https://nikivazou.github.io/static/Haskell17/a-tale.pdf
   - http://ucsd-progsys.github.io/liquidhaskell-tutorial/08-measure-sets.html
   - https://github.com/ucsd-progsys/liquidhaskell/search?q=logical+constraints&unscoped_q=logical+constraints&type=Issues
   - https://github.com/ucsd-progsys/liquidhaskell/issues/223
   - https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/StateConstraints.hs
   - https://github.com/ucsd-progsys/liquidhaskell/pull/290
   - [old] https://github.com/ucsd-progsys/liquidhaskell/blob/4c2b9070ef220fb713bb5dfdaf0b9ddd73c2c9f0/tests/pos/ConstraintsAppend.hs
   - https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/absref/pos/ListISort-LType.hs
   - [important] https://conscientiousprogrammer.com/blog/2015/12/23/24-days-of-hackage-2015-day-23-liquid-haskell-refinement-types-for-the-real-world/
-}
