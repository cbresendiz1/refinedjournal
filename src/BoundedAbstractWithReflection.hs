{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-@ LIQUID "--prune-unsorted" @-}
--{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module BoundedAbstractWithReflection where

{- I think a good starting point is to start
   making a list of data structures with
   abstract refinements and logical constraints
-}
-- Basic example
{-@
data STree a <p:: a -> Bool
             ,q:: a -> a -> Bool
             ,r:: a -> a -> Bool> =
    SEmpty
  | SNode {svalue :: a<p>
          ,sleft  :: STree a<q svalue>
          ,sright :: STree a<r svalue>}
@-}
data STree a =
    SEmpty
  | SNode {svalue :: a
          ,sleft  :: STree a
          ,sright :: STree a}

{-@ createSTree :: STree <{\x -> x > 0},{\x y -> x > y},{\x y -> y > x}> Int @-}
createSTree :: STree Int
createSTree = SEmpty

{-@ measure size @-}
{-@ size :: xts:STree a -> {v:Nat | v = size xts} @-}
size :: STree a -> Int
size SEmpty = 0
size (SNode v lt rt) = 1 + size lt + size rt

-- I think I need an assume function and verification
{- I think this is the start of something bad down below -}

-- Let's try with a data structure that has only one value it most check no matter what

{-@ data Checkthisout a <p :: a -> Bool, r :: a -> a -> Bool> =
        EmptyCheck
      | Manager {king :: a<p>
                ,lackeys :: [a<p>]<r king>} @-}
data Checkthisout a =
    EmptyCheck
  | Manager {king    :: a
            ,lackeys :: [a]}

--{-@ insertElm :: forall <p:: a -> Bool,r:: a -> a -> Bool>.
--    x:a<p> -> Checkthisout <p,r> a -> Checkthisout <p,r> a @-}
insertElm :: a -> Checkthisout a -> Checkthisout a
insertElm x EmptyCheck = Manager x []
insertElm l (Manager k lacks) = Manager k (l:lacks)


{- I think expanding the predicates would be helpful
   Also, what are your questions and what do you need to know
   Well, my question in this case is to figure out why Manager
   doesn't work
-}

-- probably if you need to merge like mergebranch, you will need to create an append

{- TODO -}
-- For this example, you need to figure out how logical constraints can be transferred with
--   with operations like insertions and deletion
-- don't use assume!
{-@ mergeBranch :: forall<p:: a -> Bool, l:: a -> a -> Bool, r:: a -> a -> Bool>.
    a<p> -> STree <p,l,r> a -> STree <p,l,r> a -> STree <p,l,r> a @-} -- don't we get different invariants with different branches
mergeBranch :: a -> STree a -> STree a -> STree a
mergeBranch v lt rt = undefined --SNode v lt rt

{-@ constructNode
      :: forall<p :: a -> Bool, l :: a -> a -> Bool, r :: a -> a -> Bool, newq :: a -> a -> Bool, newr :: a -> a -> Bool>.
    x:a<p> -> lts:STree <p,l,r> a -> rts:STree <p,l,r> a -> STree <p,l,r> a @-}
constructNode :: a -> STree a -> STree a -> STree a
constructNode x lts rts = mergeBranch x lts rts

-- oh, my this might need reflection

{-@ insertSTree :: forall <p :: a -> Bool, q :: a -> a -> Bool, r :: a -> a -> Bool>.
    Ord a => a<p> -> xts:STree <p,r,q> a -> STree <p,r,q> a / [size xts] @-}
insertSTree :: Ord a => a -> STree a -> STree a
insertSTree x SEmpty = SNode x SEmpty SEmpty
insertSTree x (SNode v slt srt) =
  if x > v then
    SNode v slt undefined--slt (insertSTree x srt)
  else
    SNode v undefined srt--(insertSTree x slt) srt


{-
There are a ton of papers to read that will help in this eternal search for
refinement nirvana

- Deriving Law-Abiding Instances
- Liquid Types by Manuel Eberi
- Local Refinement Types
- Ryan Scotts talk on Refinements
- Also, go to benchmarks/icfp15/pos/Overview.lhs
- Automated verification tools for Haskell programs by Baranowski (Very helpful)
- Finding and Fixing Bugs in LiquidHaskell
-}

{- Can you add parametric invariants in {v...} instances

   Let's try the tree data structure againt -}

{-@
data ITree a <p:: a -> Bool
             ,q:: a -> a -> Bool
             ,r:: a -> a -> Bool> =
    IEmpty
  | INode {ivalue :: a<p>
          ,ileft  :: ITree a<q ivalue>
          ,irigth :: ITree a<r ivalue>}
@-}
data ITree a =
    IEmpty
  | INode {ivalue :: a
          ,ileft  :: ITree a
          ,iright :: ITree a}

{-@ measure llen @-}
{-@ llen :: ITree a -> Nat @-}
llen :: ITree a -> Int
llen IEmpty        = 0
llen (INode v lt rt) = 1 Prelude.+ llen lt + llen rt

{-@ createNormalOrder :: ITree <{\x -> x > 0},{\x y -> x > y},{\x y -> y > x}> Int @-}
createNormalOrder :: ITree Int
createNormalOrder = INode 3 (INode 2 IEmpty IEmpty) (INode 4 IEmpty IEmpty)

{-@ createReverseOrder :: ITree <{\x -> x > 0},{\x y -> y > x},{\x y -> x > y}> Int @-}
createReverseOrder :: ITree Int
createReverseOrder = INode 3 (INode 4 IEmpty IEmpty) (INode 2 IEmpty (INode 1 IEmpty IEmpty))
-- If you did this without specifying the p,q,r this would not be possible.

{- Let's try a polymorphic insertion -}
--{-@ reflect insert @-}
--insert :: Ord a => a -> ITree a -> ITree a
--insert x emp@IEmpty = INode x emp emp
--insert x (INode v lt rt) =
--  if x > v then
--    INode v (insert x lt) rt
--  else
--    INode v lt (insert x rt)

--{-@ insertAscendingOrder
--      :: forall a <p :: a -> Bool
--                  ,q :: a -> a -> Bool
--                  ,r :: a -> a -> Bool>.
--
--    Ord a => a<p> -> ITree <p,q,r> a -> ITree <p,q,r> a @-}
--insertAscendingOrder :: forall a. Ord a => a -> ITree a -> ITree a
--insertAscendingOrder x emp@IEmpty = INode x emp emp
--insertAscendingOrder x (INode v lt rt)
--  | x > v = INode v lt (insertAscendingOrder x rt)
--  | otherwise = INode v (insertAscendingOrder x lt) rt
--
{-@
data HList a <p:: a -> Bool,q :: a -> a -> Bool> =
    HNil
  | HCons {hhead :: a<p>
          ,htail :: HList a<q hhead>}
@-}
data HList a =
    HNil
  | HCons {hhead :: a
          ,htail :: HList a}

{-@ testingList :: forall <p::a -> Bool,q::a -> a -> Bool>.
    a<p> -> HList a<p> -> HList a<p> @-}
testingList :: a -> HList a -> HList a
testingList x xs = HCons x xs

{-@
data PList a <p:: a -> a -> Bool> =
    PNil
  | PCons {phead :: a
          ,ptail :: PList <p> a<p phead>}
@-}
data PList a =
    PNil
  | PCons {phead :: a
          ,ptail :: PList a}

{-@ type IncrList a = PList <{\x v -> x <= v}> a @-}

{-@ testIncr :: IncrList Int @-}
testIncr :: PList Int
testIncr = PCons 1 (PCons 2 (PCons 3 (PCons 4 PNil)))

{-@
data GList a <p:: a -> a -> Bool> where
    GNil  :: forall a. GList<p>a
  | GCons :: forall a. h:a -> GList <p> a<p h> -> GList <p> a
@-}
data GList a where
  GNil  :: GList a
  GCons :: a -> GList a -> GList a

{-@ testIncrGADT :: GList <{\x y -> x > y}> Int @-}
testIncrGADT :: GList Int
testIncrGADT = GCons 3 GNil

testInsertIncr :: Int -> GList Int -> GList Int
testInsertIncr x xs = GCons x xs

-- I am really having trouble with insertions
-- Man, what the heck

{-@ type GIncrList a = GList <{\x y -> x > y}> a @-}

{-@ insert :: Ord a => a -> GIncrList a -> GIncrList a @-}
insert :: Ord a => a -> GList a -> GList a
insert x xs = GNil
insert x (GCons y ys)
  | x <= y = GCons x (GCons y ys)
  | otherwise = GCons y (insert x ys)

-- Perhaps I didn't create some thing for equality

{-@ type OrdList a = [a]<{\x v -> x <= v}> @-}

{-@ insertSort :: (Ord a) => [a] -> OrdList a @-}
insertSort :: (Ord a) => [a] -> [a]
insertSort = foldr insertH []

{-@ insertH :: (Ord a) => a -> OrdList a -> OrdList a @-}
insertH :: (Ord a) => a -> [a] -> [a]
insertH x [] = [x]
insertH x (y : ys)
  | x <= y = x : y : ys
  | otherwise = y : insertH x ys

{-@
data ListA [alen] a <p :: a -> a -> Bool> where
    ANil :: ListA <p> a
  | ACons :: h:a -> ListA <p> a<p h> -> ListA <p> a
@-}
data ListA a where
  ANil :: ListA a
  ACons :: a -> ListA a -> ListA a

{-@ type OrderList a = ListA <{\x y -> x <= y}> a @-}

{-@ measure alen @-}
alen :: ListA a -> Int
alen ANil = 0
alen (ACons x xs) = 1 Prelude.+ alen xs

--{-@ insertA :: (Ord a) => a -> xs:OrderList a -> OrderList a / [alen xs] @-}
--insertA :: Ord a => a -> ListA a -> ListA a
--insertA y ANil = ACons y ANil
--insertA y t@(ACons x xs)
--  | y <= x = ACons y (insertA x xs)
--  | otherwise = ACons x t


{-@ autosize L @-}
data L a where
  LNil  :: L a
  LCons :: a -> L a -> L a

{- This looks like induction. So you
   will need a base case and prove termination-}

{- This is still a problem.
   I'm getting an error that it is
   not matching the inferred type/subtyping -}

{-@
data IncList a where
    Emp :: IncList a
  | (:<) :: hd:a -> tl:IncList {v:a | hd <= v} -> IncList a
@-}
data IncList a where
  Emp :: IncList a
  (:<) :: a -> IncList a -> IncList a

insertInc :: Ord a => a -> IncList a -> IncList a
insertInc y Emp = y :< Emp
insertInc y (x :< xs)
  | y <= x = y :< (x :< xs)
  | otherwise = x :< insertInc y xs

{-@
data AbsList a <p:: a -> a -> Bool> where
    Amp :: AbsList <p> (a <p h>)
  | (:>) :: h:a -> AbsList <p> (a <p h>)-> AbsList <p> (a <p h>)
@-}
data AbsList a where
  Amp  :: AbsList a
  (:>) :: a -> AbsList a -> AbsList a

{-@ absinsert :: Ord a => a -> AbsList <{\x v -> x <= v}> a -> AbsList <{\x v -> x <= v}> a @-}
absinsert :: Ord a => a -> AbsList a -> AbsList a
absinsert x Amp = x :> Amp
absinsert x (y :> ys)
  | x <= y = x :>  (y :> ys)
  | otherwise = y :> (absinsert x ys)



{-@ type OrdList a = [a]<{\x v -> x <= v}> @-}

{-@ insertn :: Ord a => a -> [a]<{\x v -> x <= v}> -> [a]<{\x v -> x <= v}> @-}
--{-@ insertn :: Ord a => a -> OrdList a -> OrdList a @-}
insertn x [] = [x]
insertn x (y:ys)
  | x <= y = x : y : ys
  | otherwise = y : insertn x ys


{-@
data NewList a <p:: a -> a -> Bool> =
    NewNil
  | NewCons {nhd :: a
            ,ntl :: NewList <p> (a<p nhd>)}
@-}
data NewList a =
    NewNil
  | NewCons {nhd :: a
            ,ntl :: NewList a}

{-@ newinsert :: Ord a => a -> NewList <{\x v -> x <= v}> a -> NewList <{\x v -> x <= v}> a @-}
newinsert :: Ord a => a -> NewList a -> NewList a
newinsert x NewNil = NewCons x NewNil
newinsert x t@(NewCons y ys)
  | x <= y = NewCons x (NewCons y ys)
  | otherwise = NewCons y (newinsert x ys)
