{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--reflection" @-}
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

{-@ insertElm :: forall <p:: a -> Bool,r:: a -> a -> Bool>.
    x:a<p> -> Checkthisout <p,r> a -> Checkthisout <p,r> a @-}
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
