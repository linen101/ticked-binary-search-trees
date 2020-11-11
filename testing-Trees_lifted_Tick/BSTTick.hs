{-@ LIQUID "--reflection" @-}

module BSTTick ( Tree, Maybe, height, size, set, get) where

import Language.Haskell.Liquid.RTick
import ProofCombinators
import Functions_Types (max, min, Nat, Maybe(Nothing,Just))
import Prelude hiding (Maybe(Nothing,Just), max, min, pure, return)


-------------------------------------------------------------------------------
-- | Datatype:
-------------------------------------------------------------------------------

{-@ type NETree k v= {t: Tree k v | 0 < size t} @-}

{-@ data Tree k v <l :: root:k -> x:k -> Bool, r :: root:k -> x:k -> Bool> 
        = Nil
        | Node { key :: k
               , val :: v
               , tl  :: Tree <l, r> (k <l key>) v
               , tr  :: Tree <l, r> (k <r key>) v }
@-}

data Tree k v = Nil | Node k v (Tree k v) (Tree k v) deriving Show

{-@ type BST k v = Tree <{\root k -> k < root}, {\root k -> k > root}> k v @-}

-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

{-@ measure size @-}
{-@ size :: Tree k v -> Nat @-}
size                :: Tree k v -> Int
size Nil            = 0
size (Node _ _ l r) = 1 + size l + size r
{-@ invariant {t:Tree k v | 0 <= size t} @-}

{-@ measure height @-}
{-@ height :: Tree k v -> Nat @-}
height :: Tree k v -> Int
height Nil            = 0
height (Node k v l r) = 1 + max (height l) (height r)
{-@ invariant {t:Tree k v | 0 <= height t} @-}

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ empty :: { t:Tick { ts:(BST k v) | size ts == 0 } | tcost t == 0 } @-}
empty :: Tick (Tree k v)
empty = pure Nil

{-@ reflect singleton@-}
{-@ singleton :: k -> v -> { t:Tick { ts:(BST k v) | size ts == 1 } | tcost t == 0 } @-}
singleton :: Ord k=> k -> v -> Tick (Tree k v) 
singleton k v = pure (Node k v Nil Nil)

{-@ reflect set @-}
{-@ set :: Ord k => ts:BST k v-> k -> v -> 
            { t:Tick { ts':(BST k v) | size ts' == size ts + 1 || size ts' == size ts } | tcost t <= height ts  } @-}
set :: Ord k => Tree k v-> k -> v -> Tick (Tree k v)
set Nil k v  =  singleton k v
set (Node k v l r) k' v'
    | k' < k =  if tcost l' >0 
                    then waitN (tcost l')  (Node k v (tval l') r)
                    else wait (Node k v (tval l') r)
    | k' > k =  if tcost r' >0 
                    then waitN  (tcost r') (Node k v l (tval r'))
                    else wait (Node k v l (tval r'))
    | otherwise =  wait (Node k v' l r)
    where 
        l' = step 1 (set l k' v')
        r' = step 1 (set r k' v')

{-@ reflect set' @-}
{-@ set' :: Ord k => ts:BST k v-> k -> v -> 
            { t:Tick { ts':(BST k v) | size ts' == size ts + 1 || size ts' == size ts } | tcost t <= height ts  } @-}        
set' :: Ord k => Tree k v-> k -> v -> Tick (Tree k v)
set' Nil k v = singleton k v
set' (Node k v l r) k' v'
    | k' < k    = let Tick n l' = step 1 (set l k' v') in Tick n (Node k v l' r)
    | k' > k    = let Tick n r' = step 1 (set r k' v') in Tick n (Node k v l r')
    | otherwise = wait (Node k v' l r)

{-@ reflect get @-}
{-@ get :: (Ord k) =>  ts: BST k v -> k:k -> 
         { t:Tick (Maybe v) | tcost t <= height ts} @-}
get :: (Ord k) => Tree k v -> k -> Tick (Maybe v)           
get Nil _    = pure Nothing
get (Node k v l r) key
    | key < k    = step 1 (get l key)
    | key > k    = step 1 (get r key)
    | otherwise = pure (Just v)


-------------------------------------------------------------------------------
-- | Cost proofs:
-------------------------------------------------------------------------------

{-@ getCost :: (Ord k) => b:BST k v -> key:k
    -> { tcost (get b key) <= height b} 
    / [height b] @-}
getCost :: (Ord k) => Tree k v -> k -> Proof
getCost b@(Nil) k
   = tcost (get b k)
   ==. tcost (pure Nothing)
   ==. tcost (Tick 0 Nothing)
   ==. 0
   ==. height b
   *** QED
{-getCost b@(Node k v l r) k   
-}

-- | An example BST
{-@ reflect tree1 @-}
{-@ tree1 :: BST Int String @-}
tree1 :: (Tree Int String)
tree1 = tval ( set ( tval (set (tval (set Nil 10 "cat") ) 20 "dog") ) 30 "zebra")



{-@ test :: () -> TT  @-}
test :: () -> Bool 
test () =  tcost (get tree1 10) <= height tree1

       
-- | Another example BST  
{-@ reflect tree2 @-}
{-@ tree2 :: BST Int String @-}
tree2 :: (Tree Int String)
tree2 = tval ( set' ( tval (set' (tval (set' Nil 5 "siamese") ) 18 "bobtail") ) 3 "sphinx")

{-@ test2 :: () -> TT @-}
test2 :: () -> Bool
test2 () = tcost (set' tree2 40 "squirrel") <= height tree2
