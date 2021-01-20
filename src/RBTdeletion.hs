{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module RBTdeletion where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min, log, fmap, (=<<))
import Log2
import RBTree(Color(..),RBTree(..), Maybe(..), height, size, isB, bh, rh, isBH, isRB, col, isARB, left, right, balanceL, balanceR)

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators

{-@ type ORBTN k v N = {v: ORBT k v  | bh v = N }         @-}


-- reduce the black height of the subtree c by reddening the node. 
-- This operation should only be called on BlackRBT. 
-- Here, c must be black because it is the child of a red node, 
-- and we know that c can't be Nil because it must have the same black height as (Node B y yv a b).


{-@ makeRed :: t  : BlackRBT k v
            -> {t' : ARBTN k v {bh t - 1} | size t' > 0} 
@-}
makeRed (Node B k v l r) = Node R k v l r 

-- 	Rebalancing function 
--  after a deletion from a left subtree 
--  of a black rooted tree
--  invariant bh t = bh l + 1

{-@ balL :: Ord k => k:k -> v 
         -> l : ARBT {key:k | key < k} v  
         -> r : RBTN {key:k | key > k} v {bh l+1}
         -> {t : ARBTN k v {bh l + 1} | IsB r => isRB t}
@-}
balL :: Ord k => k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balL y yv (Node R x xv a b) c                  = Node R y yv (Node B x xv a b) c
balL x xv bl (Node B y yv a b)                 = balanceR x xv bl (Node R y yv a b) 
balL x xv bl (Node R z zv (Node B y yv a b) c) = Node R y yv (Node B x xv bl a) (balanceR z zv b (makeRed c))

-- 	Rebalancing function 
--  after a deletion from a right subtree 
--  of a black rooted tree
--  invariant bh t = bh l

{-@ balR :: Ord k => k:k -> v 
         -> l : RBT {key:k | key < k} v  
         -> r : ARBTN {key:k | key > k} v {bh l - 1} 
         -> { t : ARBTN k v {bh l} | IsB l => isRB t } 
@-}
balR :: Ord k => k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balR x xv a (Node R y yv b c)                  = Node R x xv a (Node B y yv b c)
balR y yv (Node B x xv a b) bl                 = balanceL y yv (Node R x xv a b) bl
balR z zv (Node R x xv a (Node B y yv b c)) bl = Node R y yv (balanceL x xv (makeRed a) b) (Node B z zv c bl)


{-@ merge :: Ord k => k:k 
          -> l : RBT {key:k | key < k} v 
          -> r : RBTN {key:k | key > k} v {bh l} 
          -> {t : ARBTN k v {bh l} | IsB l && IsB r => isRB t}
@-}
merge :: Ord k => k -> RBTree k v -> RBTree k v -> RBTree k v
merge _ Nil x                               =  x
merge _ x Nil                               =  x
merge k (Node R x xv a b) (Node R y yv c d) = 
    case merge k b c of
        Node R z zv b' c'                   -> Node R z zv (Node R x xv a b') (Node R y yv c' d)
        bc                                  -> Node R x xv a (Node R y yv bc d)
merge k (Node B x xv a b) (Node B y yv c d) =
    case merge k b c of 
        Node R z zv b' c'                   -> Node R z zv (Node B x xv a b') (Node B y yv c' d)
        bc                                  -> balL x xv a (Node B y yv c d)
merge k a (Node R x xv b c)                 =  Node R x xv (merge k a b) c     -- IsB l && IsB r => isRB t
merge k (Node R x xv a b) c                 =  Node R x xv a (merge k b c)     -- IsB l && IsB r => isRB t   		


-- termination -> decreasing parameter height t

{-@ del :: Ord k => k 
           -> t : RBT k v 
           -> {t' : ARBT k v | (if (IsB t && size t>0) then bh t' = bh t - 1 else bh t' = bh t )
                            && (IsB t || isRB t') } 
           / [height t]
@-}
del :: Ord k => k -> RBTree k v -> RBTree k v
del k Nil                   = Nil
del k (Node col key v l r)  = 
    case compare k key of
        LT -> case l of
                Nil            -> Node R key v Nil r
                Node B _ _ _ _ -> balL key v (del k l) r
                _              -> Node R key v (del k l) r
        GT -> case r of
                Nil            -> Node R key v l Nil
                Node B _ _ _ _ -> balR key v l (del k r)
                _              -> Node R key v l (del k r)
        EQ                     -> merge k l r
      
-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------
{-@ predicate Inv1 V = (isARB V && IsB V) => isRB V @-}
{-@ predicate Inv2 V = isRB V => isARB V            @-}

{-@ using (Color) as {v: Color | v = R || v = B}           @-}
{-@ using (RBTree k v) as {v: RBTree k v | Inv1 v && Inv2 v}  @-}

