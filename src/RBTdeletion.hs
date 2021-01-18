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

{-@ balL :: k:k -> v 
         -> l : ARBT {key:k | key < k} v  
         -> {r : RBTN {key:k | key > k} v {bh l + 1} | IsR l => IsB r } 
         -> {t : ARBTN k v {bh l + 1} | isB r => isRB t } 
@-}
balL :: k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balL y yv (Node R x xv a b) c                  = Node R y yv (Node B x xv a b) c
balL x xv bl (Node B y yv a b)                 = balanceR x xv bl (Node R y yv a b) 
balL x xv bl (Node R z zv (Node B y yv a b) c) = Node R y yv (Node B x xv bl a) (balanceR z zv b (makeRed c))

-- 	Rebalancing function 
--  after a deletion from a right subtree 
--  of a black rooted tree
--  invariant bh t = bh l

{-@ balR :: k:k -> v 
         -> l : RBT {key:k | key < k} v  
         -> r : ARBTN {key:k | key > k} v {bh l - 1} 
         -> { t : ARBTN k v {bh l} | IsB l => isRB t } 
@-}
balR :: k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balR x xv a (Node R y yv b c)                  = Node R x xv a (Node B y yv b c)
balR y yv (Node B x xv a b) bl                 = balanceL y yv (Node R x xv a b) bl
balR z zv (Node R x xv a (Node B y yv b c)) bl = Node R y yv (balanceL x xv (makeRed a) b) (Node B z zv c bl)

{-@ merge :: RBTree k v -> RBTree k v -> RBTree k v @-}
merge :: RBTree k v -> RBTree k v -> RBTree k v
merge Nil x                               = x
merge x Nil                               = x
merge (Node R x xv a b) (Node R y yv c d) = 
	case merge b c of
		Node R z zv b' c' -> Node R (Node R x xv a b') (Node R y yv c' d)

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------
{-@ predicate Inv1 V = (isARB V && IsB V) => isRB V @-}
{-@ predicate Inv2 V = isRB V => isARB V            @-}

{-@ using (Color) as {v: Color | v = R || v = B}           @-}
{-@ using (RBTree k v) as {v: RBTree k v | Inv1 v && Inv2 v}  @-}