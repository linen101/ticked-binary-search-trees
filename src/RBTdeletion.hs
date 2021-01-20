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

{-@ makeBlackD :: t  : ARBT k v
               -> {t' : RBT k v | size t > 0 => IsBlackRBT t' }
@-}
makeBlackD Nil              = Nil
makeBlackD (Node _ k v l r) = Node B k v l r 


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


-- merge 2 trees 
-- with same bh

{-@ merge :: Ord k => k:k 
          -> l : RBT {key:k | key < k} v 
          -> r : RBTN {key:k | key > k} v {bh l}
          -> {ti : Tick {t : (ARBTN k v {bh l}) | IsB l && IsB r => isRB t} 
                 | tcost ti <= min (height l) (height r) }
@-}
merge :: Ord k => k -> RBTree k v -> RBTree k v -> Tick (RBTree k v)
merge _ Nil x                               =  pure x
merge _ x Nil                               =  pure x
merge k (Node R x xv a b) (Node R y yv c d) =  pure (\m -> mergeR m) </> (merge k b c)
    where
        mergeR (Node R z zv b' c')  = (Node R z zv (Node R x xv a b') (Node R y yv c' d))
        mergeR bc                   = (Node R x xv a (Node R y yv bc d))
merge k (Node B x xv a b) (Node B y yv c d) = pure (\m -> mergeB m) </> (merge k b c)
    where
        mergeB (Node R z zv b' c')  = (Node R z zv (Node B x xv a b') (Node B y yv c' d))
        mergeB bc                   = (balL x xv a (Node B y yv c d))
merge k a (Node R x xv b c)                 =  pure (\l' -> Node R x xv l' c) <*> (merge k a b)    -- IsB l && IsB r => isRB t
merge k (Node R x xv a b) c                 =  pure (\r' -> Node R x xv a r') <*> (merge k b c)     -- IsB l && IsB r => isRB t   		
    

{-@ delete :: Ord k => k 
                    -> t : BlackRBT k v 
                    -> {ti : Tick (RBT k v) 
                           | tcost ti <= height t}  
@-}
delete k t = fmap makeBlackD (del k t)

-- termination -> decreasing parameter height t

{-@ del :: Ord k => k 
           -> t : RBT k v 
           -> { ti : Tick {t' : (ARBT k v) | (if (IsB t && size t>0) then bh t' = bh t - 1 else bh t' = bh t ) 
                            && (not (IsB t) => isRB t') } 
                   | tcost ti <= height t }
           / [height t]
@-}
del :: Ord k => k -> RBTree k v -> Tick (RBTree k v)
del k Nil                   = pure Nil
del k (Node col key v l r)  = 
    case compare k key of
        LT -> case l of
                Nil            -> wait (Node R key v Nil r)
                Node B _ _ _ _ -> pure (\l' -> balL key v l' r) </> (del k l)
                _              -> pure (\l' -> Node R key v l' r) </> (del k l)
        GT -> case r of
                Nil            -> wait (Node R key v l Nil)
                Node B _ _ _ _ -> pure (\r' -> balR key v l r') </> (del k r)
                _              -> pure (\r' -> Node R key v l r') </> (del k r)
        EQ                     -> step 1 (merge k l r)
     
-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------
{-@ predicate Inv1 V = (isARB V && IsB V) => isRB V @-}
{-@ predicate Inv2 V = isRB V => isARB V            @-}
{-@ predicate IsBlackRBT T = bh T > 0 && IsB T @-}

{-@ using (Color) as {v: Color | v = R || v = B}           @-}
{-@ using (RBTree k v) as {v: RBTree k v | Inv1 v && Inv2 v}  @-}

