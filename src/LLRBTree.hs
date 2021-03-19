{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}
{-@ LIQUID "--exact-data-con" @-}


module LLRBTree where

import Functions_Types (max, min, logComp, logTwotoPower, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min, log, fmap, (=<<))
import Log2
import RBTree(Color(..),RBTree(..), Maybe(..), height, size, isB, bh, rh, isBH, isRB, col, isARB)

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators

---------------------------------------------------------------------------
-- | Left Leaning Red-Black Trees -----------------------------------------
---------------------------------------------------------------------------

{-@ type LLRBT k v      = {t: RBT k v      | isLeftLean t}  @-}
{-@ type LLRBTN k v N   = {t: RBTN k v N   | isLeftLean t}  @-}
{-@ type LLARBT k v     = {t: ARBT k v     | isLeftLean t}  @-}
{-@ type LLARBTN k v N  = {t: ARBTN k v N  | isLeftLean t}  @-}
{-@ type BlackLLRBT k v = {t: BlackRBT k v | isLeftLean t}  @-}

{-@ measure isLeftLean @-}
{-@ isLeftLean :: RBTree k v -> Bool @-}
isLeftLean :: RBTree k v -> Bool
isLeftLean Nil              = True
isLeftLean (Node c _ _ l r) = isLeftLean l && isLeftLean r
                           && (col r == B)



---------------------------------------------------------------------------
-- | lookup for an element -------------------------------------------------------
---------------------------------------------------------------------------
{-@ reflect get' @-}
{-@ get' ::  Ord k => k:k 
            -> ts : LLRBT k v 
            -> { t:Tick (Maybe v) | tcost t <= height ts } 
@-}
get' :: Ord k => k -> RBTree k v -> Tick (Maybe v)
get' _ Nil    = pure Nothing
get' k' (Node c k v l r)
    | k' < k     = step 1 (get' k' l)
    | k' > k     = step 1 (get' k' r)
    | otherwise  = wait (Just v)


---------------------------------------------------------------------------
-- | Add an element -------------------------------------------------------
---------------------------------------------------------------------------
{-@ reflect makeBlack' @-}
{-@ makeBlack' :: {t : LLARBT k v | size t > 0} -> BlackLLRBT k v @-}
makeBlack' (Node _ k v l r) = Node B k v l r

{-@ reflect set' @-}
{-@ set' ::  (Ord k) => k -> v  
            -> t : LLRBT k v 
            -> {t' : Tick (BlackLLRBT k v) | tcost t' <= height t}
                    
@-}

set' k v s = fmap makeBlack' (insert' k v s)

{-@ reflect insert' @-}
{-@ insert' ::   (Ord k) => k -> v 
                -> t : LLRBT k v 
                -> {ti : Tick {t' : (LLARBTN k v {bh t}) | (IsB t => isRB t') && size t' > 0} 
                              | tcost ti <= height t}
@-}
insert' :: Ord k => k -> v -> RBTree k v -> Tick (RBTree k v)
insert' k v Nil                    = pure (Node R k v Nil Nil)
insert' k v (Node B key val l r) 
    | k < key   = pure (\l' -> balanceL' key val l' r) </> (insert' k v l)
    | k > key   = pure (\r' -> balanceR' B key val l r') </> (insert' k v r) 
    | otherwise = wait (Node B key v l r)
insert' k v (Node R key val l r) 
    | k < key   = pure (\l' -> Node R key val l' r) </> (insert' k v l)
    | k > key   = pure (\r' -> balanceR' R key val l r') </> (insert' k v r) 
    | otherwise = wait (Node R key v l r)

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------
{-@ reflect balanceL' @-}
{-@ balanceL' :: k:k -> v 
                -> {l : LLARBT {key:k | key < k} v |  size l >0 }
                -> {r : LLRBTN {key:k | k < key} v {bh l} | IsB r}
                -> {t : (LLRBTN k v {bh l+1}) | size t > 0}
@-}
balanceL' :: k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balanceL' z zv (Node R y yv (Node R x xv a b) c) d = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceL' x xv a b                                 = Node B x xv a b

{-@ reflect balanceR' @-}
{-@ balanceR' :: c:Color -> k:k -> v 
                -> {l : LLRBT {key:k | key < k} v | c == R =>  IsB l }
                -> {r : LLRBTN {key:k | k < key} v {bh l} |  (c == R => isRB r) && size r > 0 }
                -> {t : (LLARBT k v )| (if (c==B ) then (bh t = bh l + 1) else (bh t = bh l))
                                   && ((c == B) => isRB t)
                                   && size t > 0}
@-}
balanceR' :: Color -> k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balanceR' B y yv (Node R x xv a b) (Node R z zv c d) = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceR' col y yv x (Node R z zv c d)               = Node col z zv (Node R y yv x c) d
balanceR' col x xv a b                               = Node col x xv a b
-- 


---------------------------------------------------------------------------
-- | Lemmas ---------------------------------------------------------------
---------------------------------------------------------------------------

-- prove that a a ll red-black tree
-- with n internal nodes can have 
-- a maximum height of 2lg(n+1). 

-- we must prove the following statements
-- 1. A subtree rooted at any tree x has at least 2^(bh x) -1 internal nodes
-- 2. Any tree x with (height x) has bh x >= (height x) /2

{-@ ple lemma1 @-}
{-@ lemma1
    :: Ord k
    => t:LLRBT k v
    -> { (twoToPower (bh t)) <= size t + 1 }
    / [bh t]
@-}
lemma1 :: Ord k => RBTree k v -> Proof
lemma1 t@Nil
    =   twoToPower 0
    ==. 1
    ==. 0 + 1
    ==. size t + 1
    *** QED

lemma1 t@(Node R k v l r) 
    =   twoToPower (bh t)
    <=. 2*twoToPower (bh t)
    ==. 2*twoToPower (bh l)
    ==. twoToPower (bh l) + twoToPower (bh l)
    ==. twoToPower (bh l)  + twoToPower (bh r) 
        ? lemma1 l
        ? lemma1 r
    <=. size l + 1 + size r + 1    
    ==. size t + 1
    *** QED

lemma1 t@(Node B k v l r) 
    =   twoToPower (bh t)
    ==. 2*twoToPower (bh t - 1)
    ==. 2*twoToPower (bh l) 
    ==. twoToPower (bh l) + twoToPower (bh l)
    ==. twoToPower (bh l)  + twoToPower (bh r) 
        ? lemma1 l
        ? lemma1 r
    <=. size l + 1 + size r + 1    
    ==. size t + 1
    *** QED 



-------------------------------------------------------------------------------
-- Cost Proof -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ assume rh_bh :: t:BlackLLRBT k v-> { rh t <= bh t } @-}
rh_bh :: RBTree k v -> Proof
rh_bh _ = assumption


{-@ ple height_costUB @-}
{-@ height_costUB 
    :: Ord k
    => t : BlackLLRBT k v
    -> { height t <= 2 * log (size t + 1) } 
    / [height t]
@-}   
height_costUB :: Ord k => RBTree k v -> Proof
height_costUB t 
    =   height t
    <=. rh t + bh t
    --  ? toProof (rh_bh t)
    <=. bh t + bh t
    ==. 2 * bh t
      ? toProof (logTwotoPower (bh t))
    ==. 2 * log (twoToPower (bh t)) 
      ? lemma1 t
      ? toProof (logComp (twoToPower (bh t)) (size t + 1))
    <=. 2 * log (size t + 1)  
    *** QED

{-@ ple set'_costUB @-}
{-@ set'_costUB
    :: Ord k
    => k : k
    -> v:v
    -> t : BlackLLRBT k v 
    -> { tcost (set' k v t) <= 2 * log (size t + 1) } 
    / [height t]
@-} 
set'_costUB :: Ord k => k -> v -> RBTree k v -> Proof
set'_costUB k v t 
    =   tcost (set' k v t)
    <=. height t
      ? height_costUB t
    <=. 2 * log (size t + 1)  
    *** QED

{-@ ple get'_costUB @-}
{-@ get'_costUB
    :: Ord k
    => k : k
    -> t : BlackLLRBT k v 
    -> { tcost (get' k t) <= 2 * log (size t + 1) } 
    / [height t]
@-} 
get'_costUB :: Ord k => k -> RBTree k v -> Proof
get'_costUB k t 
    =   tcost (get' k t)
    <=. height t
      ? height_costUB t
    <=. 2 * log (size t + 1)  
    *** QED

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------


{-@ using (Color) as {v: Color | v = R || v = B}    @-}
{-@ using (RBTree k v) as {t: RBTree k v | Invs t } @-}
{-@ using (BlackLLRBT k v) as {t:BlackLLRBT k v | "mao"=="maow" } @-}
{-@ using (BlackLLRBT k v) as {t:BlackLLRBT k v | rh t <= bh t }  @-}
