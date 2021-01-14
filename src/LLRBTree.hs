{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module LLRBTree where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min, log, fmap, (=<<))
import Log2
import RBTree(Color(..),RBTree(..), Maybe(..), height, size, isB, bh, rh, isBH, isRB, col, isARB, left, right)

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators

{-@ type LLRBT k v      = {t: RBT k v      | isLeftLean t}   @-}
{-@ type LLRBTN k v N   = {t: RBTN k v N   | isLeftLean t}   @-}
{-@ type LLARBT k v     = {t: ARBT k v     | isLeftLean t}   @-}
{-@ type LLARBTN k v N  = {t: ARBTN k v N  | isLeftLean t }  @-}
{-@ type BlackLLRBT k v = {t: LLRBT k v    | (bh t > 0 && IsB t)
                                            || isempty t} 
@-}

{-@ measure isLeftLean @-}
{-@ isLeftLean :: RBTree k v -> Bool @-}
isLeftLean :: RBTree k v -> Bool
isLeftLean Nil              = True
isLeftLean (Node c _ _ l r) = isLeftLean l && isLeftLean r
                           && (col r == B)


{-@ measure isempty @-}
isempty :: RBTree k v -> Bool
isempty Nil              = True
isempty (Node _ _ _ l r) = False

---------------------------------------------------------------------------
-- | Left Leaning Red-Black Trees -----------------------------------------
---------------------------------------------------------------------------

{-@ set' ::  (Ord k) => k -> v  
            -> t : LLRBT k v 
            -> {t' : Tick (BlackLLRBT k v) | tcost t' <= height t}
                    
@-}

set' k v s = fmap makeBlack' (insert' k v s)

{-@ makeBlack' :: LLARBT k v -> BlackLLRBT k v @-}
makeBlack' Nil              = Nil
makeBlack' (Node _ k v l r) = Node B k v l r



{-@ insert' ::   (Ord k) => k -> v 
                -> t : LLRBT k v 
                -> {ti : Tick {t' : (LLARBTN k v {bh t}) | IsB t => isRB t'} | tcost ti <= height t}
@-}
insert' :: Ord k => k -> v -> RBTree k v -> Tick (RBTree k v)
insert' k v Nil                    = pure (Node R k v Nil Nil)
insert' k v (Node col key val l r) = case compare k key of
    LT -> pure (\l' -> balanceL' col key val l' r) </> (insert' k v l)
    GT -> pure (\r' -> balanceR' col key val l r') </> (insert' k v r)
    EQ -> wait (Node col key v l r)



{-@ balanceL' :: c:Color -> k:k -> v 
                -> {l : LLARBT {key:k | key < k} v |  c == R => isRB l }
                -> {r : LLRBTN {key:k | k < key} v {bh l} | IsB r}
                -> {t : LLARBT k v | (if (c==B) then (bh t = bh l + 1) else (bh t = bh l))
                                   && ((c == B) => isRB t)}

@-}
balanceL' :: Color -> k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balanceL' _ z zv (Node R y yv (Node R x xv a b) c) d = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceL' col x xv a b                               = Node col x xv a b

{-@ balanceR' :: c:Color -> k:k -> v 
                -> {l : LLRBT {key:k | key < k} v | c == R =>  IsB l }
                -> {r : LLRBTN {key:k | k < key} v {bh l} |  c == R => isRB r  }
                -> {t : LLARBT k v | (if (c==B) then (bh t = bh l + 1) else (bh t = bh l))
                                   && ((c == B) => isRB t)}
@-}
balanceR' :: Color -> k -> v -> RBTree k v -> RBTree k v -> RBTree k v
balanceR' B y yv (Node R x xv a b) (Node R z zv c d) = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceR' col y yv x (Node R z zv c d)               = Node col z zv (Node R y yv x c) d 
balanceR' col x xv a b                               = Node col x xv a b  
-- 
-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Inva V = isRB V => isARB V            @-}
{-@ predicate Invb V = (isARB V && IsB V) => isRB V @-}
{-@ predicate Invc V = (isARB V && IsR V && IsB (left V) && IsB (right V)) => isRB V  @-}

{-@ using (RBTree k v) as {t: RBTree k v | Inva t && Invb t && Invc t } @-}
