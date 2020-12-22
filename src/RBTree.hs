{-@ LIQUID "--no-termination" @-}

module RBTree where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (max,min)

data RBTree k v = Nil | Node Color k v !(RBTree k v) !(RBTree k v) deriving (Show)

data Color = B | R deriving (Eq,Show)


---------------------------------------------------------------------------
-- | Datatypes -------------------------------------------------------
---------------------------------------------------------------------------

{-@ data RBTree k v <l :: root:k -> x:k -> Bool, r :: root:k -> x:k -> Bool>
            = Nil
            | Node { tCol :: Color
                   , key  :: k
                   , val  :: v
                   , tl   :: RBTree <l, r> (k <l key>) v
                   , tr   :: RBTree <l, r> (k <r key>) v
                  }
  @-}

--   Ordered Red-Black Trees    --

{-@ type ORBT k v = RBTree <{\root v -> v < root }, {\root v -> v > root}> k v @-}

--   Red-Black Trees            --

{-@ type RBT k v    = {v: ORBT k v | isRB v && isBH v } @-}
{-@ type RBTN k v N = {v: RBT k v  | bh v = N }         @-}


--  Almost Red-Black Trees      --

{-@ type ARBT k v    = {v: ORBT k v | isARB v && isBH v} @-}
{-@ type ARBTN k v N = {v: ARBT k v | bh v = N }         @-}

-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

--  size invariant  --  

{-@ measure size @-}
{-@ size :: RBTree k v -> Nat @-}
size :: RBTree k v -> Int
size Nil             = 0
size (Node _ _ _ l r) = 1 + size l + size r
{-@ invariant {t:Tree k v | 0 <= size t} @-}

--  height invariant   --

{-@ measure height @-}
{-@ height :: RBTree k v -> Nat @-}
height :: RBTree k v -> Int
height Nil              = 0
height (Node _ _ _ l r) = 1 + max (height l) (height r)
{-@ invariant {t:Tree k v | 0 <= height t} @-}


--  check if root is black  --

{-@ measure isB @-}       
{-@ isB :: RBTree k v -> Bool @-}
isB (Nil)         = False               --True or False doesnt matter wtf
isB (Node c k v l r) = c == B

--  black height of tree  --
-- blackh only considers the left sub-tree, 
-- but this is legitimate, because isBH will ensure the
-- right subtree has the same blackh.

{-@ measure bh    @-}
{-@ bh :: RBTree k v -> Int @-}      -- here i had Nat - NOO 0 IS NOT NAT
bh :: RBTree k v -> Int
bh (Nil)         = 0
bh (Node c k v l r) = bh l + if (c == R) then 0 else 1
{-@ invariant {t:RBTree k v | 0 <= bh t} @-}


-- `black height invariant `--
{-@ measure isBH @-}
{-@ isBH :: RBTree k v -> Bool @-}
isBH :: RBTree k v -> Bool
isBH Nil = True
isBH (Node c _ _ l r) = bh l == bh r
                     && isBH l 
                     && isBH r

-- color of a Tree  --

{-@ measure col   @-}        
col :: RBTree k v -> Color
col (Node c k v l r)  = c
col (Nil)          = B

--      color Invariant      --
{-@ measure isRB   @-}
isRB :: RBTree k v -> Bool
isRB (Nil)         = True
isRB (Node c k v l r) = isRB l && isRB r && if c == R then (col l == B) && (col r == B) else True
{-@ invariant {t:RBTree k v | isRB t => isARB t } @-}
{-@ invariant {t:RBTree k v | isARB t && (col t == B) => isRB t} @-}

{-@ measure isARB  @-}    
isARB :: RBTree k v -> Bool
isARB (Nil)         = True
isARB (Node c k v l r) = isRB l && isRB r

{-@ predicate IsB T = not (col T == R) @-}


---------------------------------------------------------------------------
-- | Add an element -------------------------------------------------------
---------------------------------------------------------------------------

{-@ makeBlack :: ARBT k v -> RBT k v @-} --here
makeBlack :: RBTree k v -> RBTree k v
makeBlack Nil              = Nil
makeBlack (Node _ k v l r) = Node B k v l r

{-@ set :: (Ord k) => k -> v -> RBT k v -> RBT k v @-}
set :: Ord k => k -> v-> RBTree k v -> RBTree k v
set k v t = makeBlack (insert k v t)

{-@ insert :: (Ord k) => k -> v -> t:RBT k v -> {v: ARBTN k v {bh t} | (col t == B) => isRB v} @-} --here
insert k v Nil             = Node R k v Nil Nil
insert k v t@(Node B key val l r) 
    | k < key   = balanceL key val (insert k v l) r 
    | k > key   = balanceR key val l (insert k v r) 
    | otherwise = t
insert k v t@(Node R key val l r) 
    | k < key   = Node R key val (insert k v l) r
    | k > key   = Node R key val l (insert k v r)
    | otherwise = t


---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------


{-@ balanceL  :: k:k -> v -> l:ARBT {key:k | key < k} v -> RBTN {key:k | k < key} v {bh l} -> RBTN k v {1 + bh l} @-}
balanceL z zv (Node R y yv (Node R x xv a b) c) d = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceL z zv (Node R x xv a (Node R y yv b c)) d = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceL k v l r = Node B k v l r


{-@ balanceR  :: k:k -> v -> l:RBT {key:k | key < k} v -> ARBTN {key:k | k < key} v {bh l} -> RBTN k v {1 + bh l} @-}
balanceR x xv a (Node R y yv b (Node R z zv c d)) = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceR x xv a (Node R z zv (Node R y yv b c) d) = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceR x xv a b = Node B x xv a b

