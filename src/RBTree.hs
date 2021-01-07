{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module RBTree where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min, log, fmap, (=<<))
import Log2

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators

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

--   Black rooted Red-Black Trees   --

{-@ type BlackRBT k v = {t: RBT k v | IsB t && bh t >0 } @-}


-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

--  size invariant  --  

{-@ measure size @-}
{-@ size :: RBTree k v -> Nat @-}
size :: RBTree k v -> Int
size Nil              = 0
size (Node _ _ _ l r) = 1 + size l + size r

--  height invariant   --

{-@ measure height @-}
{-@ height ::   t:RBTree k v 
                -> {u:Nat | isBH t => u <= rh t + bh t} 
@-}
height :: RBTree k v -> Int
height Nil              = 0
height (Node _ _ _ l r) = 1 + max (height l) (height r)

{-@ measure left   @-}
{-@ left :: {t:RBTree k v | size t >0 } -> RBTree k v @-}        
left :: RBTree k v -> RBTree k v
left (Node c k v l r) = l

{-@ measure right   @-}
{-@ right :: {t:RBTree k v | size t >0 } -> RBTree k v @-}        
right :: RBTree k v -> RBTree k v
right (Node c k v l r) = r


--  check if node is black  --

{-@ measure isB @-}       
{-@ isB :: RBTree k v -> Bool @-}
isB (Nil)            = True               --True or False doesnt matter wtf
isB (Node c k v l r) = c == B

--  black height of tree  --
-- blackh only considers the left sub-tree, 
-- but this is legitimate, because isBH will ensure the
-- right subtree has the same blackh.

{-@ measure bh    @-}
{-@ bh :: t : RBTree k v -> Nat @-}      
bh :: RBTree k v -> Int
bh (Nil)            = 0
bh (Node c k v l r) = bh l + if (c == R) then 0 else 1

{-@ measure rh    @-}
{-@ rh ::   t : RBTree k v -> Nat @-}      
rh :: RBTree k v -> Int
rh (Nil)            = 0
rh (Node c k v l r) = max (rh l) (rh r) + if (c == R) then 1 else 0


-- `black height invariant `--
{-@ measure isBH @-}
{-@ isBH :: RBTree k v -> Bool @-}
isBH :: RBTree k v -> Bool
isBH Nil              = True
isBH (Node c _ _ l r) = bh l == bh r
                     && isBH l 
                     && isBH r

-- color of a Tree  --

{-@ measure col   @-}        
col :: RBTree k v -> Color
col (Node c k v l r) = c
col (Nil)            = B

--      color Invariant      --
{-@ measure isRB   @-}
isRB :: RBTree k v -> Bool
isRB (Nil)            = True
isRB (Node c k v l r) = isRB l && isRB r 
                      && if c == R then (col l == B) && (col r == B) else True


{-@ measure isARB  @-}    
isARB :: RBTree k v -> Bool
isARB (Nil)            = True
isARB (Node c k v l r) = isRB l && isRB r

{-@ predicate IsB T = not (col T == R) @-}


---------------------------------------------------------------------------
-- | lookup for an element -------------------------------------------------------
---------------------------------------------------------------------------

{-@ reflect get @-}
{-@ get ::  Ord k => k:k 
            -> ts: RBT k v
            -> { t:Tick (Maybe v) | tcost t <= height ts } 
@-}
get :: Ord k => k -> RBTree k v -> Tick (Maybe v)
get _ Nil    = pure Nothing
get k' (Node c k v l r)
    | k' < k     = step 1 (get k' l)
    | k' > k     = step 1 (get k' r)
    | otherwise  = wait (Just v)

---------------------------------------------------------------------------
-- | Add an element -------------------------------------------------------
---------------------------------------------------------------------------

{-@ makeBlack :: RBT k v -> BlackRBT k v @-}
makeBlack Nil              = Nil
makeBlack (Node _ k v l r) = Node B k v l r

{-@ set ::  (Ord k) => k -> v  
            -> t : BlackRBT k v 
            -> { t' : Tick (BlackRBT k v) 
                    | tcost t' <= height t} 
@-}
set k v s = fmap makeBlack (insert k v s)

{-@ insert ::   (Ord k) => k -> v 
                -> t:BlackRBT k v 
                -> { t' : Tick (RBTN k v {bh t}) 
                        | tcost t' <= height t} 
@-}
insert k v Nil                    = wait (Node R k v Nil Nil)
insert k v s@(Node B key val l r) = case compare k key of
                              LT -> pure (\l' -> balanceL key val l' r) </> (insert k v l) 
                              GT -> pure (\r' -> balanceR key val l r') </> (insert k v r) 
                              EQ -> wait (Node B key v l r)
insert k v s@(Node R key val l r) = case compare k key of
                              LT -> pure (\l' -> Node R key val l' r) </> (insert k v l)
                              GT -> pure (\r' -> Node R key val l r') </> (insert k v r)
                              EQ -> wait (Node R key v l r)

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------


{-@ balanceL :: k:k -> v 
                -> l : ARBT {key:k | key < k} v 
                -> r : RBTN {key:k | k < key} v {bh l} 
                -> t : RBTN k v {1 + bh l} 
@-}
balanceL z zv (Node R y yv (Node R x xv a b) c) d =   ( Node R y yv (Node B x xv a b) (Node B z zv c d) )
balanceL z zv (Node R x xv a (Node R y yv b c)) d =   ( Node R y yv (Node B x xv a b) (Node B z zv c d) )
balanceL k v l r                                  =   (Node B k v l r)


{-@ balanceR :: k:k -> v 
                -> l : RBT {key:k | key < k} v 
                -> r : ARBTN {key:k | k < key} v {bh l} 
                -> t : RBTN k v {1 + bh l} 
@-}
balanceR x xv a (Node R y yv b (Node R z zv c d)) =  ( Node R y yv (Node B x xv a b) (Node B z zv c d) )
balanceR x xv a (Node R z zv (Node R y yv b c) d) =  ( Node R y yv (Node B x xv a b) (Node B z zv c d) )
balanceR x xv a b                                 =  (Node B x xv a b)

---------------------------------------------------------------------------
-- | Lemmas ---------------------------------------------------------------
---------------------------------------------------------------------------

-- prove that a a red-black tree
-- with n internal nodes can have 
-- a maximum height of 2lg(n+1). 

-- we must prove the following statements
-- 1. A subtree rooted at any tree x has at least 2^(bh x) -1 internal nodes
-- 2. Any tree x with (height x) has bh x >= (height x) /2

{-@ ple lemma1 @-}
{-@ lemma1
    :: Ord k
    => t:RBT k v
    -> { (twoToPower (bh t)) <= size t + 1 }
    / [size t]
@-}
lemma1 :: Ord k => RBTree k v -> Proof
lemma1 t@Nil
    =   size t + 1
    ==. 0 + 1
    ==. (twoToPower 0)
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
 

{-@ ple lemma1a @-}
{-@ lemma1a
    :: Ord k
    => {t:RBT k v | size t >0 }
    -> {l:RBT k v | l == left t}
    -> { 1 >= bh t - bh l }
@-}
lemma1a :: Ord k => RBTree k v -> RBTree k v -> Proof
lemma1a t@(Node c k v l' r) l | c == B
    = 1
    ==. 1 + bh t - bh t
    ==. 1 + bh t - (bh l + 1)
    ==. bh t - bh l
    >=. bh t - bh l
    *** QED

lemma1a t@(Node c k v l' r) l | c == R
    = 1
    ==. 1 + bh t - bh t
    ==. 1 + bh t - (bh l + 0)
    ==. bh t - bh l + 1
    >=. bh t - bh l
    *** QED

{-@ assume logTwotoPower :: x : Nat 
                            -> { log (twoToPower x) == x } 
@-}
logTwotoPower :: Int -> Proof
logTwotoPower _ = assumption

{-@ assume logComp ::   x:Int -> y: Int 
                        -> { x <= y => log x <= log y } 
@-}
logComp :: Int -> Int -> Proof
logComp _ _ = assumption

{-@ ple height_cost @-}
{-@ height_cost 
    :: Ord k
    => t : BlackRBT k v
    -> { height t <= 2 * log (size t + 1) } 
    / [height t]
@-}   
height_cost :: Ord k => RBTree k v -> Proof
height_cost t 
    =   height t
    <=. rh t + bh t
 --     ? toProof (heightRB t)
    <=. bh t + bh t
    ==. 2 * bh t
      ? toProof (logTwotoPower (bh t))
    ==. 2 * log (twoToPower (bh t)) 
      ? lemma1 t
      ? toProof (logComp (twoToPower (bh t)) (size t + 1))
    <=. 2 * log (size t + 1)  
    *** QED



-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Invs V = Inv1 V && Inv2 V && Inv3 V   @-}
{-@ predicate Inv1 V = (isARB V && IsB V) => isRB V @-}
{-@ predicate Inv2 V = isRB V => isARB V            @-}
{-@ predicate Inv3 V = 0 <= bh V                    @-}

{-@ using (Color) as {v: Color | v = R || v = B}           @-}
{-@ using (RBTree k v) as {v: RBTree k v | Invs v}  @-}
{-@ using (BlackRBT k v ) as {t : BlackRBT k v  | rh t <= bh t} @-}

