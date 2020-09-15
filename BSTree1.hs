module  BSTree (BSTree, size, height, insert, search, root) where

{-@ type Nat = {v:Int | 0 <= v} @-}

{-@ type NEBSTree a = {t: BSTree a | 0 < size t} @-}

{-@ data BSTree a = Nil 
                  | Node { x :: a
                         , l :: BSTree {v:a | v < x }  
                         , r :: BSTree {v:a | v > x } }
                         @-}
data BSTree a = Nil | Node a (BSTree a) (BSTree a) deriving Show

{-@ measure size @-}
{-@ size :: BSTree a -> Nat @-}
size :: BSTree a -> Int
size Nil = 0
size (Node x l r) = 1 + size l + size r
{-@ invariant {v:BSTree a | 0 <= size v} @-}

{-@  measure height @-}
{-@ height :: BSTree a -> Nat @-}
height :: BSTree a -> Int
height Nil = 0
height (Node x l r) = if (height l) > (height r) then (1 + height l) else (1 + height r)
{-@ invariant {v:BSTree a | 0 <= height v} @-}

{-@ insert :: Ord a => t:BSTree a -> x:a -> {t':BSTree a | size t' = size t || size t' = size t + 1} @-}
insert :: Ord a => BSTree a -> a -> BSTree a
insert Nil x = Node x Nil Nil
insert t@(Node y l r) x
    | x < y = (Node y (insert l x) r) 
    | x > y = (Node y l (insert r x))
    | x == y = t

{-@ search :: Ord a => BSTree a -> a -> Bool @-}
search :: Ord a => BSTree a -> a -> Bool
search Nil _ = False
search (Node y l r) x
    | x == y = True
    | x < y = search l x
    | x > y = search r x 


{-@ root :: NEBSTree a -> a @-} 
root :: BSTree a -> a 
root (Node x _ _) = x