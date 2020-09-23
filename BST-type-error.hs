module BST1 where

import Measures (Tree (Nil,Node), size, height, searchTree)
import Prelude hiding (lookup)

{-@ die :: {v:String | false} -> a @-}
die msg = error msg


{-@ type BSTree = {t: Tree k v | searchTree t} @-}



