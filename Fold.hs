{-@ LIQUID "--reflection" @-}

module Fold (foldl) where

import Language.Haskell.Liquid.RTick
import Prelude hiding (foldl, pure, length)


{-@ measure length @-}
{-@ length :: [a] -> Nat @-}
length :: [a] -> Int
length []       = 0
length (_ : xs) = 1 + length xs

{-@ reflect foldl @-}
{-@ foldl :: (b -> a -> b) -> b -> xs:[a] -> {t: Tick b | tcost t == length xs} @-}
foldl f z []  = pure z
foldl f z (x : xs) = let w = f z x in 1 `step` foldl f w xs
