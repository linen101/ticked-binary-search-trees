# Proving complexity properties of Binary Search Trees using Liquid Haskell

## A guide on how to type check the programs in my thesis
This contains instructions about how to type check the programs in my thesis. Every program is expected to type check without warnings.

### Tested on
`The Glorious Glasgow Haskell Compilation System, version 8.10.2
`

`LiquidHaskell Version 0.8.10.2
`
## Liquid Haskell
We use [LH as a GHC plugin](https://ucsd-progsys.github.io/liquidhaskell-blog/2020/08/20/lh-as-a-ghc-plugin.lhs/)

We compile the project with the LH plugin using 

either `cabal v2-build`

either `stack build`

## Binary Search Trees
We prove the cost of `set`, `get`, `delete` methods on BSTs in the module `BSTTick`

## Red-Black Trees
We prove the cost of `set`, `get` methods on Red-Black Trees and the theorem of logarithmic height in the module `RBTree`

We prove the cost of `delete` method on Red-Black Trees in the module `RBTdeletion`. 

`RBTdeletion` imports `RBTree`.

## Left-Leaning Red-Black Trees
We prove the cost of `set`, `get` methods on Red-Black Trees and the theorem of logarithmic height in the module `LLRBTree`. 

`LLRBTree` imports `RBTree`.

## Auxiliary functions
We verify properties on auxiliary functions

#### Log
We copy `Log2` module from [RTick](https://github.com/mathandley/RTick/blob/master/Log2.hs) to verify the logarithmic height property of Red-Black Trees and Left-Leaning Red-Black Trees.

#### Functions_Types
We include other auxiliary functions in `Functions_Types` module.
