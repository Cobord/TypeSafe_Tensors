module Attention

import Data.Tensor
import Data.Para

import Architectures.Attention
import Architectures.Softargmax

{-------------------------------------------------------------------------------
Attention example

Will run self attention as usual, on matrices, and then on trees
-------------------------------------------------------------------------------}

||| We'll first instantiate self attention as a parametric map on matrices
||| `n` here represents the length of sequence
||| `d` here represents the dimension of the features
SelfAttentionMat : {n, d : Nat}
  -> Para (Tensor [n, d] Double) (Tensor [n, d] Double)
SelfAttentionMat = SelfAttention softargmax


||| Let's choose a simple input matrix
inputMatrix : Tensor [3, 2] Double
inputMatrix = fromConcreteTy [ [1, 3]
                             , [2, -3]
                             , [0, 0.3]]

||| Let's choose a query, value and key matrices:
||| a matrix of ones, a triangular matrix, and a matrix of threes, respectively
params : {d : Nat} -> CSelfAttentionParams (Vect d) {a=Double}
params = MkCSAParams ones tri (ones <&> (*3))

||| Now we can run self attention on the matrix
||| This value can be inspected in REPL, or otherwise
outputMatrix : Tensor [3, 2] Double
outputMatrix = Run SelfAttentionMat inputMatrix params


||| Now we'll instantiate self attention as a parametric map on trees and use
||| container tensors for this. Here we'll study attention where the input
||| structure isn't a sequence, but a tree, but we'll keep the feature structure
||| as a sequence
||| That is, instead of `Tensor [n, d] Double`
||| we'll have `CTensor [BinTreeLeaf, Vect d] Double`
SelfAttentionTree : {d : Nat} -> Para
  (CTensor [BinTreeLeaf, Vect d] Double)
  (CTensor [BinTreeLeaf, Vect d] Double)
SelfAttentionTree = SelfAttention softargmax

||| We choose a simple input tree
||| Notably, the set of parameters can be the same as the one for matrices
inputTree : CTensor [BinTreeLeaf, Vect 2] Double
inputTree = fromConcreteTy $
  Node' (Node' (Leaf [1, -1])
               (Leaf [0.5, 1.2]))
        (Leaf [-0.3, 1.2])

||| We can run sefl attention on the tree, and inspect the result
outputTree : CTensor [BinTreeLeaf, Vect 2] Double
outputTree = Run SelfAttentionTree inputTree params