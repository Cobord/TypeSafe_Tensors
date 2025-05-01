module Tensor.ContainerTensor.TensorExamples

import Data.Vect
import Data.Fin

import Data.Container.Definition
import Data.Container.Instances

import Tensor.ContainerTensor.Tensor
import Tensor.ContainerTensor.TensorUtils
-- import Tensor.ContainerTensor.NaperianTensor
import Algebra
import Data.Tree
import Data.Rig
import Softmax
import Misc



----------------------------------------
--- Examples with cube-shaped tensors
----------------------------------------
-- They're named Tensor' with a prime to remind us we can use
-- a more general, non-cubical tensor

||| Analogous to np.range, except the range is specified in the type
t0 : Tensor' [7] Double
t0 = range 

||| We can construct Tensors directly
t1 : Tensor' [3, 4] Double
t1 = fromArray' [ [0, 1, 2, 3]
                , [4, 5, 6, 7]
                , [8, 9, 10, 11]]


t2 : Tensor' [2, 5] Double
t2 = fromArray' [ [0, 1, 2, 3, 4]
                , [5, 6, 7, 8, 9]]



||| Safe elementwise addition
tSum : Tensor' [3, 4] Double
tSum = t1 + t1

failing
  ||| Can't add tensors of different shapes
  tSumFail : Tensor' [3, 4] Double
  tSumFail = t1 + t2

||| Safe indexing
indexExample : Double
indexExample = t1 @@@ [1, 2]

failing
   -- We cannot index outside of the tensor's shape
   indexExampleFail : Double
   indexExampleFail = t1 @@@ [7, 2]

-- Safe transposition
-- t1Transposed : Tensor' [4, 3] Double
-- t1Transposed = transposeMatrix t1

||| We can do all sorts of numeric operations
numericOps : Tensor' [2, 5] Double
numericOps = abs ((t2 * negate t2) <&> (+7))

----------------------------------------
--- Generalised tensor examples
----------------------------------------
-- These include tree shaped tensors, and other non-cubical ones


||| With "Tensor" we can do everything that we could do with "Tensor'"
t0again : Tensor [VectCont 7] Double
t0again = fromArray $ fromVect [1,2,3,4,5,6,7]

t1again : Tensor [VectCont 3, VectCont 4] Double
t1again = fromArray $ fromVect $ fromVect <$> [ [0, 1, 2, 3]
                                              , [4, 5, 6, 7]
                                              , [8, 9, 10, 11]]


||| Instead of having a vector with n elements, we can have a tree with leaves as elements.
ex1 : Tensor [BTreeLeafCont] Double
ex1 = fromArray $ fromBTreeLeaf $ Node' (Node' (Leaf (-42)) (Leaf 47)) (Leaf 2)

||| Or a tree with nodes as elements
ex2 : Tensor [BTreeNodeCont] Double
ex2 = fromArray $ fromBTreeNode $ Node 127 Leaf' (Node 14 Leaf' Leaf')
{- 
    127
  /     \
 *      14     
       / \
       *  * 
-}

||| Or elements themselves can be vectors!
ex3 : Tensor [BTreeLeafCont, VectCont 2] Double
ex3 = fromArray $ fromBTreeLeaf $ (Leaf $ fromVect [1,2])

||| We can index into those structures
indexTreeExample : Double
indexTreeExample = ex1 @@ [GoLLeaf (GoLLeaf AtLeaf)]


failing
  ||| And we'll get errors if we try to index outside of the structure
  indexTreeExampleFail : Double
  indexTreeExampleFail = ex1 @@ [GoRLeaf (GoLLeaf AtLeaf)]

-- Dot product
-- tDot : Tensor [] Double
-- tDot = dot t0again t0again


attention : {inputStructure, features : Cont} -> {a : Type} ->
  Fractional a => Rig a => Exp a =>
  Applicative (Ext inputStructure) => Applicative (Ext features) =>
  AllAlgebra [features] a =>
  AllAlgebra [inputStructure, features] a =>
  (softmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  (Tensor [inputStructure, features] a) ->
  (Tensor [inputStructure, features] a) ->
  (Tensor [inputStructure, features] a) ->
  Tensor [inputStructure, features] a
attention softmax q k v =
  let attentionMatrix : Tensor [inputStructure, inputStructure] a
      attentionMatrix = (q `multiplyMMT` k) -- missing softmax1
      sm = softmax
      -- sm' = softmax1 {s=inputStructure} {ss=[inputStructure]} {a=a}
  in ?holre -- attentionMatrix `matMul` v

-- We need to be able to apply softmax (the argument to attention) to attentionMatrix
-- That's what the tmfa function is for
