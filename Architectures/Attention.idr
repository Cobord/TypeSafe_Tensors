module Architectures.Attention

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Container.TreeUtils

import Tensor.ContainerTensor.Tensor
import Tensor.ContainerTensor.TensorUtils
import Data.Tree
import Para.Para
import Architectures.Softmax
import Algebra
import Misc

||| Generalised form of attention
public export
crossAttention : {inputStructure, crossStructure, features : Cont} ->
  Applicative (Ext inputStructure) => Applicative (Ext crossStructure) => Applicative (Ext features) =>
  {a : Type} -> Num a =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  (softmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  (q : Tensor [inputStructure, features] a) ->
  (k : Tensor [crossStructure, features] a) ->
  (v : Tensor [inputStructure, features] a) ->
  Tensor [crossStructure, features] a
crossAttention {allAlg = ((::) {allAlg=_})} softmax q k v =
  let attentionMatrix : Tensor [crossStructure, inputStructure] a
      attentionMatrix = softmax <-$-> (q `multiplyMMT` k)
  in attentionMatrix `matMul` v


||| Self-attention is cross-attention where inputStructure = crossStructure
public export
selfAttention : {inputStructure, features : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext inputStructure) => Applicative (Ext features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  (softmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  (q : Tensor [inputStructure, features] a) ->
  (k : Tensor [inputStructure, features] a) ->
  (v : Tensor [inputStructure, features] a) ->
  Tensor [inputStructure, features] a
selfAttention = crossAttention

||| Self-attention for cubical tensors
public export
selfAttention' : {inputSize, featureSize : Nat} ->
  {a : Type} -> Num a =>
  (softmax' : Tensor' [inputSize] a -> Tensor' [inputSize] a) ->
  (q : Tensor' [inputSize, featureSize] a) ->
  (k : Tensor' [inputSize, featureSize] a) ->
  (v : Tensor' [inputSize, featureSize] a) ->
  Tensor' [inputSize, featureSize] a
selfAttention' softmax' (MkT q) (MkT k) (MkT v)
  = MkT $ selfAttention (fromCubicalTensor . softmax' . toCubicalTensor) q k v


||| Data structure for holding parameters of self-attention
record SelfAttentionParams
  (features : Cont)
  {auto prf : Applicative (Ext features)}
  (a : Type) where
  constructor MkSAParams
  queryMatParam : Tensor [features, features] a
  keyMatParam : Tensor [features, features] a
  valueMatParam : Tensor [features, features] a

||| Forward pass of self-attention
SAImpl : {inputStructure, features : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext inputStructure) => Applicative (Ext features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  (softmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  (input : Tensor [inputStructure, features] a) ->
  (params : SelfAttentionParams features a) ->
  Tensor [inputStructure, features] a
SAImpl {allAlg = ((::) {allAlg=_})} softmax input (MkSAParams queryMat keyMat valueMat)
  = let queries = queryMat `multiplyMMT` input
        keys = keyMat `multiplyMMT` input
        values = valueMat `multiplyMMT` input
  in selfAttention softmax queries keys values

-- ||| Forward pass of self-attention for cubical tensors
-- SAImpl' : {inputSize, featureSize : Nat} -> {a : Type} -> Num a =>
--   (softmax : Tensor' [inputSize] a -> Tensor' [inputSize] a) ->
--   (input : Tensor' [inputSize, featureSize] a) ->
--   (params : SelfAttentionParams (VectCont featureSize) a) ->
--   Tensor' [inputSize, featureSize] a
-- SAImpl' softmax input (MkSAParams queryMat keyMat valueMat)
--   = let queries = queryMat `multiplyMMT` (GetT input)
--         keys = keyMat `multiplyMMT` (GetT input)
--         values = valueMat `multiplyMMT` (GetT input)
--   in selfAttention (fromCubicalTensor . softmax . toCubicalTensor) queries keys values

||| Self-attention as a parametric map
public export
SelfAttention : {inputStructure, features : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext inputStructure) => Applicative (Ext features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  (softmax : Tensor [inputStructure] a -> Tensor [inputStructure] a)
  -> Para (Tensor [inputStructure, features] a)
          (Tensor [inputStructure, features] a)
SelfAttention softmax = MkPara
  (const (SelfAttentionParams features a))
  (SAImpl softmax)


||| Self-attention for cubical tensors as a parametric map
public export
SelfAttention' : {inputSize, featureSize : Nat} -> {a : Type} -> Num a =>
  (softmax' : Tensor' [inputSize] a -> Tensor' [inputSize] a) ->
  Para (Tensor' [inputSize, featureSize] a)
       (Tensor' [inputSize, featureSize] a)
SelfAttention' softmax' = MkPara
  (const (SelfAttentionParams (VectCont featureSize) a))
  (\inp => toCubicalTensor . (SAImpl {features=VectCont featureSize} (fromCubicalTensor . softmax' . toCubicalTensor) (fromCubicalTensor inp)))


-- Self Attention for matrices
SelfAttentionMat : {n, d : Nat}
  -> Para (Tensor' [n, d] Double) (Tensor' [n, d] Double)
SelfAttentionMat = SelfAttention' softmax'

-- Self Attention for trees
SelfAttentionTree : {d : Nat} -> Para
  (Tensor [BTreeLeafCont, VectCont d] Double)
  (Tensor [BTreeLeafCont, VectCont d] Double)
SelfAttentionTree = SelfAttention softmaxBTreeLeaf


--------------------
-- Examples
--------------------
-- Will run self attention as usual, on matrices, and one on trees


||| Consume an input matrix, parameters, and produce the output of a self-attention layer
SAMatrixForwardPass : {n, d : Nat}
  -> (input : Tensor' [n, d] Double)
  -> (p : Param SelfAttentionMat input)
  -> Tensor' [n, d] Double
SAMatrixForwardPass = Run SelfAttentionMat


inputMatrix : Tensor' [4, 2] Double
inputMatrix = fromArray' [ [1, 3]
                         , [2, 8]
                         , [0, 0]
                         , [1, 3]]

||| Parameters for self-attention
||| Here just a matrix of ones
params : {d : Nat} -> SelfAttentionParams (VectCont d) Double
params = MkSAParams ones ones ones 

||| Example output for cubical self-attention
SAOutputMatrix : Tensor' [4, 2] Double
SAOutputMatrix = SAMatrixForwardPass inputMatrix params

||| Consume a tree of vectors of features, parameters, and produce the output of a self-attention layer
SATreeForwardPass : {d : Nat}
  -> (input : Tensor [BTreeLeafCont, VectCont d] Double)
  -> (p : Param SelfAttentionTree input)
  -> Tensor [BTreeLeafCont, VectCont d] Double
SATreeForwardPass = Run SelfAttentionTree


tree1 : Tensor [BTreeLeafCont, VectCont 2] Double
tree1 = fromArray $ fromBTreeLeaf $ 
  Node' (Node' (Leaf (fromVect [1, 3])) (Leaf (fromVect [1, 3])))
        (Node' (Leaf (fromVect [10, 4])) (Leaf (fromVect [1, 3])))

||| Example output for tree self-attention
SAOutputTree : Tensor [BTreeLeafCont, VectCont 2] Double
SAOutputTree = SATreeForwardPass tree1 params

{-


-- This is a left leaning tree of depth 3, where the content of each leaf is [1, 3]
{-
        .
   /      \
  [1,3]    .
          /  \
      [1,3]    . 
              / \
            [1,3] [1,3]

 -}
