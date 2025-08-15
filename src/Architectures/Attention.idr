module Architectures.Attention

import Data.Tensor
import Architectures.Softmax
import Data.Para

parameters {a : Type} {auto _ : Num a}
  ||| Generalised form of attention
  public export
  crossAttentionA : {crossStructure : ContA} ->
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a) ->
    (q, v : TensorA [inputStructure, features] a) ->
    (k : TensorA [crossStructure, features] a) ->
    TensorA [crossStructure, features] a
  crossAttentionA {allAlg = ((::) {allAlg=_})} softmax q v k =
    let attentionMatrix : TensorA [crossStructure, inputStructure] a
        attentionMatrix = softmax <-$-> (q `matrixMatrixProductA` k)
    in attentionMatrix `matMulA` v
  
  ||| Self-attention is cross-attention where inputStructure = crossStructure
  public export
  selfAttentionA : {inputStructure, features : ContA} ->
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a) ->
    (q, v, k : TensorA [inputStructure, features] a) ->
    TensorA [inputStructure, features] a
  selfAttentionA = crossAttentionA

  ||| Data structure for holding parameters of self-attention
  public export
  record SelfAttentionParamsA (features : ContA) where
    constructor MkSAParamsA
    queryMatParam : TensorA [features, features] a
    valueMatParam : TensorA [features, features] a
    keyMatParam : TensorA [features, features] a

  ||| Forward pass of self-attention, from input
  SAImplA : (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a) ->
    (input : TensorA [inputStructure, features] a) ->
    (params : SelfAttentionParamsA features) ->
    TensorA [inputStructure, features] a
  SAImplA {allAlg = ((::) {allAlg=_})} softmax input (MkSAParamsA queryMat valueMat keyMat)
    = let queries = queryMat `matrixMatrixProductA` input
          keys = keyMat `matrixMatrixProductA` input
          values = valueMat `matrixMatrixProductA` input
      in selfAttentionA softmax queries values keys

  ||| Self-attention as a parametric map
  public export
  SelfAttentionA : {features : ContA} ->
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softmax : TensorA [inputStructure] a -> TensorA [inputStructure] a) ->
    Para (TensorA [inputStructure, features] a)
         (TensorA [inputStructure, features] a)
  SelfAttentionA softmax = MkPara
    (const (SelfAttentionParamsA features))
    (SAImplA softmax)

  ||| Self-attention for cubical tensors
  namespace CubicalAttention
    public export
    selfAttention : {inputSize, featureSize : Nat} ->
      (softmax' : Tensor [inputSize] a -> Tensor [inputSize] a) ->
      (q, v, k : Tensor [inputSize, featureSize] a) ->
      Tensor [inputSize, featureSize] a
    selfAttention softmax q v k
      = ToCubicalTensor $ selfAttentionA (FromCubicalTensorMap softmax)
         (FromCubicalTensor q)
         (FromCubicalTensor v)
         (FromCubicalTensor k)

    ||| Cubical variant of SelfAttentionParamsA
    public export
    record SelfAttentionParams (features : Nat) where
      constructor MkSAParams
      queryMatParam : Tensor [features, features] a
      valueMatParam : Tensor [features, features] a
      keyMatParam : Tensor [features, features] a

    public export
    ToCubicalParams : {features : Nat} ->
      SelfAttentionParamsA (Vect features) -> SelfAttentionParams features
    ToCubicalParams (MkSAParamsA queryMatParam valueMatParam keyMatParam)
      = MkSAParams (ToCubicalTensor queryMatParam)
                   (ToCubicalTensor valueMatParam)
                   (ToCubicalTensor keyMatParam)

    public export
    FromCubicalParams : {features : Nat} ->
      SelfAttentionParams features -> SelfAttentionParamsA (Vect features)
    FromCubicalParams (MkSAParams queryMatParam valueMatParam keyMatParam)
      = MkSAParamsA (FromCubicalTensor queryMatParam)
                    (FromCubicalTensor valueMatParam)
                    (FromCubicalTensor keyMatParam)

    public export
    SAImpl : {inputStructure, features : Nat} ->
      (sm : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
      (input : Tensor [inputStructure, features] a) ->
      (params : SelfAttentionParams features) ->
      Tensor [inputStructure, features] a
    SAImpl sm input params = ToCubicalTensor $ SAImplA
      (FromCubicalTensorMap sm)
      (FromCubicalTensor input)
      (FromCubicalParams params)

    ||| Self-attention for cubical tensors as a parametric map
    public export
    SelfAttention : {inputSize, featureSize : Nat} ->
      (sm : Tensor [inputSize] a -> Tensor [inputSize] a) ->
      Para (Tensor [inputSize, featureSize] a)
           (Tensor [inputSize, featureSize] a)
    SelfAttention sm = MkPara
      (const (SelfAttentionParams featureSize))
      (SAImpl sm) 


--------------------
-- Examples
--------------------
-- Will run self attention as usual, on matrices, and one on trees

-- Self Attention for matrices
SelfAttentionMat : {n, d : Nat}
  -> Para (Tensor [n, d] Double) (Tensor [n, d] Double)
SelfAttentionMat = SelfAttention softmax

-- Self Attention for trees
SelfAttentionTree : {d : Nat} -> Para
  (TensorA [BinTreeLeaf, Vect d] Double)
  (TensorA [BinTreeLeaf, Vect d] Double)
SelfAttentionTree = SelfAttentionA softmaxBinTreeLeaf


inputMatrix : Tensor [4, 2] Double
inputMatrix = fromConcrete [ [1, 3]
                           , [2, 8]
                           , [0, 0]
                           , [1, 3]]

||| Parameters for self-attention
||| Here just a matrix of ones
params : {d : Nat} -> SelfAttentionParamsA (Vect d) {a=Double}
params = MkSAParamsA onesA onesA onesA

||| Example output for cubical self-attention
SAOutputMatrix : Tensor [4, 2] Double
SAOutputMatrix = (Run SelfAttentionMat) inputMatrix (ToCubicalParams params)

tree1 : TensorA [BinTreeLeaf, Vect 2] Double
tree1 = fromConcreteA $ Node' (Leaf [4, 5]) (Leaf [-12, 25])

||| Example output for tree self-attention
SAOutputTree : TensorA [BinTreeLeaf, Vect 2] Double
SAOutputTree = (Run SelfAttentionTree) tree1 params