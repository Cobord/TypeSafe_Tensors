module Architectures.Attention

import Data.Tensor
import Data.Para
import Architectures.Softargmax

parameters {a : Type} {auto _ : Num a}
  ||| Generalised form of attention
  public export
  crossAttention : {inputStructure, crossStructure, features : Cont} ->
    (allAppl : AllApplicative [inputStructure, features]) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
    (q, v : CTensor [inputStructure, features] a) ->
    (k : CTensor [crossStructure, features] a) ->
    CTensor [crossStructure, features] a
  crossAttention {allAlg = Cons} {allAppl = Cons} softargmax q v k =
    let attentionMatrix : CTensor [crossStructure, inputStructure] a
        attentionMatrix = softargmax <-$> (q `matrixMatrixProduct` k)
    in attentionMatrix `matMul` v


  ||| Self-attention is cross-attention where inputStructure = crossStructure
  public export
  selfAttention : {inputStructure, features : Cont} ->
    (allAppl : AllApplicative [inputStructure, features]) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
    (q, v, k : CTensor [inputStructure, features] a) ->
    CTensor [inputStructure, features] a
  selfAttention = crossAttention

  
  ||| Data structure for holding parameters of self-attention
  public export
  record CSelfAttentionParams (features : Cont) where
    constructor MkCSAParams
    queryMatParam : CTensor [features, features] a
    valueMatParam : CTensor [features, features] a
    keyMatParam : CTensor [features, features] a

  ||| Forward pass of self-attention, from input
  SAImpl : {inputStructure, features : Cont} ->
    (allAppl : AllApplicative [inputStructure, features]) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
    (input : CTensor [inputStructure, features] a) ->
    (params : CSelfAttentionParams features) ->
    CTensor [inputStructure, features] a
  SAImpl {allAppl = Cons} {allAlg = Cons} softargmax input (MkCSAParams queryMat valueMat keyMat)
    = let queries = queryMat `matrixMatrixProduct` input
          keys = keyMat `matrixMatrixProduct` input
          values = valueMat `matrixMatrixProduct` input
      in selfAttention softargmax queries values keys

  ||| Self-attention as a parametric map
  public export
  SelfAttention : {inputStructure, features : Cont} ->
    (allAppl : AllApplicative [inputStructure, features]) =>
    (allAlg : AllAlgebra [inputStructure, features] a) =>
    (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
    Para (CTensor [inputStructure, features] a)
         (CTensor [inputStructure, features] a)
  SelfAttention softargmax = MkPara
    (const (CSelfAttentionParams features))
    (SAImpl softargmax)

  SelfAttentionParams : (features : Nat) -> Type
  SelfAttentionParams features = CSelfAttentionParams (Vect features)