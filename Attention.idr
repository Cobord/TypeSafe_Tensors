module Attention

import ApplicativeLinAlg
import Tensor
import Tensor.Naperian
import Tree
import Rig

import Para.Para


-- We might not need Naperian
attention : {features, inputStructure : Type -> Type} -> {a : Type}
  -> (Applicative features, Applicative inputStructure, Naperian inputStructure, Naperian features, Rig a, Algebra inputStructure a, Algebra inputStructure (features a), Algebra features (inputStructure a))
  => (softmax : inputStructure a -> inputStructure a)
  -> (q : inputStructure (features a))
  -> (k : inputStructure (features a))
  -> (v : inputStructure (features a))
  -> inputStructure (features a)
attention softmax queries keys values =
  let attentionMatrix = transpose (queries `matMul` (transpose keys))
      attentionMatrixSoftmax = softmax <$> attentionMatrix
  in attentionMatrixSoftmax `matMul` values

record SelfAttentionParams (s, d : Type -> Type) (a : Type) where
  constructor MkSelfAttentionParams
  softmax : s a -> s a
  queryMat : d (d a)
  keyMat : d (d a)
  valueMat : d (d a)

ff : {s, d : Type -> Type} -> {a : Type}
  -> (Applicative d, Applicative s, Rig a, Algebra d a, Algebra s (d a), Algebra d (d a))
  => s (d a) -> SelfAttentionParams s d a -> s (d a)
ff input (MkSelfAttentionParams softmax queryMat keyMat valueMat)
  = attention softmax queries keys values where
    queries = input `matMul` queryMat
    keys = input `matMul` keyMat
    values = input `matMul` valueMat

SelfAttention : {s, d : Type -> Type} -> {a : Type}
  -> (Applicative d, Applicative s, Rig a, Algebra d a, Algebra s (d a)) 
  => Para (s (d a)) (s (d a))
SelfAttention {a} = MkPara (const (SelfAttentionParams s d a)) ff

