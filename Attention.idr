module Attention

import Data.Vect

import ApplicativeLinAlg
import Tensor
import Tensor.Naperian
import Tree
import Rig
import Para.Para

attention : {inputStructure, features : Type -> Type} -> {a : Type}
  -> (Applicative inputStructure, Applicative features, Rig a, Algebra features a, Algebra inputStructure (features a))
  => (softmax : inputStructure a -> inputStructure a)
  -> (q : inputStructure (features a))
  -> (k : inputStructure (features a))
  -> (v : inputStructure (features a))
  -> inputStructure (features a)
attention softmax queries keys values =
  let attentionMatrix = softmax <$> (queries `multiplyMMT` keys)
  in attentionMatrix `matMul` values

record SelfAttentionParams (inp, features : Type -> Type) (a : Type) where
  constructor MkSelfAttentionParams
  softmax : inp a -> inp a
  queryMat : features (features a)
  keyMat : features (features a)
  valueMat : features (features a)

SAImpl : {inputStructure, features : Type -> Type} -> {a : Type}
  -> (Applicative inputStructure, Applicative features, Rig a, Algebra features a, Algebra inputStructure (features a))
  => inputStructure (features a)
  -> SelfAttentionParams inputStructure features a
  -> inputStructure (features a)
SAImpl input (MkSelfAttentionParams softmax queryMat keyMat valueMat)
  = let queries = queryMat `multiplyMMT` input
        keys = keyMat `multiplyMMT` input
        values = valueMat `multiplyMMT` input
    in attention softmax queries keys values
  
SelfAttention : {s, d : Type -> Type} -> {a : Type}
  -> (Applicative d, Applicative s, Rig a, Algebra d a, Algebra s (d a)) 
  => Para (s (d a)) (s (d a))
SelfAttention {a} = MkPara (const (SelfAttentionParams s d a)) SAImpl


-- Self Attention for matrices
SelfAttentionMat : {n, d : Nat}
  -> Para (Vect n (Vect d Double)) (Vect n (Vect d Double))
SelfAttentionMat {n} {d} = SelfAttention {s=Vect n, d=Vect d}



-- Self Attention for trees
SelfAttentionTree : Para
  (BinTreeLeafOnly (BinTreeLeafOnly Double))
  (BinTreeLeafOnly (BinTreeLeafOnly Double))
SelfAttentionTree = SelfAttention {s=BinTreeLeafOnly, d=BinTreeLeafOnly}

