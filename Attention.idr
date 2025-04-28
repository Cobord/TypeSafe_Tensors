module Attention

import Data.Vect

import ApplicativeLinAlg
import Tensor.Tensor
import Tensor.TensorUtils
import Tensor.Naperian
import Tree
import Rig
import Para.Para
import Softmax
import Algebra


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

record SelfAttentionParams (features : Type -> Type) (a : Type) where
  constructor MkSelfAttentionParams
  queryMatParam : features (features a)
  keyMatParam : features (features a)
  valueMatParam : features (features a)

SAImpl : {inputStructure, features : Type -> Type} -> {a : Type}
  -> (Applicative inputStructure, Applicative features, Rig a, Algebra features a, Algebra inputStructure (features a))
  => (inputStructure a -> inputStructure a)
  -> inputStructure (features a)
  -> SelfAttentionParams features a
  -> inputStructure (features a)
SAImpl softmax input (MkSelfAttentionParams queryMat keyMat valueMat)
  = let queries = queryMat `multiplyMMT` input
        keys = keyMat `multiplyMMT` input
        values = valueMat `multiplyMMT` input
    in attention softmax queries keys values


||| Generalised Self Attention
SelfAttention : {inputStructure, features : Type -> Type} -> {a : Type}
  -> (Applicative inputStructure, Applicative features, Rig a, Algebra features a, Algebra inputStructure (features a)) 
  => (inputStructure a -> inputStructure a)
  -> Para (inputStructure (features a)) (inputStructure (features a))
SelfAttention {a} softmax = MkPara 
  (const (SelfAttentionParams features a))
  (SAImpl softmax)


-- Self Attention for matrices
SelfAttentionMat : {n, d : Nat}
  -> Para (Vect n (Vect d Double)) (Vect n (Vect d Double))
SelfAttentionMat {n} {d} = SelfAttention {inputStructure=Vect n, features=Vect d} softmax

matParam : {d : Nat}
  -> SelfAttentionParams (Vect d) Double
matParam = MkSelfAttentionParams
  (toArray (the (Tensor [d, d] Double) ones))
  (toArray (the (Tensor [d, d] Double) ones))
  (toArray (the (Tensor [d, d] Double) ones))

matImpl : {n, d : Nat}
  -> (v : Vect n (Vect d Double))
  -> (p : Param SelfAttentionMat v)
  -> Vect n (Vect d Double)
matImpl = Run SelfAttentionMat


-- Self Attention for trees
SelfAttentionTree : {d : Nat} -> Para
  (BTreeLeaf (Vect d Double))
  (BTreeLeaf (Vect d Double))
SelfAttentionTree {d} = SelfAttention {inputStructure=BTreeLeaf, features=Vect d} (softmax {f=BTreeLeaf})

matrix1 : Vect 4 (Vect 2 Double)
matrix1 = [ [1, 3], [1, 3], [1, 3] , [1, 3]]

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
tree1 : BTreeLeaf (Vect 2 Double)
tree1 = Node () (Node () (Leaf [1, 3]) (Leaf [1, 3])) (Node () (Leaf [1, 3]) (Leaf [1, 3]))
