module Architectures.Attention

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Container.TreeUtils

import Tensor.ContainerTensor.Tensor
import Tensor.ContainerTensor.TensorUtils
-- import ApplicativeLinAlg
-- import Tensor.Tensor
-- import Tensor.TensorUtils
-- import Tensor.Naperian
import Data.Tree
import Data.Rig
import Para.Para
import Architectures.Softmax
import Algebra
import Misc

||| Generalised form of attention
public export
crossAttention : {inputStructure, crossStructure, features : Cont} ->
  Applicative (Ext inputStructure) => Applicative (Ext crossStructure) => Applicative (Ext features) =>
  {a : Type} -> Rig a =>
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
selfAttention : {inputStructure, features : Cont} ->
  {a : Type} -> Rig a =>
  Applicative (Ext inputStructure) => Applicative (Ext features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  (softmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  (q : Tensor [inputStructure, features] a) ->
  (k : Tensor [inputStructure, features] a) ->
  (v : Tensor [inputStructure, features] a) ->
  Tensor [inputStructure, features] a
selfAttention = crossAttention


rrr : {shape : ApplV conts} -> Num a => Rig (Tensor shape a)
rrr = %search

ffg : Rig a => AllAlgebra [] a
ffg = %search

-- Should follow from what?
-- ffgr : Num a => Algebra (Ext (VectCont 3)) (Tensor [] a)
-- ffgr = %search

-- ffgr' : Rig a => AllAlgebra [VectCont 3] a
-- ffgr' = %search -- ?ffgr'_rhs


fg : Rig a => AllAlgebra [VectCont 3, VectCont 4] a
fg = ?isearch

-- ||| Self-attention for cubical tensors
-- public export
-- selfAttention' : {inputSize, featureSize : Nat} ->
--   {a : Type} -> Rig a =>
--   (softmax : Tensor' [inputSize] a -> Tensor' [inputSize] a) ->
--   (q : Tensor' [inputSize, featureSize] a) ->
--   (k : Tensor' [inputSize, featureSize] a) ->
--   (v : Tensor' [inputSize, featureSize] a) ->
--   Tensor' [inputSize, featureSize] a
-- selfAttention' softmax (MkT q) (MkT k) (MkT v)
--   = MkT $ selfAttention ?ss ?qq ?kk ?vv


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
SAImpl : {inputStructure, features : Cont} -> {a : Type} -> Rig a =>
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

||| Self-attention as a parametric map
public export
SelfAttention : {inputStructure, features : Cont} -> {a : Type} -> Rig a =>
  Applicative (Ext inputStructure) => Applicative (Ext features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  (softmax : Tensor [inputStructure] a -> Tensor [inputStructure] a)
  -> Para (Tensor [inputStructure, features] a)
          (Tensor [inputStructure, features] a)
SelfAttention softmax = MkPara
  (const (SelfAttentionParams features a))
  (SAImpl softmax)


matParam : {d : Nat}
  -> SelfAttentionParams (VectCont d) Double
matParam = MkSAParams ones ones ones 


inputMatrix : Tensor' [4, 2] Double
inputMatrix = fromArray' [ [1, 3]
                         , [2, 8]
                         , [0, 0]
                         , [1, 3]]



-- Self Attention for matrices
SelfAttentionMat : {n, d : Nat}
  -> Para (Tensor' [n, d] Double) (Tensor' [n, d] Double)
SelfAttentionMat 
  -- This follows just from Algebra (Ext c) a, where a=Tensor shape a?
  -- And that requires Rig a on Tensor shape a?
  = let aab : Algebra (Ext (VectCont d)) Double
        aab = %search
        aal : Algebra (Ext (VectCont d)) (Tensor [] Double)
        aal = %search -- MkAlgebra ?uuearch
        -- bbl : Rig (Tensor [] Double)
        -- bbl = %search -- MkRig 0 1 (?pp ?mm
        t = SelfAttention {a=Double,inputStructure=VectCont n, features=VectCont d} softmax 
    in ?alall
-- SelfAttentionMat {n} {d} = SelfAttention {inputStructure=Vect n, features=Vect d} softmax

{-
matImpl : {n, d : Nat}
  -> (v : Vect n (Vect d Double))
  -> (p : Param SelfAttentionMat v)
  -> Vect n (Vect d Double)
matImpl = Run SelfAttentionMat
-}

tree1 : Tensor [BTreeLeafCont, VectCont 2] Double
tree1 = fromArray $ fromBTreeLeaf $ 
  Node' (Node' (Leaf (fromVect [1, 3])) (Leaf (fromVect [1, 3])))
        (Node' (Leaf (fromVect [100, 1000])) (Leaf (fromVect [1, 3])))

-- Self Attention for trees
SelfAttentionTree : {d : Nat} -> Para
  (Tensor [BTreeLeafCont, VectCont d] Double)
  (Tensor [BTreeLeafCont, VectCont d] Double)
SelfAttentionTree {d}
  = let y = SelfAttention -- {a=Double,inputStructure=BTreeLeafCont, features=VectCont d} -- (softmax {f=BTreeLeaf})
    in ?tuuu


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
