module Architectures.Linear

import Data.Tensor
import Para.Para

public export
linearImpl : {x, y : ContA} -> {a : Type} -> Num a =>
  AllAlgebra [x] a =>
  TensorA [y, x] a -> TensorA [y] a -> TensorA [x] a -> TensorA [y] a
linearImpl weights bias input = matrixVectorProductA weights input + bias

linearImpl' : {i, j : Nat} -> {a : Type} -> Num a =>
  Tensor [j, i] a -> Tensor [j] a -> Tensor [i] a -> Tensor [j] a
linearImpl' = ?ghh -- linearImpl {x=Vect i, y=Vect j} {a}

linearImplTreeLeaf : {a : Type} -> Num a =>
  TensorA [BTreeLeaf, BTreeLeaf] a ->
  TensorA [BTreeLeaf] a ->
  TensorA [BTreeLeaf] a ->
  TensorA [BTreeLeaf] a
linearImplTreeLeaf = linearImpl

public export
linearPara : {x, y : ContA} -> {a : Type} -> Num a =>
  AllAlgebra [x] a =>
  Para (TensorA [x] a) (TensorA [y] a)
linearPara = MkPara
  (const (TensorA [y, x] a, TensorA [y] a))
  (\input, (weights, bias) => linearImpl weights bias input)


-- linearPara' : {i, j : Nat} -> {a : Type} -> Num a =>
--   Para (Tensor [i] a) (Tensor [j] a)
-- linearPara' = ?ghh -- linearPara {x=Vect i, y=Vect j} {a}
