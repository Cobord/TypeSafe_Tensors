module Architectures.Linear

import Data.Tensor
import Data.Para

public export
linearImplA : {x, y : ContA} -> Num a =>
  AllAlgebra [x] a =>
  TensorA [y, x] a -> TensorA [y] a -> TensorA [x] a -> TensorA [y] a
linearImplA weights bias input = matrixVectorProductA weights input + bias

linearImpl : {i, j : Nat} -> Num a =>
  Tensor [j, i] a -> Tensor [j] a -> Tensor [i] a -> Tensor [j] a
linearImpl weights bias input = ToCubicalTensor $ linearImplA
  (FromCubicalTensor weights)
  (FromCubicalTensor bias)
  (FromCubicalTensor input)

public export
linearParaA : {x, y : ContA} -> {a : Type} -> Num a =>
  AllAlgebra [x] a =>
  Para (TensorA [x] a) (TensorA [y] a)
linearParaA = MkPara
  (const (TensorA [y, x] a, TensorA [y] a))
  (\input, (weights, bias) => linearImplA weights bias input)

public export
linearPara : {i, j : Nat} -> {a : Type} -> Num a =>
  Para (Tensor [i] a) (Tensor [j] a)
linearPara = MkPara
  (const (Tensor [j, i] a, Tensor [j] a))
  (\input, (weights, bias) => linearImpl weights bias input)