module Architectures.Linear

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Tensor.Tensor
import Data.Tensor.TensorUtils
import Para.Para
import Architectures.Softmax
import Algebra
import Misc


public export
linearImpl : {x, y : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext x) => Applicative (Ext y) => 
  AllAlgebra [x] a =>
  Tensor [y, x] a -> Tensor [y] a -> Tensor [x] a -> Tensor [y] a
linearImpl weights bias input = multiplyMV weights input + bias

linearImpl' : {i, j : Nat} -> {a : Type} -> Num a =>
  Tensor' [j, i] a -> Tensor' [j] a -> Tensor' [i] a -> Tensor' [j] a
linearImpl' = ?ghh -- linearImpl {x=VectCont i, y=VectCont j} {a}

linearImplTreeLeaf : {a : Type} -> Num a =>
  Tensor [BTreeLeafCont, BTreeLeafCont] a ->
  Tensor [BTreeLeafCont] a ->
  Tensor [BTreeLeafCont] a ->
  Tensor [BTreeLeafCont] a
linearImplTreeLeaf = linearImpl

public export
linearPara : {x, y : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext x) => Applicative (Ext y) => 
  AllAlgebra [x] a =>
  Para (Tensor [x] a) (Tensor [y] a)
linearPara = MkPara
  (const (Tensor [y, x] a, Tensor [y] a))
  (\input, (weights, bias) => linearImpl weights bias input)


-- linearPara' : {i, j : Nat} -> {a : Type} -> Num a =>
--   Para (Tensor' [i] a) (Tensor' [j] a)
-- linearPara' = ?ghh -- linearPara {x=VectCont i, y=VectCont j} {a}
