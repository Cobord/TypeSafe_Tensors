module Architectures.Linear

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Tensor.ContainerTensor.Tensor
import Tensor.ContainerTensor.TensorUtils
import Data.Rig
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

linearPara : {x, y : Cont} -> {a : Type} -> Num a =>
  Applicative (Ext x) => Applicative (Ext y) => 
  AllAlgebra [x] a =>
  Para (Tensor [x] a) (Tensor [y] a)
linearPara = MkPara
  (const (Tensor [y, x] a, Tensor [y] a))
  (\input, (weights, bias) => linearImpl weights bias input)