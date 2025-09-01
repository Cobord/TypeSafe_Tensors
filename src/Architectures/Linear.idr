module Architectures.Linear

import Data.Tensor
import Data.Para

public export
linearImpl : {x, y : Cont} -> Num a =>
  AllAlgebra [x] a =>
  (allAppl : AllApplicative [x, y]) =>
  CTensor [y, x] a -> CTensor [y] a -> CTensor [x] a -> CTensor [y] a
linearImpl {allAppl = Cons} weights bias input
  = matrixVectorProduct weights input + bias

public export
linearParaA : {x, y : Cont} -> {a : Type} -> Num a =>
  AllAlgebra [x] a =>
  AllApplicative [x, y] =>
  Para (CTensor [x] a) (CTensor [y] a)
linearParaA = MkPara
  (const (CTensor [y, x] a, CTensor [y] a))
  (\input, (weights, bias) => linearImpl weights bias input)