module Architectures.Affine

import Data.Tensor
import Data.Para

-- This is often called a 'linear layer', but really it is affine because of the bias

public export
record AffineLayerParams (x, y : Cont) (a : Type) where
  constructor MkParams
  weights : CTensor [y, x] a
  bias : CTensor [y] a

public export
affineImpl : {x, y : Cont} -> Num a =>
  AllAlgebra [x] a =>
  (allAppl : AllApplicative [x, y]) =>
  CTensor [x] a -> AffineLayerParams x y a -> CTensor [y] a
affineImpl {allAppl = Cons} input (MkParams weights bias)
  = matrixVectorProduct weights input + bias

public export
affinePara : {x, y : Cont} -> {a : Type} -> Num a =>
  AllAlgebra [x] a =>
  AllApplicative [x, y] =>
  CTensor [x] a -\-> CTensor [y] a
affinePara = MkPara
  (const (AffineLayerParams x y a))
  affineImpl