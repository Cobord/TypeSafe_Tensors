module Tensor.CubicalTensor.TensorUtils

import Data.Vect 

import Data.Num
import Tensor.CubicalTensor.Tensor

public export
zeros : Num a => {shape : Vect n Nat} -> Tensor shape a
zeros = tensorReplicate zero

public export
ones : Num a => {shape : Vect n Nat} -> Tensor shape a
ones = tensorReplicate one

public export
flatten : Tensor shape a -> List a
flatten = foldr (::) []


public export
eye : Num a => {n : Nat} -> Tensor [n, n] a
eye = ?eye_rhs
