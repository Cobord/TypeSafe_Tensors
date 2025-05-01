module Tensor.CubicalTensor.TensorUtils

import Data.Vect 

import Data.Rig
import Tensor.CubicalTensor.Tensor

public export
zeros : Rig a => {shape : Vect n Nat} -> Tensor shape a
zeros = tensorReplicate zero

public export
ones : Rig a => {shape : Vect n Nat} -> Tensor shape a
ones = tensorReplicate one

public export
flatten : Tensor shape a -> List a
flatten = foldr (::) []


public export
eye : Rig a => {n : Nat} -> Tensor [n, n] a
eye = ?eye_rhs
