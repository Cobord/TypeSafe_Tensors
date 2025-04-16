module Tensor.TensorUtils

import Data.Vect 

import Rig
import Tensor.Tensor

public export
zeros : Rig a => {shape : Vect n Nat} -> Tensor shape a
zeros = tensorReplicate zero

public export
ones : Rig a => {shape : Vect n Nat} -> Tensor shape a
ones = tensorReplicate one


