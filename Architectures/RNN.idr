module Architectures.RNN

import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Tensor.ContainerTensor.Tensor
import Tensor.ContainerTensor.TensorUtils
import Data.Rig


fn : {n : Nat}
  -> Vect n x -> state -> (Vect n y, state)


