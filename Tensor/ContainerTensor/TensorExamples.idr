module Tensor.ContainerTensor.TensorExamples

import Data.Vect
import Data.Fin

import Tensor.ContainerTensor.Tensor
import Algebra
import Tree
import Rig

t1 : Tensor' [3, 4] Double
t1 = ?hole

-- t1 = fromGenArray $ [ [0, 1, 2, 3]
--                     , [4, 5, 6, 7]
--                     , [8, 9, 10, 11]]