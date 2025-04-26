module Tensor.ContainerTensor.TensorExamples

import Data.Vect
import Data.Fin

import Tensor.ContainerTensor.Tensor
import Algebra
import Tree
import Rig

{-
TODO:
1. fromArray
2. generalised indexing
 -}
-- TODO:

t0 : Tensor' [7] Double
t0 = fromArray' [1,2,3,4,5,6,7]


t1 : Tensor' [3, 4] Double
t1 = fromArray' $ [ [0, 1, 2, 3]
                  , [4, 5, 6, 7]
                  , [8, 9, 10, 11]]


t2 : Tensor' [2, 5] Double
t2 = fromArray' $ [ [0, 1, 2, 3, 4]
                  , [5, 6, 7, 8, 9]]


-- Safe elementwise addition, t1 + t2 would not compile
tSum : Tensor' [3, 4] Double
tSum = t1 + t1

tMul : Tensor' [2, 5] Double
tMul = t2 * t2