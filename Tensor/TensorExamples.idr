module Tensor.TensorExamples

import Data.Fin
import Data.Vect

import Tensor.Tensor
---------------
--- Examples
---------------

t1 : Tensor [3, 4] Double
t1 = fromArray $ [ [0, 1, 2, 3]
                 , [4, 5, 6, 7]
                 , [8, 9, 10, 11]]

t2 : Tensor [2, 5] Double
t2 = fromArray $ [ [0, 1, 2, 3, 4]
                 , [5, 6, 7, 8, 9]]

tSum : Tensor [3, 4] Double
tSum = t1 + t1

indexExample : Double
indexExample = t1 @@ [1, 2]

takeExample : Tensor [1, 2] Double
takeExample = takeTensor [1, 2] t1


negExample : Tensor [3, 4] Double
negExample = negate t1

absExample : Tensor [3, 4] Double
absExample = abs negExample

