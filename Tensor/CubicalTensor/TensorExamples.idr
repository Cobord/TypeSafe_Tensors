module Tensor.CubicalTensor.TensorExamples

import Data.Fin
import Data.Vect

import Tensor.CubicalTensor.Tensor
import Tensor.Naperian
---------------
--- Examples
---------------

t0 : Tensor [7] Double
t0 = fromArray [1,2,3,4,5,6,7]


t1 : Tensor [3, 4] Double
t1 = fromArray $ [ [0, 1, 2, 3]
                 , [4, 5, 6, 7]
                 , [8, 9, 10, 11]]


t2 : Tensor [2, 5] Double
t2 = fromArray $ [ [0, 1, 2, 3, 4]
                 , [5, 6, 7, 8, 9]]

-- Safe elementwise addition, t1 + t2 would not compile
tSum : Tensor [3, 4] Double
tSum = t1 + t1

tMul : Tensor [2, 5] Double
tMul = t2 * t2

negExample : Tensor [3, 4] Double
negExample = negate t1

absExample : Tensor [3, 4] Double
absExample = abs negExample

transposet1 : Tensor [4, 3] Double
transposet1 = transposeMatrix t1

-- Safe indexing, t1 @ [7, 5] would not compile
indexExample : Double
indexExample = t1 @@ [1, 2]

-- Safe slicing, takeTensor [10, 2] t1 would not compile
takeExample : Tensor [2, 1] Double
takeExample = takeTensor [2, 1] t1

