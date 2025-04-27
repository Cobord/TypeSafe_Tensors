module Tensor.ContainerTensor.TensorExamples

import Data.Vect
import Data.Fin

import Data.Container.Definition
import Data.Container.Instances

import Tensor.ContainerTensor.Tensor
import Algebra
import Data.Tree
import Rig

----------------------------------------
--- Examples with cube-shaped tensors
----------------------------------------
-- They're named Tensor' with a prime to remind us we can use
-- a more general, non-cubical tensor

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
tMul = (t2 * t2) <&> (+7)

-- Safe indexing, t1 @ [7, 5] would not compile
indexExample : Double
indexExample = t1 @@@ [1, 2]


negExample : Tensor' [3, 4] Double
negExample = negate t1

absExample : Tensor' [3, 4] Double
absExample = abs negExample


----------------------------------------
--- Generalised tensor examples
----------------------------------------

-- Some ergonomics here can be improved
t0gen : Tensor [VectCont 7] Double
t0gen = fromArray $ fromVectOld [1,2,3,4,5,6,7]


-- Dot product
tDot : Tensor [] Double
-- tDot = dot t0gen t0gen


ex2 : Tensor [TreeLeafCont] Double
ex2 = fromArray $ fromTreeLeaf $ Node' (Leaf 1) (Leaf 2)

ex3 : Tensor [TreeNodeCont] Double
ex3 = fromArray $ fromTreeNode $ Node 127 Leaf' Leaf'


ex4 : Tensor [VectCont 2, TreeNodeCont] Double
ex4 = fromArray $ ?hole -- fromTreeNode $ Node 127 Leaf' Leaf'