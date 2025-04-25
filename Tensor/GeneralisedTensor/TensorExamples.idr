module Tensor.GeneralisedTensor.TensorExamples

import Data.Vect 

import Tensor.GeneralisedTensor.Tensor
import Algebra
import Tree
import Rig

%hide Builtin.infixr.(#)

----------------------------------------
--- Examples with cube-shaped tensors
----------------------------------------

-- They're named Tensor' instead of Tensor to always remind us that perhaps we can use a more general form of a tensor

t1 : Tensor' [3, 4] Double
t1 = fromGenArray $ [ [0, 1, 2, 3]
                    , [4, 5, 6, 7]
                    , [8, 9, 10, 11]]

t2 : Tensor' [2, 5] Double
t2 = fromGenArray $ [ [0, 1, 2, 3, 4]
                    , [5, 6, 7, 8, 9]]

-- Safe elementwise addition, t1 + t2 would not compile
tSum : Tensor' [3, 4] Double
tSum = t1 + t1

tMul : Tensor' [2, 5] Double
tMul = t2 * t2


negExample : Tensor' [3, 4] Double
negExample = negate t1

absExample : Tensor' [3, 4] Double
absExample = abs negExample


--- Indexing, slicing

-- Safe indexing, t1 @ [7, 5] would not compile
indexExample : Double
indexExample = t1 @@ [1, 2]

-- Safe slicing, takeTensor [10, 2] t1 would not compile
takeExample : Tensor' [2, 1] Double
takeExample = takeTensor [2, 1] t1



-- transposet1 : Tensor' [4, 3] Double
-- transposet1 = transposeMatrix t1

exampleStandardTensor : Tensor' [2, 3] Double
exampleStandardTensor = fromGenArray $ [ [1,2,3]
                                       , [4,5,6]]

----------------------------------------
--- Generalised tensor examples
----------------------------------------

ex1 : Tensor [# List, # Vect 2] Double
ex1 = fromGenArray $ [[1,2], [3,4], [5,6], [12, 14]]

ex2 : Tensor [# List, # BTreeLeaf] Double
ex2 = fromGenArray $ [ Node' (Leaf 3) (Leaf 4)
                     , Leaf 8
                     , Node' (Node' (Leaf 100) (Leaf 140)) (Leaf 17)]


ex3 : Tensor [# List, # BTreeLeaf] Double
ex3 = fromGenArray $ [ Leaf 1000 
                     , Leaf (-40)]


ex4 : Tensor [# List, # BTreeLeaf] Double
ex4 = ex2 + ex3


exTreeNode1 : Tensor [# List, # BTreeNode] Double
exTreeNode1 = fromGenArray $ [Leaf' 
                             , Node 3 (Node 4 Leaf' Leaf') Leaf' ]

exTreeNode2 : Tensor [# List, # BTreeNode] Double
exTreeNode2 = fromGenArray $ [Node 100 Leaf' Leaf']

exTreeNode3 : Tensor [# List, # BTreeNode] Double
exTreeNode3 = exTreeNode1 * exTreeNode2


listEx : Tensor [# List] Double
listEx = fromGenArray $ [1,4,5,2]

exDot : Tensor [] Double
exDot = dot listEx listEx

exDot2 : Tensor [] Double
exDot2 = dot exTreeNode2 exTreeNode2

exShow : String
exShow = show listEx


test : {f : Type -> Type} -> Applicative f => Tensor [# f, # f] Double
test = fromGenArray $ ?test_rhs
