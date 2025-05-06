module Tensor.GeneralisedTensor.TensorExamples

import Data.Vect 

import Tensor.GeneralisedTensor.Tensor
import Algebra
import Tree
import Data.Num

%hide Builtin.infixr.(#)


----------------------------------------
--- Generalised tensor examples
----------------------------------------

ex1 : Tensor [# List, # Vect 2] Double
ex1 = fromGenArray $ [[1,2], [3,4], [5,6], [12, 14]]

-- Note that these can't be transposed! They're jagged, and List isn't Naperian, and neither is BTreeLeaf
ex2 : Tensor [# List, # BTreeLeaf] Double
ex2 = fromGenArray $ [ Node' (Leaf 3) (Leaf 4)
                     , Leaf 8
                     , Node' (Node' (Leaf 100) (Leaf 140)) (Leaf 17)]


ex3 : Tensor [# List, # BTreeLeaf] Double
ex3 = fromGenArray $ [ Leaf 1000 
                     , Leaf (-40)]


ex4 : Tensor [# List, # BTreeLeaf] Double
ex4 = ex2 + ex3


exBTreeNode1 : Tensor [# List, # BTreeNode] Double
exBTreeNode1 = fromGenArray $ [Leaf' 
                             , Node 3 (Node 4 Leaf' Leaf') Leaf' ]

exBTreeNode2 : Tensor [# List, # BTreeNode] Double
exBTreeNode2 = fromGenArray $ [Node 100 Leaf' Leaf']

exBTreeNode3 : Tensor [# List, # BTreeNode] Double
exBTreeNode3 = exBTreeNode1 * exBTreeNode2


listEx : Tensor [# List] Double
listEx = fromGenArray $ [1,4,5,2]

exDot : Tensor [] Double
exDot = dot listEx listEx

exDot2 : Tensor [] Double
exDot2 = dot exBTreeNode2 exBTreeNode2

exShow : String
exShow = show listEx