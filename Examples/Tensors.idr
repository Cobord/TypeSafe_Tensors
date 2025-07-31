module Examples.Tensors

import Data.Tensor
import Data.Tensor.Utils
-- import Data.Tensor.NaperianTensor

{-
Need to compute stride-based functionality for:
 * Slice
 * Take
 * Transpose
 * Show

Need to fix automatic flattening for TensorA for contraction operations
 -}

----------------------------------------
-- Examples of standard, cubical tensors
----------------------------------------

||| We can construct Tensors directly
t0 : Tensor [3, 4] Double
t0 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

||| Or using analogous functions to np.arange and np.reshape
t1 : Tensor [6] Double
t1 = range

t2 : Tensor [2, 3] Double
t2 = reshape t1

failing
  ||| Which will fail if we supply an array with the wrong shape
  t1Fail : Tensor [3, 4] Double
  t1Fail = fromArray [ [0, 1, 2, 3, 999]
                     , [4, 5, 6, 7]
                     , [8, 9, 10, 11]]

failing
  ||| Or if the reshape is not possible
  t2Fail : Tensor [7, 2] Double
  t2Fail = reshape t1

||| We can perform safe elementwise addition
t0Sum : Tensor [3, 4] Double
t0Sum = t0 + t0

||| And all sorts of numeric operations
numericOps : Tensor [3, 4] Double
numericOps = abs ((t0 * negate t0) <&> (+7))

dotProduct : Tensor [] Double
dotProduct = dot t1 t1

failing
  ||| Failing if we add tensors of different shapes
  tSumFail : Tensor [3, 4] Double
  tSumFail = t1 + t2

failing
  ||| Or if types mismatch in contractions
  dotProductFail : Tensor [] Double
  dotProductFail = dot t1 (range {n=7})


||| We can safely index into tensors
indexExample : Double
indexExample = t0 @@ [1, 2]

failing
   ||| And fail if we index outside of the tensor's shape
   indexExampleFail : Double
   indexExampleFail = t1 @@ [7, 2]

-- ||| Safe transposition
-- t1Transposed : Tensor [4, 3] Double
-- t1Transposed = transposeMatrix t1


-- ||| Safe slicing, takeTensor [10, 2] t1 would not compile
-- takeExample : Tensor [2, 1] Double
-- takeExample = takeTensor [2, 1] t1

failing
  takeExampleFail : Tensor [10, 2] Double
  takeExampleFail = takeTensor [10, 2] t1



----------------------------------------
-- Generalised tensor examples
-- These include list, tree shaped tensors, and other non-cubical tensors
----------------------------------------

||| TensorA can do everything that Tensor can
t0Again : TensorA [Vect 3, Vect 4] Double
t0Again = fromArrayA $ [ [0, 1, 2, 3]
                       , [4, 5, 6, 7]
                       , [8, 9, 10, 11]]

||| Including converting from Tensor
t1again : TensorA [Vect 6] Double
t1again = FromCubicalTensor t1


||| Above, the container Vect was being made explicit because
||| there are other containers we can use
||| For instance, we can use List, which allows us to store
||| an arbitrary number of elements
exList : TensorA [List] Double
exList = fromArrayA [1,2,3,4,5,6,7,8]

exList2 : TensorA [List] Double
exList2 = fromArrayA [100,-200,1000]

{- 
We can use BTreeLeaf, allowing us to store a tree-shaped 'vector'
which has elements on its leaves
        *
      /   \
     *     2 
    / \
(-42)  46 
-}
exTree1 : TensorA [BTreeLeaf] Double
exTree1 = fromArrayA $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)



{- 
Here's another tree of the same shape, with a different number of elements
        *
      /   \
     10   100 
-}
exTree2 : TensorA [BTreeLeaf] Double
exTree2 = fromArrayA $ Node' (Leaf 10) (Leaf 100)

||| We can take the dot product of these two trees
||| The fact that they don't have the same number of elements does not matter
||| What matters is that the container defining them 'BTreeLeaf' is the same
dotProduct2 : TensorA [] Double
dotProduct2 = dotA exTree1 exTree2

{- 
Here's a tree-vector with nodes as elements
   200
  /   \
 10   3000
 /\   / \
*  * *   * 
-}
ex3 : TensorA [BTreeNode] Double
ex3 = fromArrayA $ Node 200 (Node 10 Leaf' Leaf') (Node 3000 Leaf' Leaf')

||| And here's a tree with whose nodes are vectors of size 2
ex4 : TensorA [BTreeLeaf, Vect 2] Double
ex4 = fromArrayA $ Node' (Leaf [4,1]) (Leaf [17, 4])

||| This can get very complex, but still fully type-checked
ex5 : TensorA [BTreeNode, BTreeLeaf, Vect 3] Double
ex5 = fromArrayA $
  Node (Node'
          (Leaf [1,2,3])
          (Leaf [4,5,6]))
    Leaf'
    (Node (Leaf [178, -43, 63]) Leaf' Leaf')

{- 
We can index into any of these structures
        *
      /   \
     *     2  <---- indexing here is okay
    / \
(-42)  46 
-}
indexTreeExample : Double
indexTreeExample = exTree1 @@ [GoRight Done]


failing
  {- 
  And we'll get errors if we try to index outside of the structure
          *
        /   \
       *     2  
      / \     \
  (-42)  46    X   <---- indexing here throws an error
  -}
  indexTreeExampleFail : Double
  indexTreeExampleFail = ex1 @@ [GoRight (GoRight Done)]


||| We can also reshape and traverse non-cubical tensors
traverseTree : TensorA [List] Double
traverseTree = fromArrayAMap postorderNode ex3


-- exReshape = 
-- TODO reshape example for non-cubical tensors