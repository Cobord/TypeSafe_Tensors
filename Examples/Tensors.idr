module Examples.Tensors

import Data.Tensor
import Data.Tensor.Utils
import Data.Tensor.NaperianTensor


----------------------------------------
-- Examples of standard, cubical tensors
----------------------------------------

||| Analogous to np.arange, except the range is specified in the type
t0 : Tensor [7] Double
t0 = range

||| We can construct Tensors directly
t1 : Tensor [3, 4] Double
t1 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

failing
   ||| And we'll get errors if we supply the wrong shape
   t1Fail : Tensor [3, 4] Double
   t1Fail = fromArray [ [0, 1, 2, 3, 999]
                      , [4, 5, 6, 7]
                      , [8, 9, 10, 11]]


t2 : Tensor [2, 5] Double
t2 = fromArray [ [0, 1, 2, 3, 4]
               , [5, 6, 7, 8, 9]]


||| Safe elementwise addition
tSum : Tensor [3, 4] Double
tSum = t1 + t1

failing
  ||| Can't add tensors of different shapes
  tSumFail : Tensor [3, 4] Double
  tSumFail = t1 + t2

||| Safe indexing
indexExample : Double
indexExample = t1 @@@ [1, 2]

failing
   ||| We cannot index outside of the tensor's shape
   indexExampleFail : Double
   indexExampleFail = t1 @@@ [7, 2]

||| Safe transposition
t1Transposed : Tensor [4, 3] Double
t1Transposed = transposeMatrix t1

||| We can do all sorts of numeric operations
numericOps : Tensor [2, 5] Double
numericOps = abs ((t2 * negate t2) <&> (+7))

||| Safe slicing, takeTensor [10, 2] t1 would not compile
takeExample : Tensor [2, 1] Double
takeExample = takeTensor [2, 1] t1

failing
  takeExampleFail : Tensor [10, 2] Double
  takeExampleFail = takeTensor [10, 2] t1

||| Dot product of two vectors
dotProduct : Tensor [] Double
dotProduct = dot t0 t0

failing
  ||| Can't dot product two different-sized vectors
  dotProductFail : Tensor [] Double
  dotProductFail = dot t0 (the (Tensor [5] Double) range)


----------------------------------------
-- Generalised tensor examples
-- These include tree shaped tensors, and other non-cubical tensors
----------------------------------------

||| TensorA can do everything that Tensor can
t0again : TensorA [VectCont 7] Double
t0again = FromCubicalTensor t0

t1again : TensorA [VectCont 3, VectCont 4] Double
t1again = FromCubicalTensor t1 

{- 
Instead of an n-element vector, here's tree with leaves as elements
        *
      /   \
     *     2 
    / \
(-42)  46 
-}
ex1 : TensorA [BTreeLeafCont] Double
ex1 = fromArrayA $ fromBTreeLeaf $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)


{- 
Here's another tree, with a different number of elements
        *
      /   \
     10   100 
-}
ex2 : TensorA [BTreeLeafCont] Double
ex2 = fromArrayA $ fromBTreeLeaf $ Node' (Leaf 10) (Leaf 100)

||| We can take the dot product of these two trees
||| The fact that they don't have the same number of elements does not matter
||| What matters is that the container defining them 'BTreeLeafCont' is the same
dotProduct2 : TensorA [] Double
dotProduct2 = dotA ex1 ex2

{- 
Here's a tree with nodes as elements
   127
  /   \
 *    14     
      / \
     *   * 
-}
ex3 : TensorA [BTreeNodeCont] Double
ex3 = fromArrayA $ fromBTreeNode $ Node 127 Leaf' (Node 14 Leaf' Leaf')

||| And here's a tree with whose nodes are vectors of size 2
ex4 : TensorA [BTreeLeafCont, VectCont 2] Double
ex4 = fromArrayA $ fromBTreeLeaf $ (Leaf $ fromVect [1,2])

{- 
We can index into any of these structures
        *
      /   \
     *     2  <---- indexing here is okay
    / \
(-42)  46 
-}
indexTreeExample : Double
indexTreeExample = ex1 @@ [GoRLeaf AtLeaf]


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
  indexTreeExampleFail = ex1 @@ [GoRLeaf (GoRLeaf AtLeaf)]