module Examples.Tensors

import Data.Tensor
import Data.Tensor.Utils
-- import Data.Tensor.NaperianTensor

{-
Need to compute stride-based functionality for:
 * Slice
 * Take
 * Transpose
 -}

----------------------------------------
-- Examples of standard, cubical tensors
----------------------------------------

||| We can construct Tensors directly
t1 : Tensor [3, 4] Double
t1 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

||| Or use functions analogous to np.reshape and np.arange, fully type-checked
t2 : Tensor [4, 5] Double
t2 = reshape $ range {n=20}

failing
  ||| Getting errors if we supply an array with the wrong shape
  t1Fail : Tensor [3, 4] Double
  t1Fail = fromArray [ [0, 1, 2, 3, 999]
                     , [4, 5, 6, 7]
                     , [8, 9, 10, 11]]

  ||| Or if the reshape is not possible
  t2Fail : Tensor [4, 5] Double
  t2Fail = reshape $ range {n=21}


||| We can perform safe elementwise addition
tSum : Tensor [3, 4] Double
tSum = t1 + t1

||| And all sorts of numeric operations
numericOps : Tensor [4, 5] Double
numericOps = abs ((t2 * negate t2) <&> (+7))

failing
  ||| Failing if we add tensors of different shapes
  tSumFail : Tensor [3, 4] Double
  tSumFail = t1 + t2

||| We can safely index into tensors
indexExample : Double
indexExample = t1 @@@ [1, 2]

failing
   ||| We cannot index outside of the tensor's shape
   indexExampleFail : Double
   indexExampleFail = t1 @@@ [7, 2]

-- ||| Safe transposition
-- t1Transposed : Tensor [4, 3] Double
-- t1Transposed = transposeMatrix t1


-- ||| Safe slicing, takeTensor [10, 2] t1 would not compile
-- takeExample : Tensor [2, 1] Double
-- takeExample = takeTensor [2, 1] t1

failing
  takeExampleFail : Tensor [10, 2] Double
  takeExampleFail = takeTensor [10, 2] t1

v : Tensor [5] Double
v = range

||| Dot product of two vectors
dotProduct : Tensor [] Double
dotProduct = dot v v

failing
  ||| Can't dot product two different-sized vectors
  dotProductFail : Tensor [] Double
  dotProductFail = dot v (range {n=6})


----------------------------------------
-- Generalised tensor examples
-- These include tree shaped tensors, and other non-cubical tensors
----------------------------------------

||| TensorA can do everything that Tensor can
t0again : TensorA [Vect 5] Double
t0again = FromCubicalTensor v

-- t1again : TensorA [Vect 3, Vect 4] Double -- I think here we want to automatically flatten, like numpy does. But then we lose shape information. This is something to fix
-- t1again = FromCubicalTensor t1 

t1again' : TensorA [Vect 12] Double 
t1again' = FromCubicalTensor t1 

{- 
Instead of an n-element vector, here's tree with leaves as elements
        *
      /   \
     *     2 
    / \
(-42)  46 
-}
ex1 : TensorA [BTreeLeaf] Double
ex1 = fromArrayA $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)


{- 
Here's another tree, with a different number of elements
        *
      /   \
     10   100 
-}
ex2 : TensorA [BTreeLeaf] Double
ex2 = fromArrayA $ Node' (Leaf 10) (Leaf 100)

||| We can take the dot product of these two trees
||| The fact that they don't have the same number of elements does not matter
||| What matters is that the container defining them 'BTreeLeaf' is the same
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
ex3 : TensorA [BTreeNode] Double
ex3 = fromArrayA $ Node 127 Leaf' (Node 14 Leaf' Leaf')

||| And here's a tree with whose nodes are vectors of size 2
ex4 : TensorA [BTreeLeaf, Vect 2] Double
ex4 = fromArrayA $ Node' (Leaf [4,1]) (Leaf [17, 4])

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