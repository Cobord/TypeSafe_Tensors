module Examples.Tensors

import Data.Tensor

----------------------------------------
-- Examples of standard, cubical tensors
----------------------------------------

||| We can construct Tensors directly
t0 : Tensor [3, 4] Double
t0 = fromConcrete [ [0, 1, 2, 3]
                  , [4, 5, 6, 7]
                  , [8, 9, 10, 11]]


||| Or using analogous functions to np.arange and np.reshape
t1 : Tensor [6] Double
t1 = range

-- Need to fix reshape
t2 : Tensor [2, 3] Double
t2 = reshape t1

failing
  ||| Which will fail if we supply an array with the wrong shape
  failConcrete : Tensor [3, 4] Double
  failConcrete = fromConcrete [ [0, 1, 2, 3, 999]
                              , [4, 5, 6, 7]
                              , [8, 9, 10, 11]]

failing
  ||| Or if the reshape is not possible
  failReshape : Tensor [7, 2] Double
  failReshape = reshape t1

||| We can perform safe elementwise addition
t0Sum : Tensor [3, 4] Double
t0Sum = t0 + t0

||| And all sorts of numeric operations
numericOps : Tensor [3, 4] Double
numericOps = abs (- (t0 * t0) <&> (+7))

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
-- For some reason this started being incredibly slow to typecheck, commenting out for the time being
-- t1Transposed : Tensor [4, 3] Double
-- t1Transposed = transposeMatrix t1

||| Safe slicing
takeExample : Tensor [2, 1] Double
takeExample = takeTensor [2, 1] t0

failing
  ||| Which fails when we try to take more than exists
  takeExampleFail : Tensor [10, 2] Double
  takeExampleFail = takeTensor [10, 2] t0


----------------------------------------
-- Generalised tensor examples
-- These include list, tree shaped tensors, and other non-cubical tensors
----------------------------------------

||| TensorA can do everything that Tensor can
t0Again : TensorA [Vect 3, Vect 4] Double
t0Again = FromCubicalTensor t0

||| Including building concrete Tensors
t1again : TensorA [Vect 6] Double
t1again = fromConcreteA [1,2,3,4,5,6]

||| Above, the container Vect is made explicit in the type
||| There are other containers we can use in its place
||| We can use List which allows us to store an arbitrary number of elements
exList : TensorA [List] Double
exList = fromConcreteA [1,2,3,4,5,6,7,8]

||| Same type as above, different number of elements
exList2 : TensorA [List] Double
exList2 = fromConcreteA [100,-200,1000]

{- 
We can also use BTreeLeaf, allowing us to store a tree with data on its leaves

        *
      /   \
     *     2 
    / \
(-42)  46 
-}
exTree1 : TensorA [BTreeLeaf] Double
exTree1 = fromConcreteA $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)



{- 
Here's another tree, with a different number of elements
        *
      /   \
     10   100 
-}
exTree2 : TensorA [BTreeLeaf] Double
exTree2 = fromConcreteA $ Node' (Leaf 10) (Leaf 100)

||| We can take the dot product of these two trees
||| The fact that they don't have the same number of elements is irrelevant
||| What matters is that the container defining them 'BTreeLeaf' is the same
dotProduct2 : TensorA [] Double
dotProduct2 = dotA exTree1 exTree2

||| Here's a tree with whose nodes are vectors of size 2
exTree3 : TensorA [BTreeNode, Vect 2] Double
exTree3 = fromConcreteA $ Node [4,1] (Node [17, 4] Leaf' Leaf') Leaf'

||| This can get very complex, but is still fully type-checked
exTree4 : TensorA [BTreeNode, BTreeLeaf, Vect 3] Double
exTree4 = fromConcreteA $
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
indexTreeExample = exTree1 @@ [GoLeft (GoLeft Done)]


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


{- 
We can also perform reshapes, views, and traversals of non-cubical tensors.
Here's a tree-vector with nodes as elements
        3
      /   \
     2     4
    / \   / \
   1   * *   * 
  / \
 *   *
-}
exTree5 : TensorA [BTreeNode] Double
exTree5 = fromConcreteA $ Node 3 (Node 2 (Node 1 Leaf' Leaf') Leaf') (Node 4 Leaf' Leaf')

||| And here is the in-order traversal of that tree
traverseTree : TensorA [List] Double
traverseTree = reshapeTensorA inorderBTreeNode exTree5