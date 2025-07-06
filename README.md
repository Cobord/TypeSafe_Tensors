# Type-safe Tensors & Network architectures

This is framework for pure functional tensor processing, implemented in Idris 2. It
* Is **type-safe**: indexing and contractions fail at compile time if types do not match
* **implements non-cubical tensors**: tensors of trees and streams instead of just arrays are supported
* **is made with ergonomics in mind**: it aims to provide the familiar numpy/Pytorch interface to the user


It is expressive enough to [implement generalised cross-attention](https://github.com/bgavran/TypeSafe_Tensors/blob/main/Architectures/Attention.idr#L19) as described in [Generalised Transformers using Applicative Functors](https://glaive-research.org/2025/02/11/Generalized-Transformers-from-Applicative-Functors.html).

It is a proof of concept, with core examples below (taken from `Data.Tensor.TensorExamples.idr`), and many rough edges. See TODOs at the ottom of the page.

```idris
||| Analogous to np.arange, except the range is specified in the type
t0 : Tensor' [7] Double
t0 = range 

||| We can construct Tensors directly
t1 : Tensor' [3, 4] Double
t1 = fromArray' [ [0, 1, 2, 3]
                , [4, 5, 6, 7]
                , [8, 9, 10, 11]]


failing
   ||| And we'll get errors if we supply the wrong shape
   t1Fail : Tensor' [3, 4] Double
   t1Fail = fromArray' [ [0, 1, 2, 3, 999]
                       , [4, 5, 6, 7]
                       , [8, 9, 10, 11]]


t2 : Tensor' [2, 5] Double
t2 = fromArray' [ [0, 1, 2, 3, 4]
                , [5, 6, 7, 8, 9]]



||| Safe elementwise addition
tSum : Tensor' [3, 4] Double
tSum = t1 + t1

failing
  ||| Can't add tensors of different shapes
  tSumFail : Tensor' [3, 4] Double
  tSumFail = t1 + t2

||| Safe indexing
indexExample : Double
indexExample = t1 @@@ [1, 2]

failing
   ||| We cannot index outside of the tensor's shape
   indexExampleFail : Double
   indexExampleFail = t1 @@@ [7, 2]

||| Safe transposition
t1Transposed : Tensor' [4, 3] Double
t1Transposed = transposeMatrix' t1

||| We can do all sorts of numeric operations
numericOps : Tensor' [2, 5] Double
numericOps = abs ((t2 * negate t2) <&> (+7))

||| Safe slicing, takeTensor [10, 2] t1 would not compile
takeExample : Tensor' [2, 1] Double
takeExample = takeTensor' [2, 1] t1

failing
  takeExampleFail : Tensor' [10, 2] Double
  takeExampleFail = takeTensor' [10, 2] t1


||| Dot product of two vectors
dotProduct : Tensor' [] Double
dotProduct = dot' t0 t0

failing
  ||| Can't dot product two different-sized vectors
  dotProductFail : Tensor' [] Double
  dotProductFail = dot' t0 (the (Tensor' [5] Double) range)



----------------------------------------
-- Generalised tensor examples
----------------------------------------
-- These include tree shaped tensors, and other non-cubical ones


||| Tensor can do everything that Tensor' can
t0again : Tensor [VectCont 7] Double
t0again = fromCubicalTensor t0 -- Or alternatively, fromArray $ fromVect [1,2,3,4,5,6,7]

t1again : Tensor [VectCont 3, VectCont 4] Double
t1again = fromCubicalTensor t1 

||| Instead of an n-element vector, here's tree with leaves as elements.
ex1 : Tensor [BTreeLeafCont] Double
ex1 = fromArray $ fromBTreeLeaf $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)
{- 
        *
      /   \
     *     2 
    / \
(-42)  46 
-}

||| Here's another one, with a different number of elements
ex2 : Tensor [BTreeLeafCont] Double
ex2 = fromArray $ fromBTreeLeaf $ Node' (Leaf 10) (Leaf 100)

||| We can take their dot product!
||| It does not matter that they have the same number of elements, it matters that the functor is the same
dotProduct2 : Tensor [] Double
dotProduct2 = dot ex1 ex2

||| Here's a tree with nodes as elements
ex3 : Tensor [BTreeNodeCont] Double
ex3 = fromArray $ fromBTreeNode $ Node 127 Leaf' (Node 14 Leaf' Leaf')
{- 
   127
  /   \
 *    14     
      / \
     *   * 
-}

||| Or elements themselves can be vectors!
ex4 : Tensor [BTreeLeafCont, VectCont 2] Double
ex4 = fromArray $ fromBTreeLeaf $ (Leaf $ fromVect [1,2])

||| We can index into those structures
indexTreeExample : Double
indexTreeExample = ex1 @@ [GoRLeaf AtLeaf]
{- 
        *
      /   \
     *     2  <---- indexing here is okay
    / \
(-42)  46 
-}


failing
  ||| And we'll get errors if we try to index outside of the structure
  indexTreeExampleFail : Double
  indexTreeExampleFail = ex1 @@ [GoRLeaf (GoRLeaf AtLeaf)]
  {- 
          *
        /   \
       *     2  
      / \     \
  (-42)  46    X   <---- indexing here throws an error
  -}
```


## Future work
* Type-safe einsum
* Type-safe broadcasting, reshaping and stacking
* In-place operations/views
* Better ergonomics for general applicative tensors
* FFI to a low-level kernel for tensor operations
* No investigation has been done regarding optimisation yet


