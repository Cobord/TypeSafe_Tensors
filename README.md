
# Type-safe Tensors & Network architectures

[![build](https://github.com/bgavran/TypeSafe_Tensors/actions/workflows/build.yml/badge.svg)](https://github.com/bgavran/TypeSafe_Tensors/actions/workflows/build.yml)

This is framework for pure functional tensor processing, implemented in Idris 2. It
* Is **type-safe**: tensor indexing and contractions fail at compile time if types do not match
* **implements non-cubical tensors**: tensors of trees and streams are supported, instead of just arrays
* **is made with ergonomics in mind**: it aims to provide the standard numpy/Pytorch interface to the user in a purely functional language with first-class types

The working hypothesis and goal of this framework is to **achieve performance not at the expense of compositionality, but because of it**, described [below](#Goal-and-technical-details).

This framework is in active development and with many rough edges, but at the moment it is expressive enough to [implement generalised cross-attention](https://github.com/bgavran/TypeSafe_Tensors/blob/main/Architectures/Attention.idr#L19) as described in [Generalised Transformers using Applicative Functors](https://glaive-research.org/2025/02/11/Generalized-Transformers-from-Applicative-Functors.html).

* [Examples](#Examples)
* [Installation instructions](#Installation-instructions)
* [Goal and technical details](#Goal-and-technical-details)
* [Planned features](#Planned-features)

## Examples

These examples are taken from `Examples.Tensors.idr`.

```idris
||| We can construct Tensors directly
t0 : Tensor [3, 4] Double
t0 = fromConcrete [ [0, 1, 2, 3]
                  , [4, 5, 6, 7]
                  , [8, 9, 10, 11]]


||| Or using analogous functions np.arange, for instance
t1 : Tensor [6] Double
t1 = range

failing
  ||| These operations will fail if we supply an array with the wrong shape
  failConcrete : Tensor [3, 4] Double
  failConcrete = fromConcrete [ [0, 1, 2, 3, 999]
                              , [4, 5, 6, 7]
                              , [8, 9, 10, 11]]

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
  tSumFail = t0 + t1

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

||| Safe transposition
t1Transposed : Tensor [4, 3] Double
t1Transposed = transposeMatrix t1

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
```

## Installation instructions

It's recommended to install this package (and generally, Idris 2) using the Idris 2 package manager [pack](https://github.com/stefan-hoeck/idris2-pack). Below it is assumed you've got both installed.

1. Clone repository, and `cd` into it
2. Run `pack install-deps typesafe-tensors.ipkg`
3. (Optional) If you want Idris 2 support in your IDE run `pack install-app idris2-lsp`

That's it!

To run examples in the REPL run `pack repl Examples/Tensors.idr`. To use this package in your code follow the instructions in [pack documentation](https://github.com/stefan-hoeck/idris2-pack/tree/main/example1) to use this library, and then include `import Data.Tensor` at the top of your source file.


## Goal and technical details

I've had a long-standing working hypothesis about software engineering that can be captured in a succint phrase: **performance ought to be achieved not at the expense of compositionality, but because of it**. 
The goal of this framework is to evaluate this hypothesis by implementing a working compositional and performant tensor processing framework. This means that special care is taken
1) to develop typed tensor interface and abstractions that enable abundant static analysis, and 
2) to defer the sacrifice of those typed abstractions for performance optimisations until the point when it becomes clear that such a sacrifice is necessary.

This static analysis is aimed to inform performance optimisations down the line, especially when in context of non-cubical tensors. These are at the moment only scarcely explored, without any known CUDA packages or optimisation algorithms existing.

The technical components of this library hinge of three interdependent components:
* **Containers**: they allow us to check that indexing a generalised Tensor is well-typed at compile-time. Doing this with cubical containers is easy since they expose the size information at the type level (i.e. `Tensor [2,3,4] Double`), but once we move on to the world of applicative functors this is no longer the case. Checking that an index into a `Tensor [BTreeNode] Double` is well-typed is only possible if the underlying functor additionally comes equipped with the data of a "shape", i.e. if the functor is a polynomial one, i.e. if the functor is the extension of a container.
* **Applicative functors**: they allow us to perform generalised linear algebra operations as described in the [Applicative Programming with Naperian Functors](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf) paper.
* **Dependent lenses**: they allow us to define morphisms of containers, and therefore generalised tensor reshaping operations that do not operate on the content of the data, only the shape. These include views, reshapes, and traversals, and many other culprits that appear in libraries like numpy.

## Planned features
* Type-safe einsum
* Type-safe broadcasting and stacking for both cubical and applicative tensors
* In-place operations/views, strided representation of tensors, including reasearch on feasibility of such strided variants for non-cubical tensors
* Better error reporting
* Comprehensive optimisation via a FFI to a low-level kernel


## Contact

Contributions and collaboration on this is welcome, feel free to submit pull requests/issues or get in touch directly.