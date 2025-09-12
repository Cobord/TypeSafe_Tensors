
# TensorType

[![build](https://github.com/bgavran/TypeSafe_Tensors/actions/workflows/build.yml/badge.svg)](https://github.com/bgavran/TypeSafe_Tensors/actions/workflows/build.yml)

> TLDR; numpy, but with types, and the ability to manipulate tree-shaped arrays

TensorType is a framework for pure functional tensor processing, implemented in Idris 2. It
* is **type-safe**: tensor indexing and contractions fail at compile time if types do not match
* **supports non-cubical tensors**: tensors of trees and streams are supported, instead of just arrays
* **is made with ergonomics in mind**: it aims to provide the standard NumPy/PyTorch interface to the user in a purely functional language

At the moment its main purpose is to enable rapid prototyping of structured neural network architectures. For instance, it is expressive enough to [implement generalised cross-attention](https://github.com/bgavran/TypeSafe_Tensors/blob/main/src/Architectures/Attention.idr#L10) (as described in the [Generalised Transformers blog post](https://glaive-research.org/2025/02/11/Generalized-Transformers-from-Applicative-Functors.html)).
It is in very early stages of development; expect breaking changes. It is not yet performant: down the line the goal is to obtain performance in a systematic way, not at the expense of compositionality and types, but rather because of them. See more in the section [below](#Goal-and-technical-details).


* [Examples](#Examples)
* [Installation instructions](#Installation-instructions)
* [Goal and technical details](#Goal-and-technical-details)
* [Planned features](#Planned-features)

## Examples

(taken from `examples/BasicExamples.idr`)

Import `Data.Tensor` at the top of your file.

```idris
import Data.Tensor
```

Now you can construct tensors directly:

```idris
t0 : Tensor [3, 4] Double
t0 = fromConcreteTy [ [0, 1, 2, 3]
                    , [4, 5, 6, 7]
                    , [8, 9, 10, 11]]
```

or by using functions analogous to numpy's, such as `np.arange` and `np.reshape`:

```idris
t1 : Tensor [6] Double
t1 = arange

t2 : Tensor [2, 3] Double
t2 = reshape t1
```

where the difference between numpy is that these operations are typechecked - meaning they will fail _at compile-time_ if you supply an array with the wrong shape.
```idris
failing
  failConcrete : Tensor [3, 4] Double
  failConcrete = fromConcreteTy [ [0, 1, 2, 3, 999]
                                , [4, 5, 6, 7]
                                , [8, 9, 10, 11]]
failing
  failRange : Tensor [6]
  failRange = arange {n=7}
```

You can perform all sorts of familiar numeric operations:

```idris
exampleSum : Tensor [3, 4] Double
exampleSum = t0 + t0

exampleOp : Tensor [3, 4] Double
exampleOp = abs (- (t0 * t0) <&> (+7))
```

including standard linear algebra

```idris
dotExample : Tensor [] Double
dotExample = dot t1 (t1 <&> (+5))

matMulExample : Tensor [2, 4]
matMulExample = matMul t2 t0

transposeExample : Tensor [4, 3] Double
transposeExample = transposeMatrix t0
```

which all have their types checked at compile-time. For instance, you can't add tensors of different shapes, or perform matrix multiplication if the dimensions of matrices don't match.

```idris
failing
  sumFail : Tensor [3, 4] Double
  sumFail = t0 + t1
  
failing
  matMulFail : Tensor [7] Double
  matMulFail = matMul t0 t1
```

Like in numpy, you can safely index into tensors, set values of tensors, and perform slicing:

```idris
||| Retrieves the value of t0 at location [1, 2]
indexExample : Double
indexExample = t0 @@ [1, 2]

||| Sets the value of t0 at location [1, 3] to 99 
setExample : Tensor [3, 4]
setExample = set t0 [1, 3] 99

||| Takes the first two rows, and 1st column of t0
sliceExample : Tensor [2, 1] Double
sliceExample = take [2, 1] t0
```

which will all fail if you go out of bounds:
```idris
failing
  indexExampleFail : Double
  indexExampleFail = t1 @@ [7, 2]

failing
  sliceFail : Tensor [10, 2] Double
  sliceFail = take [10, 2] t0
```

**And most importantly, you can do all of this with *non-cubical* tensors.** These describe tensors whose shape isn't rectangular/cubical, but can be branching/recursive/higher-order.

These are described via 'containers' and the datatype named `CTensor` standing for 'container tensor'.
Let's understand what it can do - it can do everything `Tensor` can:

```idris
t0Again : CTensor [Vect 3, Vect 4] Double
t0Again = t0
```

including building concrete tensors:

```idris
t1again : CTensor [Vect 6] Double
t1again = fromConcreteTy [1,2,3,4,5,6]
```

Here, the container `Vect` is made explicit in the type. There are other containers we can use in its place. Here is a container `BinTree` of binary trees recast as a tree-tensor:

```idris
{-
       60
      /  \
     7    2 
    / \
(-42)  46 
-}
treeExample1 : CTensor [BinTree] Double
treeExample1 = fromConcreteTy $ Node 60 (Node 7 (Leaf (-42)) (Leaf 46)) (Leaf 2)
```

This container allows us to store an arbitrary number of elements, unlike `Vect`. Here is another tree-tensor.

```idris
{-
   5
  / \
100  4
-}
treeExample2 : CTensor [BinTree] Double
treeExample2 = fromConcreteTy $ Node 5 (Leaf 100) (Leaf 4)
```

The benefit of this representation is that all linear algebra operations follow smoothly. The example below is the _dot product of trees_. The fact that they have the same number of elements is irrelevant.
What matters is that the container defining them (`BinTree`) is the same.

```idris
dotProductTree : CTensor [] Double
dotProductTree = dot treeExample1 treeExample2
```

We can do much more. Here's a tree-tensor with values only on its leaves:

```idris
{-
        *
      /   \
     *     2 
    / \
(-42)  46 
-}
treeLeafExample : CTensor [BinTreeLeaf] Double
treeLeafExample = fromConcreteTy $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)
```

and here's a tree-tensor with values only on its nodes:

```idris
{-
       60
      /  \
     7    *
    / \
   *   * 
-}
treeNodeExample : CTensor [BinTreeNode] Double
treeNodeExample = fromConcreteTy $ Node 60 (Node 7 Leaf' Leaf')  Leaf'
```

And this can get very complex and nested, as `exTree3` and `exTree4` show. But it still fully type-checked, and working as you'd expect.

```idris
treeExample3 : CTensor [BinTreeNode, Vect 2] Double
treeExample3 = fromConcreteTy $ Node [4,1] (Node [17, 4] Leaf' Leaf') Leaf'

treeExample4 : CTensor [BinTreeNode, BinTreeLeaf, Vect 3] Double
treeExample4 = fromConcreteTy $
  Node (Node'
          (Leaf [1,2,3])
          (Leaf [4,5,6]))
    Leaf'
    (Node (Leaf [178, -43, 63]) Leaf' Leaf')
```

For instance, we can index into `treeExample1`:
```idris
{- 
We can index into any of these structures
       60
      /  \
     7    2  <---- indexing here is okay
    / \
(-42)  46 
-}
indexTreeExample1 : Double
indexTreeExample1 = treeExample1 @@ [GoRight AtLeaf]
```

This will fail _at compile-time_ if you try to index outside of the tree structure:

```idris
failing
  {- 
         60
        /  \
       7    2  
      / \    \
  (-42)  46   X   <---- indexing here throws an error
  -}
  indexTreeExample1Fail : Double
  indexTreeExample1Fail = treeExample1 @@ [GoRight (GoRight AtLeaf)]
```

Likewise, you can perform reshapes, views, reversals, sorting and traversals of non-cubical tensors.
Here is the in-order traversal of `treeExample1` from above.

```idris
{-
       60
      /  \
     7    2 
    / \
(-42)  46 
-}
traversalExample : CTensor [List] Double
traversalExample = restructure (wrap inorder) treeExample1
```

## Installation instructions

It's recommended to manage the installation of this package (and generally, Idris 2) using the Idris 2 package manager [pack](https://github.com/stefan-hoeck/idris2-pack). The instructions below assume you've got both installed.

**If you want to just try it out in the REPL:**
1. Clone repository, and `cd` into it
2. Run `pack repl examples/BasicExamples.idr`
3. That's it!

**To use this framework in your project**, follow [pack standard practices](https://github.com/stefan-hoeck/idris2-pack/tree/main/example1):
1. Add the following to your `pack.toml`
```
[custom.all.tensortype]
type   = "git"
url    = "https://github.com/bgavran/TensorType"
commit = "latest:main"
ipkg   = "tensortype.ipkg"
```
2. Add `tensortype` to your `depends` argument in your project's `.ipkg` file. (Just like it is done in `examples/tensortype-examples.ipkg`)
3. Include `import Data.Tensor` at the top of your source files.
4. That's it!


## Goal and technical details

In addition to enabling fast prototyping of structured neural networks, the goal of this framework is to eventually evaluate the following hypothesis:

> **Performance can be achieved not at the expense of compositionality, but because of it.**

by taking special care to:
1) develop typed tensor interface and abstractions that enable abundant static analysis, and 
2) defer the sacrifice of those typed abstractions for performance optimisations until the point when it becomes clear that such a sacrifice is necessary.

This static analysis is aimed to inform performance optimisations down the line, especially when in context of non-cubical tensors. These are at the moment only scarcely explored, without any existing CUDA packages or optimisation algorithms.

When it comes to technical details, this library hinges of three interdependent components:
* **Containers** for **well-typed indexing of non-cubical tensors**: they allow us to validate that an index into a generalised tensor is not out of bounds at compile-time. Doing this with cubical containers is easy since they expose the size information at the type level (i.e. `Tensor [2,3,4] Double`), but once we move on to the world of applicative functors this is no longer the case. Checking that an index into a `CTensor [BinTreeNode] Double` is not out of bounds is only possible if the underlying functor additionally comes equipped with the data of the valid set of "shapes" and the valid "positions" for that shape. This is equivalent to asking that the functor is polynomial, or that the functor is an extension of a container.
* **Applicative functors** for **generalised linear algebra**: they allow us to perform generalised linear algebra operations as described in the [Applicative Programming with Naperian Functors](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf) paper.
* **Dependent lenses** for **reshaping and traversing operations**: they allow us to define morphisms of containers, and therefore generalised tensor reshaping operations that do not operate on the content of the data, only the shape. These include views, reshapes, and traversals, and many other culprits that appear in libraries like numpy.

## Planned features
* Type-safe einsum
* Type-safe broadcasting and stacking for both cubical and applicative tensors
* In-place operations/views, strided representation of tensors, including reasearch on feasibility of such strided variants for non-cubical tensors
* Better error reporting
* Comprehensive optimisation via a FFI to a low-level kernel


## Contact

Contributions and collaboration on this is welcome, feel free to submit pull requests/issues or get in touch directly.