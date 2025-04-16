module ApplicativeLinAlg

import Data.Fin
import Data.Vect

import Tensor.Tensor
import Tensor.Naperian
import Tree
import Rig

import Misc

||| Generalised sum operation
||| Categorically, an F-Algebra
public export
interface Algebra (f : Type -> Type) a where
  reduce : f a -> a

public export
{n : Nat} -> Rig a => Algebra (Vect n) a where
  reduce = foldr (~+~) zero

public export
{shape : Vect n Nat} -> Rig a => Algebra (Tensor shape) a where
  reduce = foldr (~+~) zero 

public export
[appSum] {shape : Vect n Nat} -> (Rig a, Applicative f)
  => Algebra (Tensor shape) (f a) where
  reduce (TZ val) = val
  reduce (TS xs) = reduce (reduce <$> xs)

aa : Algebra (Tensor [2]) (Tensor [3] a) => a
aa = ?aa_rhs

||| Just summing up elements of the tree given by the Rig a structure
public export
Rig a => Algebra BTreeLeaf a where
  reduce (Leaf leaf) = leaf
  reduce (Node _ leftTree rightTree)
    = (reduce {f=BTreeLeaf} leftTree) ~+~ 
      (reduce {f=BTreeLeaf} rightTree)

-- can be simplified by uncommenting the Rig (f a) instance in Rig.idr
public export
[usualSum'] (Rig a, Applicative f) => Algebra BTreeLeaf (f a) where
  reduce (Leaf leaf) = leaf
  reduce (Node node leftTree rightTree)
    = let lt = reduce {f=BTreeLeaf} leftTree 
          rt = reduce {f=BTreeLeaf} rightTree
      in (uncurry (~+~)) <$> (liftA2 lt rt) 

public export
Rig a => Algebra BTreeNode a where
  reduce (Leaf _) = zero
  reduce (Node node leftTree rightTree) = node ~+~ (reduce {f=BTreeNode} leftTree) ~+~ (reduce {f=BTreeNode} rightTree)

-- Scale a vector by a scalar
public export
scaleVector : (Rig a, Functor f)
  => a -> f a -> f a
scaleVector a v = (a ~*~) <$> v

-- Dot product in the usual sense
public export
dot : {f : Type -> Type} -> {a : Type}
  -> (Applicative f, Rig a, Algebra f a)
  => f a -> f a -> a
dot xs ys = reduce $ (\(x, y) => x ~*~ y) <$> (liftA2 xs ys)

public export
dotVect : {n : Nat} -> {a : Type}
  -> Rig a => Vect n a -> Vect n a -> a
dotVect = dot

public export
dotTensor : {shape : Vect n Nat} -> {a : Type}
  -> Rig a => Tensor shape a -> Tensor shape a -> a
dotTensor = dot

public export
dotTree : {a : Type}
  -> Rig a => BTreeLeaf a -> BTreeLeaf a -> a
dotTree = dot {f=BTreeLeaf}

-- Multiply a matrix and a vector
public export
multiplyMV : {f, g : Type -> Type} -> {a : Type}
  -> (Applicative f, Applicative g, Rig a, Algebra g a)
  => f (g a) -> g a -> f a
multiplyMV m v = dot v <$> m

-- Multiply a vector and a matrix
public export
multiplyVM : {f, g : Type -> Type} -> {a : Type}
  -> (Applicative f, Applicative g, Rig a, Algebra f (g a))
  => f a -> f (g a) -> g a
multiplyVM {a} {f} v m = let t : f (a, g a)
                             t = liftA2 v m
                             w : f (g a)
                             w = map (uncurry scaleVector) t
                         in reduce w

-- Multiply two matrices
-- "ij,jk->ik"
public export
matMul : {f, g, h : Type -> Type} -> {a : Type}
  -> (Functor f, Applicative g, Applicative h, Rig a, Algebra g (h a))
  => f (g a) -> g (h a) -> f (h a)
matMul m1 m2 = m1 <&> (\row => multiplyVM row m2)

-- Refactored implementation using Naperian transpose
-- Calculates result by dotting rows of m1 with columns of m2.
public export
matMul' : {f, g, h : Type -> Type} -> {a : Type}
  -> (Functor f, Applicative g, Naperian g, Naperian h, Rig a, Algebra g a)
  => f (g a) -> g (h a) -> f (h a)
matMul' m1 m2 = m1 <&> \rowA => (dot {f=g} rowA) <$> (transpose m2)

matMulTensor : {i, j, k : Nat} -> {f : Type -> Type} -> {a : Type}
  -> Rig a => Tensor [i, j] a -> Tensor [j, k] a -> Tensor [i, k] a
matMulTensor m n = fromNestedTensor (matMul' (toNestedTensor m) (toNestedTensor n))

-- ij,kj->ki
public export
multiplyMMT : {f, g, h: Type -> Type} -> {a : Type}
  -> (Applicative f, Applicative g, Functor h, Rig a, Algebra g a)
  => f (g a) -> h (g a) -> h (f a)
multiplyMMT m n = (multiplyMV m) <$> n


{-  3 x 4 matrix, (i, j)=(3,4)


-}

linearLayer : {i, j : Type -> Type} -> {a : Type}
  -> (Applicative i, Applicative j, Rig a, Algebra j a)
  => i (j a) -> i a -> j a -> i a
linearLayer weights bias input 
  = (uncurry (~+~)) <$> (liftA2 bias $ multiplyMV weights input)

v1 : Vector 3 Double
v1 = fromArray [0, 1, 2]

m1 : Matrix 3 4 Double
m1 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

-- v2 : Vector 4 Double
-- v2 = multiplyVM v1 (toNestedTensor m1)

{-
7
-}
tree0 : BTreeLeaf Double
tree0 = Leaf 7

{-
  /\
 3  4
-}
tree1 : BTreeLeaf Double
tree1 = Node () (Leaf 3) (Leaf 4)

{-
    /      \
  /\     /  \ 
 1 10  100  1000
-}
tree2 : BTreeLeaf Double
tree2 = Node () (Node () (Leaf 1) (Leaf 10)) (Node () (Leaf 100) (Leaf 1000))

dd : Double
dd = dot {f=BTreeLeaf} tree1 tree2


tN1 : BTreeNode Double
tN1 = Node 3 (Leaf ()) (Leaf ())

tN2 : BTreeNode Double
tN2 = Node 3 (Node 4 (Leaf ()) (Leaf ())) (Leaf ())

tL1 : BTreeLeaf Double
tL1 = Node () (Leaf 0.1) (Leaf 0.3)




interface Comult (f : Type -> Type) a where
  comult : f a -> f (f a)

{shape : Vect n Nat} -> Rig a => Comult (Tensor shape) a where
  comult t = toNestedTensor' ?eii

gg : Tensor [3] Double -> Tensor [3, 3] Double
gg (TS xs) = TS $ map ?fn ?gg_rhs_0

-- [1, 2, 3]
-- can we even do outer product?
-- we wouldn't need reduce, but something like multiply?
outer : {f : Type -> Type} -> {a : Type}
  -> (Rig a, Applicative f, Algebra f a)
  => f a -> f a -> f (f a)
outer xs ys = let t = liftA2 xs ys
              in ?outer_rhs 
  
