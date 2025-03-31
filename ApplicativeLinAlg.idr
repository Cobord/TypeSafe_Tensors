module ApplicativeLinAlg

import Data.Fin
import Data.Vect

import Tensor.Tensor
import Tree
import Rig

-- Generalised sum operation
-- F-Algebra in the usual sense
public export
interface Algebra (f : Type -> Type) a where
  reduce : f a -> a

public export
{n : Nat} -> Rig a => Algebra (Vect n) a where
  reduce xs = foldr (~+~) zero xs

public export
{shape : Vect n Nat} -> Rig a => Algebra (Tensor shape) a where
  reduce xs = foldr (~+~) zero xs 

public export
Rig a => Algebra BinTreeLeafOnly a where
  reduce (Leaf leaf) = leaf
  reduce (Node _ leftTree rightTree)
    = (reduce {f=BinTreeLeafOnly} leftTree) ~+~ (reduce {f=BinTreeLeafOnly} rightTree)

public export
Rig a => Algebra BinTreeNodeOnly a where
  reduce (Leaf _) = zero
  reduce (Node node leftTree rightTree) = node ~+~ (reduce {f=BinTreeNodeOnly} leftTree) ~+~ (reduce {f=BinTreeNodeOnly} rightTree)

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
  -> Rig a => BinTreeLeafOnly a -> BinTreeLeafOnly a -> a
dotTree = dot {f=BinTreeLeafOnly}


-- Multiply a matrix and a vector
public export
multiplyMV : {f, g : Type -> Type} -> {a : Type}
  -> (Applicative f, Applicative g, Rig a, Algebra g a)
  => f (g a) -> g a -> f a
multiplyMV m v = dot v <$> m

-- Scale a vector by a scalar
public export
scaleVector : {f : Type -> Type} -> {a : Type}
  -> (Rig a, Functor f)
  => a -> f a -> f a
scaleVector a v = (a ~*~) <$> v

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
public export
matMul : {f, g, h : Type -> Type} -> {a : Type}
  -> (Functor f, Applicative g, Applicative h, Rig a, Algebra g (h a))
  => f (g a) -> g (h a) -> f (h a)
matMul m1 m2 = m1 <&> (\row => multiplyVM row m2)


matMulTensor : {i, j, k : Nat} -> {f : Type -> Type} -> {a : Type}
  -> Rig a => 
  Tensor [i, j] a -> Tensor [j, k] a -> Tensor [i, k] a
matMulTensor m n = fromNestedTensor (matMul (toNestedTensor m) (toNestedTensor n))

v1 : Vector 3 Double
v1 = fromArray [0, 1, 2]

m1 : Matrix 3 4 Double
m1 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

v2 : Vector 4 Double
v2 = multiplyVM v1 (toNestedTensor m1)

{-
7
-}
tree0 : BinTreeLeafOnly Double
tree0 = Leaf 7

{-
  /\
 3  4
-}
tree1 : BinTreeLeafOnly Double
tree1 = Node () (Leaf 3) (Leaf 4)

{-
    /      \
  /\     /  \ 
 1 10  100  1000
-}
tree2 : BinTreeLeafOnly Double
tree2 = Node () (Node () (Leaf 1) (Leaf 10)) (Node () (Leaf 100) (Leaf 1000))

dd : Double
dd = dot {f=BinTreeLeafOnly} tree1 tree2


interface Exp a where
  exp : a -> a

Exp Double where
  exp = Prelude.exp

softmax : {f : Type -> Type}
  -> (Functor f, Algebra f a, Fractional a, Exp a) => f a -> f a
softmax {f} xs = let exps = exp <$> xs
                 in exps <&> (/ reduce exps)
 
softmaxVect : {n : Nat} -> Vect n Double -> Vect n Double
softmaxVect = softmax

softmaxTreeLeaf : BinTreeLeafOnly Double -> BinTreeLeafOnly Double
softmaxTreeLeaf = softmax {f=BinTreeLeafOnly}

softmaxTreeNode : BinTreeNodeOnly Double -> BinTreeNodeOnly Double
softmaxTreeNode = softmax {f=BinTreeNodeOnly}


attention : {f, g : Type -> Type} -> {a : Type}
  -> (Applicative f, Applicative g, Rig a, Algebra f a, Algebra f (g a))
  => (f a -> f a) -> f (g a) -> f (g a) -> f (g a) -> f (g a)
attention softmax q k v = ?attent



tN1 : BinTreeNodeOnly Double
tN1 = Node 3 (Leaf ()) (Leaf ())

tN2 : BinTreeNodeOnly Double
tN2 = Node 3 (Node 4 (Leaf ()) (Leaf ())) (Leaf ())

tL1 : BinTreeLeafOnly Double
tL1 = Node () (Leaf 0.1) (Leaf 0.3)

-- tL2 : BinTreeLeafOnly Double
-- tL2 = Node () (Leaf 0.4) (Node (Leaf 0.1) (Leaf 0.3))





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
  
