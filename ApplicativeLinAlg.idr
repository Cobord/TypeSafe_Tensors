module ApplicativeLinAlg

import Data.Fin
import Data.Vect

import Tensor
import Tree
import Ring

-- Generalised sum operation
-- F-Algebra in the usual sense
interface Algebra (f : Type -> Type) a where
  reduce : f a -> a

interface Comult (f : Type -> Type) a where
  comult : f a -> f (f a)

-- Generalised sum operation on a tensor
-- This will be an instance of Applicative
{shape : Vect n Nat} -> Ring a => Algebra (Tensor shape) a where
  reduce xs = foldr (~+~) zero xs 

{shape : Vect n Nat} -> Ring a => Comult (Tensor shape) a where
  comult t = toNestedTensor' ?eii

gg : Tensor [3] Double -> Tensor [3, 3] Double
gg (TS xs) = TS $ map ?fn ?gg_rhs_0

Ring a => Algebra BinTreeLeafOnly a where
  reduce (Leaf leaf) = leaf
  reduce (Node _ leftTree rightTree)
    = (reduce {f=BinTreeLeafOnly} leftTree) ~+~ (reduce {f=BinTreeLeafOnly} rightTree)

dot : {f : Type -> Type} -> {a : Type}
  -> (Ring a, Applicative f, Algebra f a)
  => f a -> f a -> a
dot xs ys = reduce $ (\(x, y) => x ~*~ y) <$> (liftA2 xs ys)

-- [1, 2, 3]
-- can we even do outer product?
-- we wouldn't need reduce, but something like multiply?
outer : {f : Type -> Type} -> {a : Type}
  -> (Ring a, Applicative f, Algebra f a)
  => f a -> f a -> f (f a)
outer xs ys = let t = liftA2 xs ys
              in ?outer_rhs 
  

scaleVector : {f : Type -> Type} -> {a : Type}
  -> (Ring a, Applicative f, Algebra f a)
  => a -> f a -> f a
scaleVector a v = map (a ~*~) v

matrixVectorMultiply : {f, g : Type -> Type} -> {a : Type}
  -> (Ring a, Applicative f, Applicative g, Algebra f a)
  => g (f a) -> f a -> g a
matrixVectorMultiply m v = map (dot v) m

vectorMatrixMultiply : {f, g : Type -> Type} -> {a : Type}
  -> (Ring a, Applicative f, Applicative g, Algebra f (g a), Algebra g a)
  => f a -> f (g a) -> g a
vectorMatrixMultiply {a} {f} v m = let t : f (a, g a)
                                       t = liftA2 v m
                                       w : f (g a)
                                       w = map (uncurry scaleVector) t
                                   in reduce w

matMul : {f, g, h : Type -> Type} -> {a : Type}
  -> (Ring a, Applicative f, Applicative g, Applicative h, Algebra g a, Algebra h a, Algebra g (h a))
  => f (g a) -> g (h a) -> f (h a)
matMul m1 m2 = map (\row => vectorMatrixMultiply {f=g} {g=h} row m2) m1


v1 : Vector 3 Double
v1 = fromArray [0, 1, 2]

m1 : Matrix 3 4 Double
m1 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

v2 : Vector 4 Double
v2 = vectorMatrixMultiply {g=(Tensor [4])} v1 (toNestedTensor m1)

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
