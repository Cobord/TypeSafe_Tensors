module ApplicativeLinAlg

import Data.Fin
import Data.Vect

import Tensor
import Ring

-- Generalised sum operation
-- F-Algebra in the usual sense
interface Algebra (f : Type -> Type) a where
  reduce : f a -> a

-- Generalised sum operation on a tensor
{shape : Vect n Nat} -> Ring a => Algebra (Tensor shape) a where
  reduce xs = foldr (~+~) zero xs 

dot : {f : Type -> Type} -> {a : Type}
  -> (Ring a, Applicative f, Algebra f a)
  => f a -> f a -> a
dot xs ys = reduce $ map (uncurry (~*~)) (liftA2 xs ys)

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


-- matMul : {i, j, k : Nat}
--   -> Tensor [i, j] a -> Tensor [j, k] a -> Tensor [i, k] a
-- matMul m1 m2 = ?ooo

v1 : Vector 3 Double
v1 = fromArray [0, 1, 2]

m1 : Matrix 3 4 Double
m1 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

v2 : Vector 4 Double
v2 = vectorMatrixMultiply {g=(Tensor [4])} v1 (toNestedTensor m1)


