module Tensor

import Data.Fin
import Data.Vect

{-
`n` is also often called rank of a tensor
-}
data Tensor : (shape : Vect n Nat) -> (contentType : Type) -> Type where
    TZ  : a -> Tensor [] a
    TS : Vect d (Tensor ds a) -> Tensor (d :: ds) a

Functor (Tensor shape) where
  map f (TZ x) = TZ (f x)
  map f (TS xs) = TS (map (map f) xs)

Foldable (Tensor shape) where
  foldr f z (TZ x) = f x z 
  foldr f z (TS xs) = foldr (\t, acc => foldr f acc t) z xs 


Show a => Show (Tensor shape a) where
  show (TZ x) = show x
  show (TS xs) = show xs


-- This equality doesn't hold as stated because:
-- Tensor (n :: ns) a is a tensor of shape (n :: ns) with elements of type a
-- Tensor [n] (Tensor ns a) would be a tensor of shape [n] with elements of type (Tensor ns a)
-- 
-- We can define functions that convert between these representations:

toNestedTensor : {n : Nat} -> {ns : Vect m Nat} -> {a : Type} -> 
                Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
toNestedTensor (TS vs) = TS (map TZ vs)

fromNestedTensor : {n : Nat} -> {ns : Vect m Nat} -> {a : Type} -> 
                   Tensor [n] (Tensor ns a) -> Tensor (n :: ns) a
fromNestedTensor (TS vs) = TS (map (\(TZ jk) => jk) vs)

-- The proof shows these conversions form a round-trip:
--pp : {n : Nat} -> {ns : Vect m Nat} -> {a : Type} ->
--     (v : Tensor (n :: ns) a) -> v = fromNestedTensor (toNestedTensor v)
--pp (TS vs) = Refl
--
---- Alternative proof showing the other direction:
--pp2 : {n : Nat} -> {ns : Vect m Nat} -> {a : Type} ->
--      (v : Vect n (Tensor ns a)) -> v = toNestedTensor (fromNestedTensor v)
--pp2 v = Refl

Scalar : (contentType : Type) -> Type
Scalar contentType = Tensor [] contentType

Vector : (size : Nat) -> (contentType : Type) -> Type
Vector size contentType = Tensor [size] contentType

Matrix : (rows, cols : Nat) -> (contentType : Type) -> Type
Matrix rows cols contentType = Tensor [rows, cols] contentType

-- unit of a monoidal functor
tensorReplicate : {shape : Vect n Nat} -> a -> Tensor shape a
tensorReplicate {shape = []} a = TZ a
tensorReplicate {shape = (n :: ns)} a = TS (replicate n (tensorReplicate a))

-- generalised zip
-- laxator of a monoidal functor
liftA2Tensor : Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
liftA2Tensor (TZ a) (TZ b) = TZ (a, b)
liftA2Tensor (TS as) (TS bs) = TS (zipWith liftA2Tensor as bs) 


{shape : Vect n Nat} -> Applicative (Tensor shape) where
  pure x = tensorReplicate x
  fs <*> xs = map (uncurry ($)) $ liftA2Tensor fs xs 

liftA2 : Applicative f => f a -> f b -> f (a, b)
liftA2 fa fb = (map (,) fa) <*> fb

  -- probably can be defined for arbitrary tensors, but it wasn't clear how to pattern match on `shape` in `Tensor shape`
-- {n : Nat} -> Applicative (Tensor [n]) where
--   pure x = TS (replicate n (TZ x))
--   fs <*> xs = map (uncurry ($)) $ liftA2 fs xs 

interface Ring a where
  zero : a
  one : a
  (~+~) : a -> a -> a
  (~*~) : a -> a -> a
  -- also laws, but we don't care right now

export infixr 6 ~+~
export infixr 7 ~*~

Ring Double where
  zero = 0
  one = 1
  (~+~) = (+)
  (~*~) = (*)

{shape : Vect n Nat} -> Ring a => Ring (Tensor shape a) where
  zero = tensorReplicate zero
  one = tensorReplicate one
  xs ~+~ ys = map (uncurry (~+~)) $ liftA2 xs ys
  xs ~*~ ys = map (uncurry (~*~)) $ liftA2 xs ys


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

-- The point of this construction is to be able to easily create tensors, without needing to use the inductive form requiring `TZ` and `TS`. 
-- Also, there was this thing with a separate indexing type? But that's unrelated, I think
Array : (shape : Vect rank Nat) -> (contentType : Type) -> Type
Array []        a = a
Array (m :: ms) a = Vect m (Array ms a)

fromArray : {xs : Vect rank Nat} -> Array xs a -> Tensor xs a
fromArray {xs = []} y = TZ y
fromArray {xs = (_ :: _)} y = TS (fromArray <$> y)

v1 : Vector 3 Double
v1 = fromArray [0, 1, 2]

m1 : Matrix 3 4 Double
m1 = fromArray [ [0, 1, 2, 3]
               , [4, 5, 6, 7]
               , [8, 9, 10, 11]]

v2 : Vector 4 Double
v2 = vectorMatrixMultiply {g=(Tensor [4])} v1 (toNestedTensor m1)



scalar1 : Tensor [] Double
scalar1 = TZ 3

scalar2 : Tensor [1] Double
scalar2 = TS [TZ 1.8]


t : {A, B : Type}
  -> Bool -> Type
t False = A
t True = B

iso : {A, B : Type}
  -> (A, B) -> (b : Bool) -> t {A=A} {B=B} b
iso (a, _) False = a
iso (_, b) True = b

tt : {A : Type} -> {B : A -> Type}
  -> Bool -> Type
tt False = A
tt True = B ?otetwe_1

iso2 : {A : Type} -> {B : A -> Type}
  -> (a : A ** B a) -> (b : Bool) -> tt {A=A} {B=B} b
iso2 ((a ** _)) False = a
iso2 ((a ** b)) True = ?tuu_2
