module Tensor

import Data.Fin
import Data.Vect

{-
-}
data Tensor : (shape : Vect n Nat) -> (contentType : Type) -> Type where
    TZ  : a -> Tensor [] a
    TS : Vect d (Tensor ds a) -> Tensor (d :: ds) a

Vector : (size : Nat) -> (contentType : Type) -> Type
Vector size contentType = Tensor [size] contentType

Matrix : (rows, cols : Nat) -> (contentType : Type) -> Type
Matrix rows cols contentType = Tensor [rows, cols] contentType

Functor (Tensor shape) where
  map f (TZ x) = TZ (f x)
  map f (TS xs) = TS (map (map f) xs)

Foldable (Tensor shape) where
  foldr f z (TZ x) = f x z 
  foldr f z (TS xs) = foldr (\t, acc => foldr f acc t) z xs 

interface Ring a where
  zero : a
  one : a
  (~+~) : a -> a -> a
  (~*~) : a -> a -> a
  -- also laws, but we don't care right now

-- Generalised sum operation
-- F-Algebra in the usual sense
interface Algebra (f : Type -> Type) a where
  reduce : f a -> a

-- Generalised sum operation on a tensor
{shape : Vect n Nat} -> Ring a => Algebra (Tensor shape) a where
  reduce xs = foldr (~+~) zero xs 

-- generalised zip
-- laxator of a monoidal functor
liftA2 : Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
liftA2 (TZ a) (TZ b) = TZ (a, b)
liftA2 (TS as) (TS bs) = TS (zipWith liftA2 as bs) 

-- probably can be defined for arbitrary tensors, but it wasn't clear how to pattern match on `shape` in `Tensor shape`
{n : Nat} -> Applicative (Tensor [n]) where
  pure x = TS (replicate n (TZ x))
  fs <*> xs = ?applyy
  -- (<*>) (TZ f) (TZ x) = TZ (f x)
  -- (<*>) (TS fs) (TS xs) = TS (zipWith (<*>) fs xs)


matMul : {i, j, k : Nat}
  -> Tensor [i, j] a -> Tensor [j, k] a -> Tensor [i, k] a
matMul = ?ooo

-- not sure what to do with this. Also, there was this thing with a separate indexing type
Array : (shape : Vect rank Nat) -> (contentType : Type) -> Type
Array []        a = a
Array (m :: ms) a = Vect m (Array ms a)


fromArray : {xs : Vect rank Nat} -> Array xs a -> Tensor xs a
fromArray {xs = []} y = TZ y
fromArray {xs = (_ :: _)} y = TS (fromArray <$> y)


tArray : Array [3, 4] Double
tArray = [ [0, 1, 2, 3]
    , [4, 5, 6, 7]
    , [8, 9, 10, 11]]


Scalar : Type -> Type
Scalar a = Tensor [] a

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
