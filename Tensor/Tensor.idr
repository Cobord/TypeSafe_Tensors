module Tensor.Tensor

import Data.Fin
import Data.Vect


import Rig

%hide Data.Vect.transpose


{-
Three main datatypes in this file:
data Tensor -> defines tensors
Array -> for ease of creation of tensors from lists
IndexTensor -> for easy indexing of tensors
-}

{-
`n` is also often called rank of a tensor
-}
public export
data Tensor : (shape : Vect n Nat) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> Tensor [] dtype
    TS : Vect d (Tensor ds dtype) -> Tensor (d :: ds) dtype

public export
Show a => Show (Tensor shape a) where
  show (TZ x) = show x
  show (TS xs) = show xs

public export
Eq a => Eq (Tensor shape a) where
  (TZ v1) == (TZ v2) = v1 == v2
  (TS xs) == (TS ys) = xs == ys

public export
Functor (Tensor shape) where
  map f (TZ x) = TZ (f x)
  map f (TS xs) = TS (map (map f) xs)

public export
Foldable (Tensor shape) where
  foldr f z (TZ x) = f x z 
  foldr f z (TS xs) = foldr (\t, acc => foldr f acc t) z xs 

public export
Traversable (Tensor shape) where
  traverse fn (TZ val) = TZ <$> fn val
  traverse fn (TS xs) = TS <$> traverse (traverse fn) xs

-- This equality doesn't hold as stated because:
-- Tensor (n :: ns) a is a tensor of shape (n :: ns) with elements of type a
-- Tensor [n] (Tensor ns a) would be a tensor of shape [n] with elements of type (Tensor ns a)
-- 
-- We can define functions that convert between these representations:

public export
toNestedTensor : Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
toNestedTensor (TS vs) = TS (map TZ vs)

public export
fromNestedTensor : Tensor [n] (Tensor ns a) -> Tensor (n :: ns) a
fromNestedTensor (TS vs) = TS (map (\(TZ jk) => jk) vs)


-- More general version than above
public export
fromNestedTensor' : Tensor sh1 (Tensor sh2 a) -> Tensor (sh1 ++ sh2) a
fromNestedTensor' (TZ tv) = tv
fromNestedTensor' (TS xts) = TS $ map fromNestedTensor' xts

public export
toNestedTensor' : Tensor (sh1 ++ sh2) a -> Tensor sh1 (Tensor sh2 a)
toNestedTensor' t = ?toNestedTensor'_rhs

-- The proof shows these conversions form a round-trip:
--pp : {n : Nat} -> {ns : Vect m Nat} -> {a : Type} ->
--     (v : Tensor (n :: ns) a) -> v = fromNestedTensor (toNestedTensor v)
--pp (TS vs) = Refl
--
---- Alternative proof showing the other direction:
--pp2 : {n : Nat} -> {ns : Vect m Nat} -> {a : Type} ->
--      (v : Vect n (Tensor ns a)) -> v = toNestedTensor (fromNestedTensor v)
--pp2 v = Refl

public export
Scalar : (dtype : Type) -> Type
Scalar dtype = Tensor [] dtype

public export
Vector : (size : Nat) -> (dtype : Type) -> Type
Vector size dtype = Tensor [size] dtype

public export
Matrix : (rows, cols : Nat) -> (dtype : Type) -> Type
Matrix rows cols dtype = Tensor [rows, cols] dtype

-- unit of a monoidal functor
public export
tensorReplicate : {shape : Vect n Nat} -> a -> Tensor shape a
tensorReplicate {shape = []} a = TZ a
tensorReplicate {shape = (n :: ns)} a = TS (replicate n (tensorReplicate a))

-- generalised zip
-- laxator of a monoidal functor

public export
liftA2Tensor : Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
liftA2Tensor (TZ a) (TZ b) = TZ (a, b)
liftA2Tensor (TS as) (TS bs) = TS (zipWith liftA2Tensor as bs) 


public export
{shape : Vect n Nat} -> Applicative (Tensor shape) where
  pure x = tensorReplicate x
  fs <*> xs = map (uncurry ($)) $ liftA2Tensor fs xs 

public export
liftA2 : Applicative f => f a -> f b -> f (a, b)
liftA2 fa fb = (map (,) fa) <*> fb

-- Pointwise Rig structure
public export
{shape : Vect n Nat} -> Rig a => Rig (Tensor shape a) where
  zero = tensorReplicate zero
  one = tensorReplicate one
  xs ~+~ ys = map (uncurry (~+~)) $ liftA2 xs ys
  xs ~*~ ys = map (uncurry (~*~)) $ liftA2 xs ys





  -- probably can be defined for arbitrary tensors, but it wasn't clear how to pattern match on `shape` in `Tensor shape`
-- {n : Nat} -> Applicative (Tensor [n]) where
--   pure x = TS (replicate n (TZ x))
--   fs <*> xs = map (uncurry ($)) $ liftA2 fs xs 


-- The point of this construction is to be able to easily create tensors using lists, without needing to use the inductive form requiRig `TZ` and `TS`. 
public export
Array : (shape : Vect rank Nat) -> (dtype : Type) -> Type
Array []        a = a
Array (m :: ms) a = Vect m (Array ms a)

public export
fromArray : {xs : Vect rank Nat} -> Array xs a -> Tensor xs a
fromArray {xs = []} y = TZ y
fromArray {xs = (_ :: _)} y = TS (fromArray <$> y)

{-
Machinery for indexing tensors
Allows us to write `indexTensor` below, and get following functionality
- example with indexTensor (tensor of shape 3 ,4 ) (2, 3) = val at that point
- example with indexTensor (tensor of shape 3 ,4 ) (10, 7) = can't even compile

-- Given a tensor `Tensor [3, 4] Double` this allows us to index one of its elements, and provide a compile-time guarantee that we won't be out of bounds
-}
public export
data IndexT : (shape : Vect n Nat) -> Type where
  Nil  : IndexT []
  (::) : Fin m -> IndexT ms -> IndexT (m :: ms)

public export
Show (IndexT shape) where
  show Nil = ""
  show (i :: is) = show i ++ ", " ++ show is

indexToShape : {n : Nat}
    -> {shape : Vect n Nat}
    -> IndexT shape -> Vect n Nat
indexToShape [] = []
indexToShape (s :: ss) = finToNat s :: indexToShape ss

-- Couterpart of 'index' for Vectors
public export
indexTensor : (index : IndexT shape)
            -> Tensor shape a
            -> a
indexTensor [] (TZ val) = val
indexTensor (indHere :: restOfIndex) (TS xs)
  = indexTensor restOfIndex (index indHere xs)


public export
infixr 9 @@
(@@) : Tensor shape a -> IndexT shape -> a
(@@) = flip indexTensor


(+++) : Vect n Nat -> Vect n Nat -> Vect n Nat
(+++) [] [] = []
(+++) (x :: xs) (y :: ys) = (x + y) :: ((+++) xs ys)

public export -- analogus to take in Data.Vect, but for Fin
takeFin : (s : Fin n) -> Vect n a -> Vect (finToNat s) a
takeFin FZ _ = []
takeFin (FS s) (x :: xs) = x :: takeFin s xs

public export --
takeTensor : (slice : IndexT shape)
          -> Tensor shape a
          -> Tensor (indexToShape slice) a
takeTensor [] (TZ val) = TZ val
takeTensor (s :: ss) (TS xs) = TS $ (takeTensor ss) <$> takeFin s xs


reshapeTensor : Tensor shape a
              -> (newShape : Vect n Nat)
              -> {auto prf : prod shape = prod newShape}
              -> Tensor newshape a
reshapeTensor t newShape = ?reshapeTensor_rhs

public export
toList : Tensor shape a -> List a
toList = foldr (::) []



matMul' : (m : Tensor [i, j] Double)
        -> (n : Tensor [j, k] Double) 
        -> Tensor [i, k] Double
matMul' m n = ?matMul'_rhs




---------------
--- Examples
---------------

t1 : Tensor [3, 4] Double
t1 = fromArray $ [ [0, 1, 2, 3]
                 , [4, 5, 6, 7]
                 , [8, 9, 10, 11]]


-- Do we need a constraint that all elements of shape are non-zero?
tTest : Tensor [0, 0] Double
tTest = TS ?ooo

-- With tensors that have a zero in them, we can't index into them since Fin - has no inhabitants
tTest2 : Tensor [0, 2] Double
tTest2 = TS ?oooo

d : Double
d = t1 @@ [1, 2]

tt : Tensor [1, 2] Double
tt = takeTensor [1, 2] t1


s : Vect 4 Nat
s = [1,2,3,4]

ss : Vect 2 Nat
ss = take 2 s
