module Tensor

import Data.Fin
import Data.Vect
import Misc

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
data Tensor : (shape : Vect n Nat) -> (contentType : Type) -> Type where
    TZ  : (val : contentType) -> Tensor [] contentType
    TS : Vect d (Tensor ds contentType) -> Tensor (d :: ds) contentType

public export
Functor (Tensor shape) where
  map f (TZ x) = TZ (f x)
  map f (TS xs) = TS (map (map f) xs)

public export
Foldable (Tensor shape) where
  foldr f z (TZ x) = f x z 
  foldr f z (TS xs) = foldr (\t, acc => foldr f acc t) z xs 

public export
Show a => Show (Tensor shape a) where
  show (TZ x) = show x
  show (TS xs) = show xs

public export
Eq a => Eq (Tensor shape a) where
  (TZ v1) == (TZ v2) = v1 == v2
  (TS xs) == (TS ys) = xs == ys



-- This equality doesn't hold as stated because:
-- Tensor (n :: ns) a is a tensor of shape (n :: ns) with elements of type a
-- Tensor [n] (Tensor ns a) would be a tensor of shape [n] with elements of type (Tensor ns a)
-- 
-- We can define functions that convert between these representations:

public export
toNestedTensor : {n : Nat} -> {ns : Vect m Nat} -> {a : Type} -> 
                Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
toNestedTensor (TS vs) = TS (map TZ vs)

public export
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

public export
Scalar : (contentType : Type) -> Type
Scalar contentType = Tensor [] contentType

public export
Vector : (size : Nat) -> (contentType : Type) -> Type
Vector size contentType = Tensor [size] contentType

public export
Matrix : (rows, cols : Nat) -> (contentType : Type) -> Type
Matrix rows cols contentType = Tensor [rows, cols] contentType

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

  -- probably can be defined for arbitrary tensors, but it wasn't clear how to pattern match on `shape` in `Tensor shape`
-- {n : Nat} -> Applicative (Tensor [n]) where
--   pure x = TS (replicate n (TZ x))
--   fs <*> xs = map (uncurry ($)) $ liftA2 fs xs 


-- The point of this construction is to be able to easily create tensors using lists, without needing to use the inductive form requiring `TZ` and `TS`. 
public export
Array : (shape : Vect rank Nat) -> (contentType : Type) -> Type
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
data IndexT : (shape : Vect n Nat) -> Type where
  Nil  : IndexT []
  (::) : Fin m -> IndexT ms -> IndexT (m :: ms)

indexToShape : {n : Nat}
    -> {shape : Vect n Nat}
    -> IndexT shape -> Vect n Nat
indexToShape [] = []
indexToShape (s :: ss) = finToNat s :: indexToShape ss

-- Couterpart of 'index' for Vectors
indexTensor : (index : IndexT shape)
            -> Tensor shape a
            -> a
indexTensor [] (TZ val) = val
indexTensor (indHere :: restOfIndex) (TS xs)
  = indexTensor restOfIndex (index indHere xs)

(+++) : Vect n Nat -> Vect n Nat -> Vect n Nat
(+++) [] [] = []
(+++) (x :: xs) (y :: ys) = (x + y) :: ((+++) xs ys)

  -- Counterpart of 'take' for Vectors
takeTensor : {extra : Vect n Nat}
           -> (slice : Vect n Nat)
           -> Tensor ((+++) slice extra) a
           -> Tensor slice a
takeTensor {extra = []} [] (TZ val) = TZ val
takeTensor {extra = (e :: es)} (s :: ss) (TS xs) = TS $ (takeTensor ss) <$> take s xs 

-- TODO should this be done with IndexT or with nats, like it's done in take?
takeTensor' : (slice : IndexT shape)
           -> Tensor shape a
           -> Tensor (indexToShape slice) a
takeTensor' [] (TZ val) = TZ val
takeTensor' (s :: ss) (TS xs) = TS $ map (takeTensor' ss) (Data.Vect.take (finToNat s) (?bb xs))


-- rwrt : (d : Nat) -> (s : Fin d) -> (m : Nat ** d = (finToNat s) + m)
-- rwrt 0 s impossible
-- rwrt (S k) FZ = ( ** ?aa)
-- rwrt (S k) (FS x) = ?rwrt_rhs_3

reshapeTensor : Tensor shape a
              -> (newShape : Vect n Nat)
              -> prod shape = prod newShape
              -> Tensor newshape a
reshapeTensor x newShape prf = ?reshapeTensor_rhs


matMul' : (m : Tensor [i, j] Double)
        -> (n : Tensor [j, k] Double) 
        -> Tensor [i, k] Double


{-
What do we want of einsum?

es "aab" Tensor [i,i,i] should sum over the first two axes
-}