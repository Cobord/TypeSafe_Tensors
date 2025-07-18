module Data.Tensor.TensorUtils

import Data.List
import Data.Vect 
import Data.Nat -- Add import for Cast
-- import System.Random


import Data.Tensor.Tensor
import Data.Functor.Naperian -- needed for range
import Misc

public export
zerosA : Num a => {shape : ApplContList conts} -> TensorA shape a
zerosA = tensorReplicateA (fromInteger 0)

public export
zeros : Num a => {shape : List Nat} -> Tensor shape a
zeros = tensorReplicate (fromInteger 0)

public export
onesA : Num a => {shape : ApplContList conts} -> TensorA shape a
onesA = tensorReplicateA (fromInteger 1)

public export
ones : Num a => {shape : List Nat} -> Tensor shape a
ones = tensorReplicate (fromInteger 1)

public export
range : {n : Nat} -> Cast Nat a => Tensor [n] a
range {n} = fromArray' $ cast . finToNat <$> positions {f=Vect n}

||| Number of elements in a cubical tensor
size : {shape : List Nat} -> (0 _ : Tensor shape a) -> Nat
size {shape} _ = prod shape


||| Flatten a non-cubical tensor into a list
||| Requires that we have Foldable on all the components
||| In general we won't know the number of elements of a non-cubical tensor at compile time
public export
flatten : {shape : ApplContList conts} -> Foldable (TensorA shape) =>
  TensorA shape a -> List a
flatten = toList

||| Flatten a cubical tensor into a vector
||| This means we know the number of elements at compile time (it could be zero!)
||| TODO this is just a reshape!
flatten' : {shape : List Nat} ->
  Tensor shape a -> Vect (prod shape) a
flatten' t = ?todo

||| Maximum value in a tensor. TensorA might be empty.
max : {shape : ApplContList conts} -> Foldable (TensorA shape) => Ord a =>
  TensorA shape a -> Maybe a
max = maxInList . flatten


-- Requires reshape
-- random : Random a => (shape : Vect n Nat) -> IO (Tensor shape a)
-- random shape = ?random_rhs


-- public export
-- eye : Num a => TensorA [n, n] a
-- eye = ?eye_rhs