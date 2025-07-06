module Data.Tensor.TensorUtils

import Data.List
import Data.Vect 
import Data.Nat -- Add import for Cast
-- import System.Random


import Data.Tensor.Tensor
import Data.Functor.Naperian -- needed for range
import Misc

public export
zeros : Num a => {shape : ApplV conts} -> Tensor shape a
zeros = tensorReplicate (fromInteger 0)

public export
zeros' : Num a => {shape : Vect n Nat} -> Tensor' shape a
zeros' = tensorReplicate' (fromInteger 0)

public export
ones : Num a => {shape : ApplV conts} -> Tensor shape a
ones = tensorReplicate (fromInteger 1)

public export
ones' : Num a => {shape : Vect n Nat} -> Tensor' shape a
ones' = tensorReplicate' (fromInteger 1)

public export
range : {n : Nat} -> Cast Nat a => Tensor' [n] a
range {n} = fromArray' $ cast . finToNat <$> positions {f=Vect n}

||| Number of elements in a cubical tensor
size : {shape : Vect n Nat} -> (0 _ : Tensor' shape a) -> Nat
size {shape} _ = prod shape


||| Flatten a non-cubical tensor into a list
||| Requires that we have Foldable on all the components
||| In general we won't know the number of elements of a non-cubical tensor at compile time
public export
flatten : {shape : ApplV conts} -> Foldable (Tensor shape) =>
  Tensor shape a -> List a
flatten = toList

||| Flatten a cubical tensor into a vector
||| This means we know the number of elements at compile time (it could be zero!)
||| TODO this is just a reshape!
flatten' : {shape : Vect n Nat} ->
  Tensor' shape a -> Vect (prod shape) a
flatten' t = ?todo

||| Maximum value in a tensor. Tensor might be empty.
max : {shape : ApplV conts} -> Foldable (Tensor shape) => Ord a =>
  Tensor shape a -> Maybe a
max = maxInList . flatten


-- Requires reshape
-- random : Random a => (shape : Vect n Nat) -> IO (Tensor' shape a)
-- random shape = ?random_rhs


-- public export
-- eye : Num a => Tensor [n, n] a
-- eye = ?eye_rhs