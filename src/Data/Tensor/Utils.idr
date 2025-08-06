module Data.Tensor.Utils

import Data.Nat -- Add import for Cast
import System.Random

import Data.Tensor.Tensor
import Misc


{-----------------------------------------------------------
{-----------------------------------------------------------
This file defines common tensor utility functions
Mirrors those found in numpy/pytorch, and includes:
* zeros
* ones
* range
* size
* flatten
* oneHot
and the corresponding container variants, when they exist.
-----------------------------------------------------------}
-----------------------------------------------------------}

namespace Zeros
  public export
  zerosA : Num a => {shape : List ContA} -> TensorA shape a
  zerosA = tensorReplicateA (fromInteger 0)
  
  public export
  zeros : Num a => {shape : List Nat} -> Tensor shape a
  zeros = ToCubicalTensor zerosA

namespace Ones
  public export
  onesA : Num a => {shape : List ContA} -> TensorA shape a
  onesA = tensorReplicateA (fromInteger 1)
  
  public export
  ones : Num a => {shape : List Nat} -> Tensor shape a
  ones = ToCubicalTensor onesA

namespace Range
  {----- 
  This one is interesting, as in the cubical case it's effectively a version of 'tabulate' from Naperian functors.
  The cubical version is implemented first, and it's possible that a more general version of rangeA can be defined for container based tensors, possibly by tabulating contents of each shape respectively
  -----}
  ||| Only works for cubical tensors
  public export
  range : {n : Nat} -> Cast Nat a => Tensor [n] a
  range {n} = fromConcrete $ cast . finToNat <$> positions {f=Vect n}

  ||| Here the type 'a' has to somehow be dependent on the shape?
  rangeA : TensorA ?whatShape ?whatType

namespace Size
  {----- 
  Can we measure the size of a tensor of containers?
  Likely need to impose an additiona constraint that the set of positions is enumerable
  -----}
  ||| Number of elements in a non-cubical tensor
  public export
  sizeA : {shape : List ContA} -> TensorA shape a -> Nat
  
  ||| Number of elements in a cubical tensor
  public export
  size : {shape : List Nat} -> (0 _ : Tensor shape a) -> Nat
  size {shape} _ = prod shape

namespace Flatten
  ||| Flatten a non-cubical tensor into a list
  ||| Requires that we have Foldable on all the components
  ||| In general we won't know the number of elements of a non-cubical tensor at compile time
  public export
  flattenA : Foldable (TensorA shape) => TensorA shape a -> List a
  flattenA = toList
  
  ||| Flatten a cubical tensor into a vector
  ||| Number of elements is known at compile time
  ||| Can even be zero, if any of shape elements is zero
  flatten : {shape : List Nat} ->
    Tensor shape a -> Vect (prod shape) a
  flatten t = ?flatten_rhs

  -- This was the old version with a strided implementation
  -- flatten : {shape : List Nat} ->
  --   Tensor shape a -> Vect (prod shape) a
  -- flatten (ToCubicalTensor (TS ex)) = extract <$> toVect ex

namespace Max
  ||| Maximum value in a tensor
  ||| Returns Nothing if the tensor is empty
  maxA : Foldable (TensorA shape) => Ord a =>
    TensorA shape a -> Maybe a
  maxA = maxInList . flattenA
  
  ||| Maximum value in a cubical tensor
  ||| Not sure why I can't use 'FromCubicalTensor . maxA'?
  max : {shape : List Nat} -> Ord a =>
    Tensor shape a -> Maybe a
  max t = maxInList (tensorFoldr (::) [] (FromCubicalTensor t))
-- max t = let tt = maxA (FromCubicalTensor t) in ?max_rhs_1

  -- TODO Fix for strided
  -- max {shape = []} t = maxA (FromCubicalTensor t)
  -- max {shape = (s :: ss)} t = let tt = maxA (FromCubicalTensor t) in ?max_rhs_1
  -- maxA maxA . FromCubicalTensor  -- t = let tt = FromCubicalTensor t in maxA tt
  --maxA . FromCubicalTensor

namespace OneHot
  -- oneHotA : Num a => {c : Cont} -> (i : c .shp) -> TensorA [c] a

  public export
  oneHot : Num a => {n : Nat} ->
    (i : Fin n) -> Tensor [n] a
  oneHot i = (.~) (zeros {shape=[n]}) [i] 1 

-- TODO Fix for strided
-- public export
-- {shape : List Nat} -> Random a => Random (Tensor shape a) where
--   randomIO = map (fromArray . toArrayHelper) randomIO
--   
--   randomRIO (lo, hi) = do
--     let loFlat = flatten lo
--     let hiFlat = flatten hi
--     randomVect <- randomRIO (loFlat, hiFlat)
--     pure $ fromArray (toArrayHelper randomVect)
-- 
-- random : Random a => (shape : List Nat) -> IO (Tensor shape a)
-- random shape = randomIO

-- public export
-- eye : Num a => TensorA [n, n] a
-- eye = ?eye_rhs