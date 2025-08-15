module Data.Tensor.Utils

import Data.Nat -- Add import for Cast
import System.Random

import Data.Tensor.Tensor
import Data.Container.SubTerm
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
  ||| Separate implementation for the case of one vs two arguments
  ||| This allows the typechecker to more easily match the right implementation at call sites, as with only TwoArg implementation the following doesn't compile:
  ||| a = Tensor [6] Double
  ||| a = arange
  ||| Otoh, we preclude calling this without a type specified
  namespace OneArg
    ||| A range of numbers [0, stop>
    public export
    arange : {stop : Nat} ->
      Cast Nat a => Tensor [stop] a
    arange {stop} = fromConcrete $
      (cast . finToNat) <$> positions {f=Vect (stop)}

  namespace TwoArgs
    ||| A range of numbers [start, stop>
    public export
    arange : {default 0 start : Nat} -> {stop : Nat} ->
      Cast Nat a => Tensor [minus stop start] a
    arange {start} {stop} = fromConcrete $
      (cast . (+start) . finToNat) <$> positions {f=Vect (minus stop start)}

  ||| Here the type 'a' has to somehow be dependent on the shape?
  rangeA : TensorA ?whatShape ?whatType

namespace Flip
  ||| Reverse a tensor along a given axis
  public export
  flip : (axis : Fin (length shape)) -> Tensor shape a -> Tensor shape a

namespace Size
  {----- 
  Can we measure the size of a tensor of containers?
  Likely need to impose an additional constraint that the set of positions is enumerable
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


namespace Triangular

  public export
  triABool : {c : ContA} -> (ip : InterfaceOnPositions MOrd (GetC c)) =>
    (sh : c.shp) -> TensorA [c, c] Bool
  triABool {ip = PosInterface {p}} sh
    = let cPositions = positions {sh=sh}
          pp : MOrd (c.pos sh) := p sh
      in outerAWithFn (flip isSubTerm) cPositions cPositions

  public export
  triA : Num a => {c : ContA} -> (ip : InterfaceOnPositions MOrd (GetC c)) =>
    (sh : c.shp) -> TensorA [c, c] a
  triA sh = fromBool <$> triABool sh

  public export
  triBool : {n : Nat} -> Tensor [n, n] Bool
  triBool = ToCubicalTensor $ triABool ()


  ||| A matrix with ones below the diagonal, and zeros elsewhere
  ||| Analogous to numpy.tri
  public export
  tri : Num a => {n : Nat} -> Tensor [n, n] a
  tri = fromBool <$> triBool

  ||| Lower triangular part of a matrix
  ||| The upper triangular part is set to zero
  ||| Analogous to numpy.tril
  public export
  lowerTriangular : Num a => {n : Nat} -> Tensor [n, n] a -> Tensor [n, n] a
  lowerTriangular = (* tri)

namespace Random
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