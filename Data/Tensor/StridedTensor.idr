module Data.Tensor.StridedTensor

import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers
import Data.Fin.Arith

import Data.Tensor
import Misc

{-
Need to compute stride-based functionality for:
 * Slice
 * Take
 * Transpose
 * Show
 * Linear algebra operations

Need to fix automatic flattening for TensorA for contraction operations
 -}


||| With a flat Tensor representation, we want to take the product of axis sizes
public export
NatsToVect : (shape : List Nat) -> ApplC
NatsToVect shape = NatToVect (prod shape)

public export
FlatStorage : (shape : List Nat) -> ApplContList [NatsToVect shape]
FlatStorage shape = [Vect (prod shape)]

public export
natsToFinProd : (shape : List Nat) -> Type
natsToFinProd shape = Fin (prod shape)

public export
CubicalTensorCont : (shape : List Nat) -> Cont
CubicalTensorCont shape = (_ : Unit) !> (natsToFinProd shape)

public export
cubicalTensorToFlat : {shape : List Nat} ->
  ComposeContainers [NatsToVect shape] =%> 
  CubicalTensorCont shape
cubicalTensorToFlat {shape = []} = constUnit <%! (\(() <| _), _ => (FZ ** ()))
cubicalTensorToFlat {shape = (s :: ss)}
  = constUnit <%! (\(() <| _), ieva => (ieva ** ()))
  

public export
flatToCubicalTensor : {shape : List Nat} ->
  CubicalTensorCont shape =%> 
  ComposeContainers [NatsToVect shape]
flatToCubicalTensor {shape = []} = (\_ => EmptyExt) <%! (\_, _ => FZ)
flatToCubicalTensor {shape = (s :: ss)}
  = (\_ => EmptyExt) <%! (\(), (cp ** ()) => cp)

-- public export
-- cubicalTensorProdNat : {shape : List Nat} ->
--   ComposeContainers (NatToVect <$> shape) =%> 
--   CubicalTensorCont shape
-- cubicalTensorProdNat {shape = []} = constUnit <%! const2Unit
-- cubicalTensorProdNat {shape = (_ :: _)}
--   = constUnit <%! (\(() <| ind), (fs, rst) =>
--     (fs ** let (_ <%! bw) = cubicalTensorProdNat
--            in bw (ind fs) rst))

public export
dLensProductReshape : {oldShape, newShape : List Nat} ->
  {auto prf : prod oldShape = prod newShape} ->
  CubicalTensorCont oldShape =%> CubicalTensorCont newShape
dLensProductReshape {prf}
  = constUnit <%! (\_ => rewrite prf in id)

-- public export
-- prodNatToCubicalTensor : {shape : List Nat} ->
--   CubicalTensorCont shape =%> 
--   ComposeContainers (NatToVect <$> shape)
-- prodNatToCubicalTensor {shape = []} = constUnit <%! const2Unit
-- prodNatToCubicalTensor {shape = (s :: ss)}
--   = let (fwss <%! bwss) = prodNatToCubicalTensor {shape=ss}
--     in (\_ => () <| \_ => fwss ()) <%! (\(), (cp ** rst) => (cp, bwss () rst))





public export
record TensorView (shape : List Nat) (dtype : Type) where
    constructor MkTensorView
    flatData : Vect (prod shape) dtype

namespace CubicalIndex
  public export
  strides : (shape : List Nat) -> List Nat
  strides [] = []
  strides (s :: ss) = prod ss :: strides ss

  ||| If all elements of shape are non-zero, then the head of the strides is also non-zero
  public export
  stridesProofHeadNonZero : {shape : List Nat} ->
    {auto prf : All IsSucc shape} ->
    {auto _ : NonEmpty (strides shape)} ->
    IsSucc (head (strides shape))
  stridesProofHeadNonZero {shape = (_ :: ss)} {prf = (_ :: ps)}
    = allSuccThenProdSucc ss
  
  ||| Index of a cubical tensor given a shape
  ||| This is 0-based indexing
  public export
  data IndexT : (shape : List Nat) -> Type where
    Nil  : IndexT []
    (::) : Fin m -> IndexT ms -> IndexT (m :: ms)

  ||| Maybe Index of a cubical tensor given a shape
  ||| Allows us to perform general slicing
  ||| This is 0-based indexing
  public export
  data MIndexT : (shape : List Nat) -> Type where
    MNil  : MIndexT []
    (:::) : Maybe (Fin m) -> MIndexT ms -> MIndexT (m :: ms)

  ||| Computes the shape of the tensor after the slicing
  ||| TODO this is not correct
  public export
  mIndexToShape : {shape : List Nat} -> MIndexT shape -> List Nat
  mIndexToShape {shape = []} MNil = []
  mIndexToShape {shape = (s :: ss)} (Nothing ::: is) = s :: mIndexToShape is
  mIndexToShape ((Just i) ::: is) = finToNat i :: mIndexToShape is
  
  ||| Given a shape and an index, compute the index in the flattened tensor
  public export
  indexCount : {shape : List Nat} -> {auto allNonZero : All IsSucc shape} ->
    IndexT shape -> Fin (prod shape)
  indexCount {shape = []} _ = FZ
  indexCount {shape = (s :: ss)} {allNonZero = (_ :: ps)} (i :: is)
    = let restCount = indexCount is
          restCountWeakened = weakenMultN s restCount
          
          strideHeadNonZero = stridesProofHeadNonZero {shape=(s :: ss)} 
          hereCount = shiftMul (head (strides (s :: ss))) i
      in addFinsBounded hereCount restCountWeakened

  public export
  indexTensor : {shape : List Nat} -> {auto allNonZero : All IsSucc shape} ->
    (t : Tensor shape a) ->
    (ind : IndexT shape) ->
    a
  indexTensor (ToCubicalTensor (TS v)) ind
    = extract $ index (indexCount ind) (toVect v)

  public export infixr 9 @@
  public export
  (@@) : {shape : List Nat} -> {auto allNonZero : All IsSucc shape} ->
    (t : Tensor shape a) ->
    (ind : IndexT shape) ->
    a
  (@@) = indexTensor


reshape : {oldShape : List Nat} -> {newShape : List Nat} ->
  {auto prf : prod newShape = prod oldShape} ->
  TensorView oldShape a ->
  TensorView newShape a
reshape {prf} (MkTensorView flatData) = MkTensorView (rewrite prf in flatData)


{-
Fix shape = [3, 4, 5]. This is 60 positions (prod shape). Three 4x5 matrices.
Let's study three examples of indexes into this shape.
- - - - -
- - - - -
- i - - -
- - - - k

- - - - -
- - - - -
- - - j -
- - - - -

- - - - -
- - - - -
- - - - -
- - - - -

Fix index k = [0, 3, 4]. This means indexing in the 1st matrix, 4th row, 5th column.
As flat data, the index of k=[0, 3, 4] can be computed as
k = 0 * (4 * 5)
  + 3 * (5)
  + 4 * 1
  = 19

Fix index i = [0, 2, 1]. This means indexing in the 1st matrix, 3rd row, 2nd column.
As flat data, this means
i = 0 * (4 * 5)
  + 2 * (5)
  + 1 * 1
  = 11

Fix index j = [1, 2, 3]. This means indexing in the 2nd matrix, 3st row, 4th column.
As flat data, this means indexing into the location given by 
j = 1 * (4 * 5 * 1)
  + 2 * (5 * 1)
  + 3 * 1
  = 33
-----------------------------------------------

Fix shape = [3, 4]. This is 12 positions.
- i - -
- - - -
- - - -

Fix index i = [0, 1]. This means indexing in the 1st row, 2nd column.
As flat data, this means
i = 0 * (4)
  + 1 * 1
  = 1


What all of these examples share in common?
Given shape : List Nat, the way we compute index is by taking a dot product of it with another vector computed *from* shape.
That other vector is called strides.

We now define the stride : Vect n Nat -> Vect n Nat function
-}

-- Here strides are in terms of number of elements, not bytes
public export
strides : (shape : Vect n Nat) -> Vect n Nat
strides [] = []
strides (s :: ss) = prod ss :: strides ss



{-
             0   1    2 
stride = 0   0   0    0
stride = 1   0   1    2
stride = 2   0   2    4
stride = 3   0   3    6
-}

-- ||| Note: (prod shape) can be zero. This means the argument (i : IndexT shape) can never be produced, as (prod shape) == 0 implies that one of the elements of shape is zero. This prevents us from being required to produce an uninhabited output type: Fin 0.
-- indexCount : (shape : List Nat) -> (i : IndexT shape) -> Fin (prod shape)
-- indexCount shape i
--   = let str = strides (fromList shape)
--     in ?indexCount_rhs


-- TODO this is technically quite inefficient since we recompute prod ss recursively
-- probably could use a helper function here?
-- bably could use a helper function here?
-- indexCount [] [] = 0
-- ind xCount (s :: ss) (i :: is) =
--     let ii : Fin s := i
--         pr : Nat := prod ss -- we want to turn this into Fin (prod ss)
--         tl : Fin (S (prod ss)) := natToFinLT (prod ss) {prf=reflexive}
--         -- prFin : Fin pr := natToFinLT (pred pr)
--         -- firstCompFin : Fin (finToNat i * pr)
--         --   := natToFinLT (finToNat i * pr) {n=finToNat i * pr}
--         restOfIndex : Fin (prod ss) := indexCount ss is  -- Fin 
--     in ?indexCount_rhs_2



{-
old:

indexCount [2, 3] : (index : IndexT [2, 3]) -> Fin 6
indexCount [2, 3] 


In other words, there should be a function
indexCount : (shape : Vect n Nat) -> (index : IndexT shape) -> Fin (prod shape)
indexCount shape index = index[0] * (prod shape[1..])
                       + index[1] * (prod shape[2..])
                       + ...
                       + index[n-1] * (prod shape[n..])
                       + index[n] * prod []

i.e.
indexCount [] [] = 0
indexCount (s :: ss) (i :: is) = i * (prod ss) + indexCount ss is
-----------------------------    ------------    ----------------
      Fin( prod(s :: ss))      Fin (s * prod ss) +  Fin (prod ss)

oooold
||| In simple terms, we want to do (i * str)
ddFin : {stride : Nat} ->
  {n : Nat} -> (i : Fin n) -> NonZero stride -> Fin (n * stride)
ddFin {n=0} FZ _ impossible
ddFin {n=0} (FS i) _ impossible
ddFin {n = (S n')} i (ItIsSucc {n=str})
  = let rl : (stride = (S str)) := %search
        strAsFin : Fin stride := natToFinLT str {prf=reflexive}
        pp : Fin (S (n' * str)) := i * strAsFin
    in ?ddFin_rhs_4
-- ddFin {n = (S n)} FZ (ItIsSucc {n=str}) = FZ
-- ddFin {n = (S n)} (FS i) (ItIsSucc {n=str})
--   = let rl : (stride = (S str)) := %search
--         strAsFin : Fin stride := natToFinLT str {prf=reflexive}
--         pp : Fin (S (n * str)) := (FS i) * strAsFin
--     in ?ddFin_rhs_4
-- 



-}