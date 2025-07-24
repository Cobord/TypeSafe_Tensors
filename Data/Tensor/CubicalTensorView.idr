module Data.Tensor.CubicalTensorView

import Data.Vect
import Data.Fin.Arith

import Data.Tensor.Tensor
import Misc

||| This only works for cubical tensors
||| This is okay, because reshape only works for cube-shaped tensors
public export
record TensorView (shape : Vect n Nat) (dtype : Type) where
    constructor ToCubicalTensorensorView
    flatData : Vect (prod shape) dtype

{-
Fix shape = [3, 4, 5]. This is 60 positions (prod shape). Three 4x5 matrices.
- - - - -
- - - - -
- i - - -
- - - - k

- - - - j
- - - - -
- - - - -
- - - - -

- - - - -
- - - - -
- - - - -
- - - - -

Fix index k = [0, 3, 4]. This means indexing in the 1st matrix, 4th row, 5th column.
As flat data, this means
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

Fix index j = [1, 0, 4]. This means indexing in the 2nd matrix, 1st row, 5th column.
As flat data, this means indexing into the location given by 
j = 1 * (4 * 5 * 1)
  + 0 * (5 * 1)
  + 4 * 1
  = 24
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
Given shape : Vect n Nat, the way we compute index is by taking a dot product of it with another vector computed *from* shape.
That other vector is called strides.
-}

||| Helper function for computing strides
||| On empty list it returns empty
||| On non-empty list it removes the first element, and reverses the rest
||| stridesHelp [3, 4, 5] = [1, 5, 4]
stridesHelp : (shape : List Nat) -> List Nat
stridesHelp [] = []
stridesHelp (x :: xs) =  [1] ++ reverse xs

||| Given a list of numbers, return a new list where each element is the product of all preceding ones
foldProd : List Nat -> List Nat
foldProd [] = []
foldProd (x :: xs) = x :: ((x*) <$> foldProd xs)


-- Shape = [3, 4, 5] -> Strides = [20, 5, 1]
-- Shape = [3, 4, 5, 6] -> Strides = [120, 30, 6, 1]
-- Shape = [3, 4] -> Strides = [4, 1]
-- Shape = [3] -> Strides = [1]
-- Here strides are in terms of number of elements, not bytes
strides : (shape : List Nat) -> List Nat
strides = reverse . foldProd . stridesHelp

||| 0-based indexing
public export
data IndexT : (shape : List Nat) -> Type where
  Nil  : IndexT []
  (::) : Fin m -> IndexT ms -> IndexT (m :: ms)

ddFin' : {n : Nat} ->
  (i : Fin (S n)) ->
  (stride : Nat) ->
  Fin (S (n * stride))
ddFin' i 0 = FZ
ddFin' i (S k) = rewrite multRightSuccPlus n k in i + ddFin' i k

||| Multiplies an index with a stride, i.e. i * stride, but bounded
||| Produces an index where each step is 'stride' sized
ddFin : {n : Nat} ->
  (i : Fin n) ->
  (stride : Nat) ->
  Fin (S ((pred n) * stride))
ddFin {n=0} FZ _ impossible
ddFin {n=0} (FS x) _ impossible
ddFin {n = (S k)} i stride = ddFin i stride

||| Given a shape and an index, compute the index in the flattened tensor
||| Example:
||| dotStr [3, 4, 5] [0, 1, 2] = 11 : Fin (60)
||| dotStr [3, 4, 5] [1, 0, 4] = 24 : Fin (60)
||| dotStr [3, 4] [0, 1] = 1
||| dotStr [3] [0] = 0
dotStr : {shape : List Nat} -> IndexT shape -> Fin (prod shape)
-- dotStr {shape} x with (strides shape)
--   dotStr {shape=[]} []                 | [] = 0
--   dotStr {shape=(s :: ss)} (is :: iss) | (st :: sts) = 
--     let amt : Fin (S ((pred s) * st)) := ddFin is st
--         rest : Fin (prod ss) := dotStr iss -- do we know prod ss = S ?n  ?
--         aa = Data.Fin.Arith.(+) amt
--     in ?dotStr_rhs


-- hmmm : (n : Nat) -> Fin m
-- hmmm n ?= natToFinLT n
-- Fin 3, Fin 4 -> Fin 12
-- 0, 1, 2
-- 0, 1, 2, 3
-- 0, 1, 2, 3, 4, 5, 6

{-
             0   1    2 
stride = 0   0   0    0
stride = 1   0   1    2
stride = 2   0   2    4
stride = 3   0   3    6
-}

||| Note: (prod shape) can be zero. This means the argument (i : IndexT shape) can never be produced, as (prod shape) == 0 implies that one of the elements of shape is zero. This prevents us from being required to produce an uninhabited output type: Fin 0.
indexCount : (shape : List Nat) -> (i : IndexT shape) -> Fin (prod shape)
indexCount shape i
  = let str = strides shape
    in ?indexCount_rhs


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