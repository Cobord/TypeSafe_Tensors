module Tensor.CubicalTensor.TensorView

import Data.Vect
import Data.Fin.Arith

import Tensor.CubicalTensor.Tensor
import Data.Rig


-- This only works for cube-shaped tensors, and not the generalised tensors one can start developing
-- But that's fine, because reshape only works for cube-shaped tensors
public export
record TensorView (shape : Vect n Nat) (dtype : Type) where
    constructor MkTensorView
    flatData : Vect (prod shape) dtype
 
{-
For a shape of 2 x 3 x 5 tensor = 30 positions (prod shape)
Indexing at [1, 0, 4] means indexing in the 2nd matrix, 1st row, 4th column:
- - - - -
- - - - -
- - - - -

- - - x -
- - - - -
- - - - -

Let shape = [2, 3, 5]
Let index = [1, 0, 4]
Ordered in a sequence, this means 1 * (3 * 5) + 0 * 5 + 4 = 19.
In other words, index[0] * (prod shape[1..]) + index[1] * (prod shape[2..]) + ... + index[n-1] * (prod shape[n..]) + index[n]

-}

a : Vect 10 Int
a = fromList [1..10]


-- this is wrong?
cc : (shape : Vect n Nat) -> (i : IndexT shape) -> Nat
cc [] [] = 0
cc (s :: ss) (i :: is) = (finToNat i * (prod ss)) + cc ss is


aTensor : TensorView [10] Int
aTensor = MkTensorView a

prff : {a : Nat} -> LTE (S a) (S a)
prff {a = 0} = LTESucc LTEZero
prff {a = (S k)} = LTESucc prff

-- Here strides are in terms of number of elements, not bytes
indexCount : {shape : Vect n Nat} -> (i : IndexT shape) -> Fin (prod shape)
indexCount {shape = []} [] = 0
indexCount {shape = (s :: ss)} (i :: is)
  = let -- thisDim : Fin (S (prod ss))
        t : Nat = prod ss
        thisDim : Fin (S t) = natToFinLT t {prf=prff {a=t}}
        -- thisDimMul = thisDim Data.Fin.Arith.(*) i
        -- rest : Fin (prod ss)
        rest = indexCount is
        -- We can turn thisDim into a Fin
        -- ttt = rest + (natToFinLT tt)
    in ?llll
  
  
indexTensorView : {shape : Vect n Nat}
  -> (i : IndexT shape)
  -> TensorView shape dtype
  -> dtype
indexTensorView i (MkTensorView flatData) = index (indexCount i) flatData



reshape : TensorView shape dtype
  -> (newShape : Vect newShapeLength Nat)
  -> {auto prf : prod shape = prod newShape}
  -> TensorView newShape dtype




