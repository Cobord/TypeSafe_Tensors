module Tensor.Einsum

import Data.Vect

import Tensor.Tensor


{-
What do we want of einsum?

Transpose -> einsum("ij->ji")
Sum -> einsum("ij->") (equals to a fold!)
Column sum -> einsum("ij->j") 
Row sum -> einsum("ij->i")
Matrix-vector product -> einsum("ij,j->i")
Matrix-matrix product -> einsum("ij,jk->ik")
Dot product (Vector) -> einsum("i,i->")
Dot product (Matrix) -> einsum("ij,ij->")

Outer product -> einsum("i,j->ij")


https://obilaniu6266h16.wordpress.com/2016/02/04/einstein-summation-in-numpy/

Is einsum abount binding?
 einsum("ij,jk->ik", M, N)

 Here we bind the tensor M to ij, and N to jk

 Einsum seems to be formed out of a few operations:
 - Transpose
 - Sum
 - Dot product
 - Outer product

 Is there anything else?
-}

AxisName : Type
AxisName = String

AxisNames : Nat -> Type
AxisNames n = Vect n AxisName

data EinsumExpr : Vect n ((m : Nat ** AxisNames m)) -> AxisNames i -> Type where
  Empty : (out : AxisNames i) -> EinsumExpr [] out

-- Einsum : Rig a => List (Tensor shape a) -> 