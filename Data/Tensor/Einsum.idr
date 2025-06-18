module Data.Tensor.Einsum

import Data.Vect
import Decidable.Equality

import Data.Unique
import Data.Tensor.Tensor
import Data.Tensor.NaperianTensor
import Misc

{-
----------------------------------------
----- Docs:
----------------------------------------
Einstein Summation in Numpy: https://obilaniu6266h16.wordpress.com/2016/02/04/einstein-summation-in-numpy/
as_strided and sum is all you need: https://jott.live/markdown/as_strided
Basic guide to einsum: https://ajcr.net/Basic-guide-to-einsum/
Named Tensor Notation: https://arxiv.org/abs/2102.13196
Functional Einsum: https://www.cambridge.org/core/journals/journal-of-functional-programming/article/domainspecific-tensor-languages/19B95794B66C66E117DFCFC7A21E22D5

----------------------------------------
----- Einsum examples:
----------------------------------------
Transpose -> einsum("ij->ji")
Sum -> einsum("ij->") (equals to a fold!)
Column sum -> einsum("ij->j") 
Row sum -> einsum("ij->i")
Matrix-vector product -> einsum("ij,j->i")
Matrix-matrix product -> einsum("ij,jk->ik")
Dot product (Vector) -> einsum("i,i->")
Dot product (Matrix) -> einsum("ij,ij->")
Outer product -> einsum("i,j->ij")

x : Tensor [3, 3, 3] Double
Einsum "iii->i" x = view main diagonal
Einsum "iii->" x = trace (sum elements along diagonal)
Einsum "ijk->" x = sum all elements
Einsum "ijk->kji" x = transpose first and last axis

y : Tensor [3, 4] Double
Einsum "ii->" x = Invalid -> x is not of the right type
Einsum "ii->ii", x = Invalid -> output subscript included multiple times

Errors:
* Output subscript can't be included multiple times!
* Every output subscript has to appear in the input


----------------------------------------
----- Interface requirements
----------------------------------------
 Einsum seems to be formed out of a few operations:
 - Transpose -> Covered by Naperian
 - Sum -> Covered by Algebra
 - Dot product -> Covered by Applicative
 - Outer product -> ?
 - anything else?

----------------------------------------
----- Misc thoughts:
----------------------------------------

TODO perhaps we need Traversables to define Einsum for loops??
Traversable connection to Applicative:
https://x.com/khoiiiind/status/1925526689339379832

Product distributes over sum
Traversable distributes over Applicative


Is einsum abount binding?
 einsum("ij,jk->ik", M, N)

 Here we bind the tensor M to ij, and N to jk

Q: SCOPING: Why should scoping of Einsum names be local?
Should it perhaps be global instead?

Maybe it doesn't matter that we have Einsum "ii" (Tensor [3, 4] a),
perhaps if we want to contract, 3 and 4 should...what? be the same variable?


Should einsum work for generalised tensors?
----------------------------------------
----- Einsum algorithm:
----------------------------------------
In this example, fix:
shapeX = [100, 4, 5]
shapeY = [100, 5, 6]
x : Tensor shapeX Double
y : Tensor shapeY Double
Einsum "bij,bjk->ik" x y

Step 1: Parsing, variable binding, and error checking
We want to first collect all the unique axis names 'b', 'i', 'j', 'l' and store tham as a axisNames : UniqueVect m AxisName

So we want
"b" -> shapeX[0], shapeY[0]
"i" -> shapeX[1]
"j" -> shapeX[2], shapeY[1]
"k" -> shapeY[2]

AxisName -> List (xs : Vect n Nat, Fin n)

This is the part where we also check for errors, and inconsistent axis naming

Step 2) When we have this, there are many tensors we can get out, depending on what the output string and output tensor is




We onlOnly look at the input string and shapes, i.e. "bij,bjk" shapeX shapeY
and use it to do parsing/error checking, and performing of variable binding.

 -}

-- TODO am I unnecessarily focused on parsing in this file? Instead of more like computational content


||| The name for an axis is an arbitrary string, usually a single character
AxisName : Type
AxisName = String

public export
data EinsumInputTy : Type where
  InputTy : Vect n AxisName -> EinsumInputTy
  ProdTy : List EinsumInputTy -> EinsumInputTy

public export
uniqueLabels : EinsumInputTy -> UniqueList AxisName
uniqueLabels (InputTy labels) = fromVect labels
uniqueLabels (ProdTy inputs) = foldr (+++) Nil (uniqueLabels <$> inputs)

||| Output types should be dependent on the input!
data EinsumOutputTy : (inputLabels : Vect n AxisName) -> Type where
  OutputTy :
    (inputTy : EinsumInputTy) ->
    (outputLabels : UniqueListFrom AxisName (uniqueLabels inputTy)) ->
    (inputLabels : Vect n AxisName) ->
    EinsumOutputTy inputLabels


-- ||| Like InputType, but we only want unique names
-- OutputType : (n : Nat) -> Type
-- OutputType n = Unique n AxisName


-- data EinsumTy : Type where
--   InputTy : Vect n AxisName -> EinsumTy
--   OutputTy : UniqueVect n AxisName -> EinsumTy

-- data EinsumExpr :
--      (input : InputNames)
--   -> (output : UniqueVect n AxisName)
--   -> Type where
  --Empty : (out : OutputAxisNames o) -> EinsumExpr [] out

-- Einsum : Num a => List (Tensor shape a) -> 


aa : String
aa = "asdf"