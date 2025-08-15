module Architectures.Softmax

import Data.Tensor

public export
softmaxA : {i : ContA} -> Fractional a => Exp a =>
  (allAlg : AllAlgebra [i] a) =>
  {default 1 temperature : a} ->
  TensorA [i] a -> TensorA [i] a
softmaxA {temperature} t
  = let exps : TensorA [i] a := exp <$> (t <&> (/ temperature))
    in exps <&> (/ (reduce exps))


||| Softmax for a cubical 1D tensor, i.e. a vector
public export
softmax : {i : Nat} -> {a : Type} -> Fractional a => Exp a => 
  {default 1 temperature : a} ->
  Tensor [i] a -> Tensor [i] a
softmax {temperature} = ToCubicalTensorMap (softmaxA {temperature=temperature})


public export
softmaxBinTreeLeaf : {a : Type} -> Fractional a => Exp a =>
  TensorA [BinTreeLeaf] a -> TensorA [BinTreeLeaf] a
softmaxBinTreeLeaf = softmaxA

public export
softmaxBinTreeNode : {a : Type} -> Fractional a => Exp a =>
  TensorA [BinTreeNode] a -> TensorA [BinTreeNode] a
softmaxBinTreeNode = softmaxA


-- public export
-- softmax : {f : Type -> Type}
--   -> (Functor f, Algebra f a, Fractional a, Exp a) => f a -> f a
-- softmax {f} xs = let exps = exp <$> xs
--                  in exps <&> (/ reduce exps)
-- 
-- softmaxVect : {n : Nat} -> Vect n Double -> Vect n Double
-- softmaxVect = softmax
-- 
-- softmaxTreeLeaf : BinTreeLeaf Double -> BinTreeLeaf Double
-- softmaxTreeLeaf = softmax {f=BinTreeLeaf}
-- 
-- softmaxTreeNode : BinTreeNode Double -> BinTreeNode Double
-- softmaxTreeNode = softmax {f=BinTreeNode}

--- TensorA softmax

-- -- This should be done by a more general map operation over a specific axis
-- public export
-- softmax1 : {s : Cont} -> {ss : ContAontList conts} ->
--   Applicative (Ext s) =>
--   Fractional (TensorA ss a) =>
--   Exp (TensorA ss a) => 
--   (allAlgebra : AllAlgebra [s] (TensorA ss a)) =>
--   TensorA (s :: ss) a -> TensorA (s :: ss) a
-- softmax1 {allAlgebra} x
--    = let sm = softmax' {i=s} {a=(TensorA ss a)}
--          t = tensorMapFirstAxis {x=s, y=s} sm 
--     in ?fmft
             


-- softmaxVect' : {n : Nat} -> TensorA [Vect n] Double -> TensorA [Vect n] Double
-- softmaxVect' = softmax'
-- 
-- softmaxBinTreeLeaf' : TensorA [BinTreeLeaf] Double -> TensorA [BinTreeLeaf] Double
-- softmaxBinTreeLeaf' = softmax'
-- 
-- softmaxBinTreeNode' : TensorA [BinTreeNode] Double -> TensorA [BinTreeNode] Double
-- softmaxBinTreeNode' = softmax'
 


-- TODO
-- namedSoftmax : {axis : Type -> Type}
--   -> {shape : Vect n ApplF} -> {a : Type}
--   -> Functor axis
--   => Elem axis shape
--   -> TensorA shape a
--   -> TensorA shape a
-- namedSoftmax {shape = []} axis t impossible -- can't be in vector if vector empty
-- namedSoftmax {shape = (axis :: ss)} Here (GTS x) = GTS (?sm <$> x)
-- namedSoftmax {shape = (s :: ss)} (There later) (GTS x) = GTS ?namedSoftmax_rhs_4
