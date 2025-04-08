module Softmax

import Data.Vect
import Data.Vect.Elem

import Tensor
import GenTensor

import ApplicativeLinAlg
import Tree
import Rig

interface Exp a where
  exp : a -> a

public export
Exp Double where
  exp = Prelude.exp

public export
softmax : {f : Type -> Type}
  -> (Functor f, Algebra f a, Fractional a, Exp a) => f a -> f a
softmax {f} xs = let exps = exp <$> xs
                 in exps <&> (/ reduce exps)
 
softmaxVect : {n : Nat} -> Vect n Double -> Vect n Double
softmaxVect = softmax

softmaxTreeLeaf : BinTreeLeafOnly Double -> BinTreeLeafOnly Double
softmaxTreeLeaf = softmax {f=BinTreeLeafOnly}

softmaxTreeNode : BinTreeNodeOnly Double -> BinTreeNodeOnly Double
softmaxTreeNode = softmax {f=BinTreeNodeOnly}



namedSoftmax : {axis : Type -> Type}
  -> {shape : Vect n (Type -> Type)} -> {a : Type}
  -> Functor axis
  => Elem axis shape
  -> GenTensor shape a
  -> GenTensor shape a
namedSoftmax {shape = []} axis t impossible -- elem can't be in vector if vector is empty
namedSoftmax {shape = (axis :: ss)} Here (GTS x) = GTS (?sm <$> x)
namedSoftmax {shape = (s :: ss)} (There later) (GTS x) = GTS ?namedSoftmax_rhs_4
