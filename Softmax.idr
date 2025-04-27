module Softmax

import Data.Vect
import Data.Vect.Elem

import Tensor.ContainerTensor.Tensor
import ApplicativeLinAlg
import Algebra
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

softmax' : {shape : ApplV conts}
  -> Fractional a => Exp a => Tensor shape a -> Tensor shape a
softmax' t = let exps = exp <$> t
             in exps <&> ?softmax'_rhs

 
softmaxVect : {n : Nat} -> Vect n Double -> Vect n Double
softmaxVect = softmax

softmaxTreeLeaf : BTreeLeaf Double -> BTreeLeaf Double
softmaxTreeLeaf = softmax {f=BTreeLeaf}

softmaxTreeNode : BTreeNode Double -> BTreeNode Double
softmaxTreeNode = softmax {f=BTreeNode}



-- namedSoftmax : {axis : Type -> Type}
--   -> {shape : Vect n ApplF} -> {a : Type}
--   -> Functor axis
--   => Elem axis shape
--   -> Tensor shape a
--   -> Tensor shape a
-- namedSoftmax {shape = []} axis t impossible -- can't be in vector if vector empty
-- namedSoftmax {shape = (axis :: ss)} Here (GTS x) = GTS (?sm <$> x)
-- namedSoftmax {shape = (s :: ss)} (There later) (GTS x) = GTS ?namedSoftmax_rhs_4
