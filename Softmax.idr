module Softmax

import Data.Vect
import Data.Vect.Elem

import Data.Container.Definition
import Data.Container.Instances
import Tensor.ContainerTensor.Tensor
import ApplicativeLinAlg
import Algebra
import Tree
import Data.Rig
import Misc

public export
softmax : {f : Type -> Type}
  -> (Functor f, Algebra f a, Fractional a, Exp a) => f a -> f a
softmax {f} xs = let exps = exp <$> xs
                 in exps <&> (/ reduce exps)

softmaxVect : {n : Nat} -> Vect n Double -> Vect n Double
softmaxVect = softmax

softmaxTreeLeaf : BTreeLeaf Double -> BTreeLeaf Double
softmaxTreeLeaf = softmax {f=BTreeLeaf}

softmaxTreeNode : BTreeNode Double -> BTreeNode Double
softmaxTreeNode = softmax {f=BTreeNode}

--- Tensor softmax

softmax' : {i : Cont}
  -> Applicative (Ext i) => (allAlg : AllAlgebra [i] a)
  => Fractional a => Exp a
  => Tensor [i] a -> Tensor [i] a
softmax' t = let exps = exp <$> t
             in exps <&> (/ reduce exps)

-- -- This should be done by a more general map operation over a specific axis
-- public export
-- softmax1 : {s : Cont} -> {ss : ApplV conts} ->
--   Applicative (Ext s) =>
--   Fractional (Tensor ss a) =>
--   Exp (Tensor ss a) => 
--   (allAlgebra : AllAlgebra [s] (Tensor ss a)) =>
--   Tensor (s :: ss) a -> Tensor (s :: ss) a
-- softmax1 {allAlgebra} x
--    = let sm = softmax' {i=s} {a=(Tensor ss a)}
--          t = tensorMapFirstAxis {x=s, y=s} sm 
--     in ?fmft
             


-- softmaxVect' : {n : Nat} -> Tensor [VectCont n] Double -> Tensor [VectCont n] Double
-- softmaxVect' = softmax'
-- 
-- softmaxBTreeLeaf' : Tensor [BTreeLeafCont] Double -> Tensor [BTreeLeafCont] Double
-- softmaxBTreeLeaf' = softmax'
-- 
-- softmaxBTreeNode' : Tensor [BTreeNodeCont] Double -> Tensor [BTreeNodeCont] Double
-- softmaxBTreeNode' = softmax'
 



-- namedSoftmax : {axis : Type -> Type}
--   -> {shape : Vect n ApplF} -> {a : Type}
--   -> Functor axis
--   => Elem axis shape
--   -> Tensor shape a
--   -> Tensor shape a
-- namedSoftmax {shape = []} axis t impossible -- can't be in vector if vector empty
-- namedSoftmax {shape = (axis :: ss)} Here (GTS x) = GTS (?sm <$> x)
-- namedSoftmax {shape = (s :: ss)} (There later) (GTS x) = GTS ?namedSoftmax_rhs_4
