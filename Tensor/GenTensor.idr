module Tensor.GenTensor

import Data.Vect

import Tensor
import Tree

||| Generalised tensors
||| For storing not necessarily cube-like structures
public export
data GenTensor : (shape : Vect n (Type -> Type))
               -> (dtype : Type)
               -> Type where
    GTZ : (val : dtype) -> GenTensor [] dtype
    GTS : f (GenTensor ds dtype) -> GenTensor (f :: ds) dtype

%name GenTensor t, u, v


data AllShow : (shape : Vect n (Type -> Type))
             -> (dtype : Type)
             -> Type where
  NilShow : Show a => AllShow [] a
  ConsShow : Show (f (AllShow fs dtype)) => AllShow (f :: fs) dtype

-- findShow : AllShow shape dtype -> GenTensor shape dtype -> Show dtype
-- findShow NilShow (GTZ val) = 
-- findShow ConsShow t = ?findShow_rhs_1

-- public export
-- {shape : Vect n (Type -> Type)} -> (allShow : AllShow shape a) => Show (GenTensor shape a) where
--   show t = let xt = allShow in ?sss
  -- show {shape = []} (GTZ val) = show val
  -- show {shape = (f :: fs)} (GTS fx) = ?asdf_2
  -- show (GTZ x) = show x
  -- show (GTS xs) = ?asdf

public export
{shape : Vect n (Type -> Type)} -> Eq a => Eq (GenTensor shape a) where
    (GTZ t) == (GTZ u) = t == u
    (GTS ts) == (GTS us) = ?lafl_2


-- This recovers usual tensors in Tensor.Tensor
Tensor' : (shape : Vect n Nat) -> Type -> Type
Tensor' shape = GenTensor (Vect <$> shape)

h : Vect 2 (Type -> Type)
h = [List, Tensor [2,3]]

rt : Tensor' [2, 3] Double
rt = ?ein

t0 : GenTensor [] Double
t0 = GTZ 3

t1 : GenTensor [List] Double
t1 = GTS [GTZ 2, GTZ 3, GTZ 17]

t2 : GenTensor [List, Vect 2] Double
t2 = GTS [GTS [GTZ 14, GTZ 9]]

t3 : GenTensor [BinTreeLeafOnly, Vect 2] Double
t3 = GTS ?eoo 

-- ttt : Tensor' [3, 4] Double
-- ttt = fromArray [ [0, 1, 2, 3]
--                 , [4, 5, 6, 7]
--                 , [8, 9, 10, 11]]