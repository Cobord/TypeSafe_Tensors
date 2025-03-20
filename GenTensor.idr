module GenTensor

import Data.Vect

import Tensor
import Tree

h : Vect 2 (Type -> Type)
h = [List, Tensor [2,3]]

public export
data GenTensor : (shape : Vect n (Type -> Type))
               -> (contentType : Type)
               -> Type where
    GTZ : (val : contentType) -> GenTensor [] contentType
    GTS : f (GenTensor ds contentType) -> GenTensor (f :: ds) contentType


Tensor' : (shape : Vect n Nat) -> Type -> Type
Tensor' shape = GenTensor (map Vect shape)

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