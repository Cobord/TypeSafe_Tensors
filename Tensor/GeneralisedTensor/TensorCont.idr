module Tensor.GeneralisedTensor.TensorCont

import Data.Fin
import Data.Vect

import Data.Container.Definition
import Data.Tree

%hide Data.Vect.fromList

public export
data TensorC : (shape : Vect n Cont) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> TensorC [] dtype
    TS : ext c (TensorC cs dtype) -> TensorC (c :: cs) dtype

public export
ArrayC : (shape : Vect rank Cont) -> (dtype : Type) -> Type
ArrayC [] dtype = dtype
ArrayC (c :: cs) dtype = (ext c) (ArrayC cs dtype)

public export
fromArrayC : {shape : Vect rank Cont} -> ArrayC shape a -> TensorC shape a
fromArrayC {shape = []} x = TZ x
fromArrayC {shape = (c :: cs)} xs = TS $ extMap c fromArrayC xs

namespace IndexTC
  public export
  data IndexTC : (shape : Vect n Cont) -> Type where
    Nil  : IndexTC []
    (::) : {s : shp'} -> pos' s -> IndexTC ms
      -> IndexTC (((!>) shp' pos') :: ms)


  -- Given the extension of a container, and a position in its shape, return the value at that position
  public export
  indexCont : (e : ext ((!>) shp' pos') a) -> pos' (fst e) -> a
  indexCont ((_ ** payload)) = payload

  -- Couterpart of 'index' for Vectors
  public export
  indexTensor : (index : IndexTC shape)
              -> TensorC shape a
              -> a
  indexTensor [] (TZ val) = val
  indexTensor (indHere :: restOfIndex) (TS xs) = indexTensor restOfIndex (?indexTensor_rhs_1)
-- indexTensor [] (TZ val) = val
-- indexTensor (indHere :: restOfIndex) (TS xs)
--   = indexTensor restOfIndex (index indHere xs)

exCont : TensorC [ListCont] Double
exCont = fromArrayC (fromList [1,2,3,4])

exCont2 : TensorC [TreeNodeCont] Int
exCont2 = fromArrayC (fromTree (Node 1 (Leaf ()) (Leaf ())))


exCont3 : TensorC [TreeLeafCont, ListCont] Int
exCont3 = fromArrayC ?exCont3_rhs

exampleList : List' Int
exampleList = fromList [1,2,3,4]

val : Int
val = indexCont exampleList 3

-- Same as index from Data.Vect!
indexVect : Fin n -> Vect' n a -> a
indexVect x xs = indexCont xs x 


