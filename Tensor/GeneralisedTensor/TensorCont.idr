module Tensor.GeneralisedTensor.TensorCont

import Data.Fin
import Data.Vect

import Data.Container.Definition
import Data.Tree

%hide Data.Vect.fromList

public export
data TensorC : (shape : Vect n Cont) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> TensorC [] dtype
    TS : Ext c (TensorC cs dtype) -> TensorC (c :: cs) dtype

%name TensorC t, t'

public export
Functor (TensorC shape) where
  map f (TZ val) = TZ $ f val
  map f (TS xs) = TS $ (map f) <$> xs

public export
ArrayC : (shape : Vect rank Cont) -> (dtype : Type) -> Type
ArrayC [] dtype = dtype
ArrayC (c :: cs) dtype = (Ext c) (ArrayC cs dtype)

public export
fromArrayC : {shape : Vect rank Cont} -> ArrayC shape a -> TensorC shape a
fromArrayC {shape = []} x = TZ x
fromArrayC {shape = (c :: _)} xs = TS $ fromArrayC <$> xs


namespace IndexTC

  -- Given the Extension of a container, and a position in its shape, return the value at that position
  -- Couterpart of 'index' for Vectors
  public export
  indexCont : (e : Ext ((!>) shp' pos') a) -> pos' (shapeExt e) -> a
  indexCont (_ <| payload) = payload

  ||| Machinery for indexing into a TensorC
  ||| Does this depend only on the shape, or also the actual container?
  public export
  data IndexTC : (shape : Vect n Cont) -> (t : TensorC shape dtype) -> Type where
    Nil : {val : dtype} -> IndexTC [] (TZ val)
    (::) : {e : Ext ((!>) shp' pos') (TensorC cs dtype)} -> (p : pos' (shapeExt e)) -> IndexTC cs (indexCont e p) -> IndexTC ((!>) shp' pos' :: cs) (TS e)
    -- can technically erase the arguments in implicit brackets?

  -- public export
  -- data IndexTC : (shape : Vect n Cont) -> Type where
  --   Nil  : IndexTC []
  --   (::) : {g : shp'} -> pos' g -> IndexTC ms
  --     -> IndexTC (((!>) shp' pos') :: ms)

  -- Here it must hold that the shape at indHere : pos' s is the smae shape as that in the TensorC? Perhaps we need to swap the order of arguments here
  public export
  indexTensorC : (t : TensorC shape a)
              -> (index : IndexTC shape t)
              -> a
  indexTensorC (TZ val) [] = val
  indexTensorC (TS xs) (i :: is) = indexTensorC (indexCont xs i) is 

||| This recovers usual tensors in Tensor.Tensor
public export
TensorC' : (shape : Vect n Nat) -> Type -> Type
TensorC' shape = TensorC $ VectCont <$> shape

arr1 : TensorC' [2, 3] Int
arr1 = fromArrayC $ ?ooaf

indexArr1 : Int
indexArr1 = indexTensorC arr1 ?givm

exCont : TensorC [ListCont] Double
exCont = fromArrayC (fromList [1,2,3,4])

exCont2 : TensorC [TreeNodeCont, ListCont] Int
exCont2 = fromArrayC $ fromTree $ Node (fromList [1,2,3,4,5]) Leaf' Leaf'

indexCont2 : Int
indexCont2 = indexTensorC exCont2 [Root, 4]


exCont3 : TensorC [TreeLeafCont, ListCont] Int
exCont3 = fromArrayC ?exCont3_rhs

exampleList : List' Int
exampleList = fromList [1,2,3,4]

val : Int
val = indexCont exampleList 3

-- Same as index from Data.Vect!
indexVect : Fin n -> Vect' n a -> a
indexVect x xs = indexCont xs x 


