module Tensor.ContainerTensor.Tensor

import Data.Fin
import Data.Vect

import Data.Container.Definition
import Data.Tree

%hide Data.Vect.fromList

public export
data Tensor : (shape : Vect n Cont) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> Tensor [] dtype
    TS : Ext c (Tensor cs dtype) -> Tensor (c :: cs) dtype

%name Tensor t, t'

public export
Functor (Tensor shape) where
  map f (TZ val) = TZ $ f val
  map f (TS xs) = TS $ (map f) <$> xs

namespace IndexTC

  -- Given the Extension of a container, and a position in its shape, return the value at that position
  -- Couterpart of 'index' for Vectors
  -- public export
  -- indexCont : (e : Ext ((!>) shp' pos') a) -> pos' (shapeExt e) -> a
  -- indexCont (_ <| payload) = payload

  ||| Machinery for indexing into a Tensor
  ||| Does this depend only on the shape, or also the actual container?
  public export
  data IndexTC : (shape : Vect n Cont) -> (t : Tensor shape dtype) -> Type where
    Nil : {val : dtype} -> IndexTC [] (TZ val)
    (::) : {e : Ext ((!>) shp' pos') (Tensor cs dtype)} -> (p : pos' (shapeExt e)) -> IndexTC cs (indexCont e p) -> IndexTC ((!>) shp' pos' :: cs) (TS e)
    -- can technically erase the arguments in implicit brackets?

  -- public export
  -- data IndexTC : (shape : Vect n Cont) -> Type where
  --   Nil  : IndexTC []
  --   (::) : {g : shp'} -> pos' g -> IndexTC ms
  --     -> IndexTC (((!>) shp' pos') :: ms)

  -- Here it must hold that the shape at indHere : pos' s is the smae shape as that in the Tensor? Perhaps we need to swap the order of arguments here
  public export
  indexTensor : (t : Tensor shape a)
              -> (index : IndexTC shape t)
              -> a
  indexTensor (TZ val) [] = val
  indexTensor (TS xs) (i :: is) = indexTensor (indexCont xs i) is 


public export
Array : (shape : Vect rank Cont) -> (dtype : Type) -> Type
Array [] dtype = dtype
Array (c :: cs) dtype = (Ext c) (Array cs dtype)

public export
fromArray : {shape : Vect rank Cont} -> Array shape a -> Tensor shape a
fromArray {shape = []} x = TZ x
fromArray {shape = (c :: _)} xs = TS $ fromArray <$> xs

||| This recovers usual tensors in Tensor.Tensor
public export
Tensor' : (shape : Vect n Nat) -> Type -> Type
Tensor' shape = Tensor $ VectCont <$> shape

Array' : (shape : Vect n Nat) -> (dtype : Type) -> Type
Array' [] dtype = dtype
Array' (s :: ss) dtype = Vect s (Array' ss dtype)

fromArray' : {shape : Vect n Nat} -> Array' shape a -> Tensor' shape a
fromArray' {shape = []} x = TZ x
fromArray' {shape = (_ :: _)} x = TS $ fromVect (fromArray' <$> x)

arr1 : Tensor' [2, 3] Int
arr1 = fromArray $ let t = fromArray' {shape=[2,3]} [[1,2,3],[4,5,6]] in ?hole
-- arr1 = fromArray $ fromVect $ fromVect <$> [[1,2,3],[4,5,6]]

indexArr1 : Int
indexArr1 = indexTensor arr1 ?givm

exCont : Tensor [ListCont] Double
exCont = fromArray (fromList [1,2,3,4])

exCont2 : Tensor [TreeNodeCont, ListCont] Int
exCont2 = fromArray $ fromTree $ Node (fromList [1,2,3,4,5]) Leaf' Leaf'

indexCont2 : Int
indexCont2 = indexTensor exCont2 [Root, 4]


exCont3 : Tensor [TreeLeafCont, ListCont] Int
exCont3 = fromArray ?exCont3_rhs

exampleList : List' Int
exampleList = fromList [1,2,3,4]


val : Int
val = indexCont exampleList 3

vv : Vect' 3 Int
vv = fromVect [1,2,3]


-- Same as index from Data.Vect!
indexVect : Fin n -> Vect' n a -> a
indexVect x xs = indexCont xs x 


