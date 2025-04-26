module Tensor.ContainerTensor.Tensor

import Data.Fin
import Data.Vect

import Data.Container.Definition
import Data.Tree
import Misc

%hide Data.Vect.fromList

public export
data Tensor : (shape : Vect n Cont) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> Tensor [] dtype
    TS : c `fof` (Tensor cs dtype) -> Tensor (c :: cs) dtype

%name Tensor t, t'

public export
Scalar : (dtype : Type) -> Type
Scalar dtype = Tensor [] dtype

public export
Vector : (c : Cont) -> (dtype : Type) -> Type
Vector c dtype = Tensor [c] dtype

public export
Matrix : (row, col : Cont) -> (dtype : Type) -> Type
Matrix row col dtype = Tensor [row, col] dtype

public export
Functor (Tensor shape) where
  map f (TZ val) = TZ $ f val
  map f (TS xs) = TS $ (map f) <$> xs


namespace ApplicativeTensor
  ||| Datatype for witnessing that all the containers in a shape are applicative
  public export
  data AllAppl : (shape : Vect n Cont) -> Type where
    Nil : AllAppl []
    Cons : Applicative (Ext c) => AllAppl cs -> AllAppl (c :: cs)

  ||| Unit of the monoidal functor
  public export
  tensorReplicate : {shape : Vect n Cont}
    -> {allAppl : AllAppl shape}
    -> a -> Tensor shape a
  tensorReplicate {shape = []} {allAppl = []} a = TZ a
  tensorReplicate {shape = (x :: xs)} {allAppl = Cons allAppl'} a
    = TS $ pure (tensorReplicate {allAppl=allAppl'} a)

  ||| Laxator of the monoidal functor
  public export
  liftA2Cont : {shape : Vect n Cont} -> {allAppl : AllAppl shape} -> Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
  liftA2Cont {allAppl = Nil} (TZ a) (TZ b) = TZ (a, b)
  liftA2Cont {allAppl = Cons allAppl'} (TS x) (TS y)
    = TS $ uncurry (liftA2Cont {allAppl=allAppl'}) <$> (liftA2 x y)

  public export
  {shape : Vect n Cont} -> {allAppl : AllAppl shape} -> Applicative (Tensor shape) where
    pure = tensorReplicate {allAppl=allAppl}
    fs <*> xs = map (uncurry ($)) $ liftA2Cont {allAppl=allAppl} fs xs 

public export
{shape : Vect n Cont} -> {allAppl : AllAppl shape} -> Num a => Num (Tensor shape a) where
  fromInteger {allAppl = []} i = tensorReplicate {allAppl=[]} $ fromInteger i 
  fromInteger {allAppl = (Cons x)} i = ?tuuu_1 -- tensorReplicate $ let t = Prelude.fromInteger i in ?vlll
  -- i = tensorReplicate (let t = Prelude.fromInteger i in ?ahhh) -- tensorReplicate (fromInteger i)
  xs + ys = ?vnaj1 -- (uncurry (+)) <$> liftA2 xs ys
  xs * ys = ?vnaj2 -- (uncurry (*)) <$> liftA2 xs ys


public export
Array : (shape : Vect rank Cont) -> (dtype : Type) -> Type
Array [] dtype = dtype
Array (c :: cs) dtype = (Ext c) (Array cs dtype)

public export
fromArray : {shape : Vect rank Cont} -> Array shape a -> Tensor shape a
fromArray {shape = []} x = TZ x
fromArray {shape = (c :: _)} xs = TS $ fromArray <$> xs

public export
toNestedTensor : Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
toNestedTensor (TS vs) = TS (TZ <$> vs)

||| This recovers usual tensors in Tensor.Tensor
-- public export
-- Tensor' : (shape : Vect n Nat) -> Type -> Type
-- Tensor' shape = Tensor ((\n => (_ : Unit) !> Fin n) <$> shape)
-- Tensor' shape = Tensor (VectCont <$> shape)

||| Instead of thing above we need this to aid type inferene
public export
record Tensor' (shape : Vect n Nat) a where
  constructor MkT
  GetT : Tensor (VectCont <$> shape) a
-- data Tensor' : (shape : Vect n Nat) -> Type -> Type where
--   MkT : {shape : Vect n Nat}
--     -> Tensor (VectCont <$> shape) a
--     -> Tensor' shape a


public export
Array' : (shape : Vect n Nat) -> (dtype : Type) -> Type
Array' [] dtype = dtype
Array' (s :: ss) dtype = Vect s (Array' ss dtype)

fromArrayHelper : {shape : Vect n Nat}
  -> Array' shape a
  -> Tensor (map (\n => (!>) () (\_ => Fin n)) shape) a
fromArrayHelper {shape=[]} x = TZ x
fromArrayHelper {shape=(s :: ss)} x = TS $ fromVect $ fromArrayHelper <$> x

public export
fromArray' : {shape : Vect n Nat} -> Array' shape a -> Tensor' shape a
fromArray' a = MkT $ fromArrayHelper a

arr : Tensor' [] Int
arr = fromArray' 117

arr0 : Tensor' [3] Int
arr0 = fromArray' [1,2,3]

exCont : Tensor [ListCont] Double
exCont = fromArray (fromList [1,2,3,4])


namespace IndexT

  -- Given the Extension of a container, and a position in its shape, return the value at that position
  -- Couterpart of 'index' for Vectors
  -- public export
  -- indexCont : (e : Ext ((!>) shp' pos') a) -> pos' (shapeExt e) -> a
  -- indexCont (_ <| payload) = payload

  ||| Machinery for indexing into a Tensor
  ||| Does this depend only on the shape, or also the actual container?
  public export
  data IndexT : (shape : Vect n Cont) -> (t : Tensor shape dtype) -> Type where
    Nil : {val : dtype} -> IndexT [] (TZ val)
    (::) : {e : ((!>) shp' pos') `fof` (Tensor cs dtype)} -> 
      (p : pos' (shapeExt e)) ->
      IndexT cs (indexCont e p) -> 
      IndexT ((!>) shp' pos' :: cs) (TS e)
    -- can technically erase the arguments in implicit brackets?

  public export
  indexTensor : (t : Tensor shape a)
              -> (index : IndexT shape t)
              -> a
  indexTensor (TZ val) [] = val
  indexTensor (TS xs) (i :: is) = indexTensor (indexCont xs i) is 

  public export
  indexTensor' : {shape : Vect n Nat}
               -> (t : Tensor' shape a)
               -> (index : IndexT (VectCont <$> shape) (GetT t))
               -> a
  indexTensor' (MkT t) index = indexTensor t index



  -- Why can't I use @ here?
  public export infixr 9 @@

  public export
  (@@) : (t : Tensor shape a) -> IndexT shape t -> a
  (@@) = indexTensor


  public export infixr 9 @@@

  public export
  (@@@) : {shape : Vect n Nat}
    -> (t : Tensor' shape a) -> IndexT (VectCont <$> shape) (GetT t) -> a
  (@@@) (MkT t) i = indexTensor t i


arr1 : Tensor' [2, 3] Int
arr1 = fromArray' [ [1, 2, 3] 
                  , [4, 5, 6] ]


indexArr1 : Int
indexArr1 =  arr1 @@@ [1,2]



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



{- 
data TT : (shape : Vect n Cont) -> Type where
  C : (shape : Vect n Cont) -> TT shape


f : TT [((!>) () (\_ => Fin 3))]
f = let n : Nat = ?shnn
        sh : Vect n Nat = ?shhh
        t = (\n => (!>) () (\_ => Fin n)) <$> sh
    in C ?hole
-}
{-
From this:
(\n => () !> (\_ => Fin n)) <$> shape
being equal to this:
[(() !> (\_ => Fin 2))] 

We should be able to infer that shape : Vect n Nat = [2]

We can simplify this to
f <$> shape
being equal to
[f 2]
where f : Nat -> Type

Can we from this, for an arbitrary f, infer that shape = [2]?
 -}
