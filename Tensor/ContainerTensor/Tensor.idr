module Tensor.ContainerTensor.Tensor

import Data.Fin
import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Tree
import Data.Rig
import Misc
import Algebra
import Tensor.Naperian

%hide Data.Vect.fromList
%hide Builtin.infixr.(#)

public export prefix 0 #

||| Container and a proof that its extension is an applicative functor
public export
record ApplC where
  constructor (#)
  GetC : Cont
  {auto prf : Applicative (Ext GetC)}

||| Construction to make it ergonomic to deal with vectors of applicative containers
public export
data ApplV : Vect n ApplC -> Type where
  Nil : ApplV []
  (::) : (c : Cont) -> Applicative (Ext c)
     => ApplV cs -> ApplV ((# c) :: cs)

public export
data Tensor : (shape : ApplV conts) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> Tensor [] dtype
    TS : Applicative (Ext c) => {cs : ApplV conts} -> c `fof` (Tensor cs dtype) -> Tensor (c :: cs) dtype


%name Tensor t, t'

public export
Scalar : (dtype : Type) -> Type
Scalar dtype = Tensor [] dtype

public export
Vector : (c : ApplC) -> (dtype : Type) -> Type
Vector (# c) dtype = Tensor [c] dtype

public export
Matrix : (row, col : ApplC) -> (dtype : Type) -> Type
Matrix (# row) (# col) dtype = Tensor [row, col] dtype

namespace FunctorT
  public export
  Functor (Tensor shape) where
    map f (TZ val) = TZ $ f val
    map f (TS xs) = TS $ (map f) <$> xs


namespace ApplicativeT
  ||| Datatype for witnessing that all the containers in a shape are applicative
  -- public export -- Not needed anymore since Applicative is baked in to Tensor
  -- data AllAppl : (shape : Vect n Cont) -> Type where
  --   Nil : AllAppl []
  --   Cons : Applicative (Ext c) => AllAppl cs -> AllAppl (c :: cs)

  ||| Unit of the monoidal functor
  public export
  tensorReplicate : {shape : ApplV conts}
    -> a -> Tensor shape a
  tensorReplicate {shape = []} a = TZ a
  tensorReplicate {shape = (c :: cs)} a = TS $ pure (tensorReplicate a)

  ||| Laxator of the monoidal functor
  public export
  liftA2Tensor : {shape : ApplV conts} -> Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
  liftA2Tensor (TZ a) (TZ b) = TZ (a, b)
  liftA2Tensor (TS x) (TS y) = TS $ uncurry liftA2Tensor <$> (liftA2 x y)

  public export
  {shape : ApplV conts} -> Applicative (Tensor shape) where
    pure = tensorReplicate 
    fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs 

namespace NumericT
  public export
  {shape : ApplV conts} -> Rig a => Rig (Tensor shape a) where
    zero = tensorReplicate zero
    one = tensorReplicate one
    xs ~+~ ys = (uncurry (~+~)) <$> liftA2 xs ys
    xs ~*~ ys = (uncurry (~*~)) <$> liftA2 xs ys
  public export
  {shape : ApplV conts} -> Num a => Num (Tensor shape a) where
    fromInteger i = pure (fromInteger i)
    xs + ys = (uncurry (+)) <$> liftA2 xs ys
    xs * ys = (uncurry (*)) <$> liftA2 xs ys

  public export
  {shape : ApplV conts} -> Neg a => Neg (Tensor shape a) where
    negate = (negate <$>)
    xs - ys = (uncurry (-)) <$> liftA2 xs ys

  public export
  {shape : ApplV conts} -> Abs a => Abs (Tensor shape a) where
    abs = (abs <$>)

  public export
  {shape : ApplV conts} -> Fractional a => Fractional (Tensor shape a) where
    t / v = (uncurry (/)) <$> liftA2 t v

  public export
  {shape : ApplV conts} -> Exp a => Exp (Tensor shape a) where
    exp = (exp <$>)



namespace AlgebraT
  public export
  data AllAlgebra : (shape : ApplV conts) -> (dtype : Type) -> Type where
    Nil : AllAlgebra [] a
    (::) : {c : Cont} -> 
      Applicative (Ext c) =>
      {cs : ApplV conts} ->
      (alg : Algebra (Ext c) (Tensor cs a))
      => AllAlgebra cs a -> AllAlgebra (c :: cs) a

  public export
  reduceTensor : {shape : ApplV conts} -> (allAlgebra : AllAlgebra shape a) => Tensor shape a -> a
  reduceTensor {allAlgebra = []} (TZ val) = val
  reduceTensor {allAlgebra = ((::) cs)} (TS xs) = reduceTensor @{cs} (reduce xs)

  public export
  {shape : ApplV conts} -> (allAlgebra : AllAlgebra shape a) =>
  Algebra (Tensor shape) a where
    reduce = reduceTensor

  public export
  [appSumTensor] {shape : ApplV conts} 
    -> {a : Type}
    -> Rig a
    => Applicative (Ext c)
    => (allAlg : AllAlgebra shape a)
    => Algebra (Tensor shape) ((Ext c) a) where
      reduce {allAlg = []} (TZ val) = val
      reduce {shape=(c::cs)} {allAlg = ((::) alg)} (TS xs) -- = ?fvhvh_2
        = let t = reduce {f=(Tensor cs)} <$> xs
          in ?ghhh -- reduce (reduce <$> xs)




public export
dot : {shape : ApplV conts} -> {a : Type}
  -> Rig a => AllAlgebra shape a
  => Tensor shape a -> Tensor shape a -> Tensor [] a
dot xs ys = TZ $ reduce $ (\(x, y) => x ~*~ y) <$> liftA2Tensor xs ys


-- Multiply a matrix and a vector
public export
multiplyMV : {a : Type} -> Rig a =>
  Applicative (Ext f) =>
  Applicative (Ext g) =>
  AllAlgebra [g] a =>
  Tensor [f, g] a -> Tensor [g] a -> Tensor [f] a
multiplyMV (TS m) v = TS (dot v <$> m)

-- Multiply a vector and a matrix
public export
multiplyVM : {a : Type} -> {f, g : Cont} -> Rig a =>
  Applicative (Ext f) =>
  Applicative (Ext g) =>
  (allAlgebra : AllAlgebra [f, g] a) =>
  Tensor [f] a -> Tensor [f, g] a -> Tensor [g] a
multiplyVM {allAlgebra = ((::) aa)} (TS v) (TS m)
  = let t = liftA2 v m
        w = (\((TZ val), v') => (val ~*~) <$> v') <$> t
    in reduce {f=(Ext f)} w

public export
matMul : {f, g, h : Cont} -> {a : Type} -> Rig a =>
  Applicative (Ext f) =>
  Applicative (Ext g) =>
  Applicative (Ext h) =>
  (allAlgebra : AllAlgebra [g, h] a) =>
  Tensor [f, g] a -> Tensor [g, h] a -> Tensor [f, h] a
matMul (TS m1) m2 = TS $ m1 <&> (\row => multiplyVM row m2)

-- ij,kj->ki
public export
multiplyMMT : {f, g, h : Cont} -> {a : Type} -> Rig a =>
  Applicative (Ext f) =>
  Applicative (Ext g) =>
  Applicative (Ext h) =>
  (allAlgebra : AllAlgebra [g] a) =>
  Tensor [f, g] a -> Tensor [h, g] a -> Tensor [h, f] a
multiplyMMT m (TS n) = TS (multiplyMV m <$> n)


public export
Array : (shape : ApplV conts) -> (dtype : Type) -> Type
Array [] dtype = dtype
Array (c :: cs) dtype = (Ext c) (Array cs dtype)

public export
fromArray : {shape : ApplV conts} -> Array shape a -> Tensor shape a
fromArray {shape = []} x = TZ x
fromArray {shape = (c :: _)} xs = TS $ fromArray <$> xs

public export
toArray : {shape : ApplV conts} -> Tensor shape a -> Array shape a
toArray (TZ val) = val
toArray (TS xs) = toArray <$> xs

public export
toNestedTensor : {n : Cont} -> {ns : ApplV conts} ->
  Applicative (Ext n) =>
  Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
toNestedTensor (TS vs) = TS (TZ <$> vs)

public export
fromNestedTensor : {n : Cont} -> {ns : ApplV conts} ->
  Applicative (Ext n) =>
  Tensor [n] (Tensor ns a) -> Tensor (n :: ns) a
fromNestedTensor (TS vs) = TS $ ((\(TZ jk) => jk) <$> vs)


-- This recovers usual tensors in Tensor.Tensor
-- public export
-- Tensor' : (shape : Vect n Nat) -> Type -> Type
-- Tensor' shape = Tensor ((\n => (_ : Unit) !> Fin n) <$> shape)
-- Tensor' shape = Tensor (VectCont <$> shape)

-- TODO this can probably be improved/simplified?
public export
vectApplV : (shape : Vect n Nat) -> ApplV ((\n => # (VectCont n)) <$> shape)
vectApplV [] = []
vectApplV (s :: ss) = VectCont s :: vectApplV ss

||| Instead of thing above we need this to aid type inference
public export
record Tensor' (shape : Vect n Nat) a where
  constructor MkT
  GetT : Tensor (vectApplV shape) a

public export
Functor (Tensor' shape) where
  map f (MkT t) = MkT $ map f t

public export
{shape : Vect n Nat} -> Num a => Num (Tensor' shape a) where
  fromInteger i = MkT $ fromInteger {ty=(Tensor (vectApplV shape) a)} i
  (MkT xs) + (MkT ys) = MkT $ (+) {ty=(Tensor (vectApplV shape) a)} xs ys
  (MkT xs) * (MkT ys) = MkT $ (*) {ty=(Tensor (vectApplV shape) a)} xs ys


public export
{shape : Vect n Nat} -> Neg a => Neg (Tensor' shape a) where
  negate (MkT t) = MkT $ negate t
  (MkT xs) - (MkT ys) = MkT $ (-) {ty=(Tensor (vectApplV shape) a)} xs ys

public export
{shape : Vect n Nat} -> Abs a => Abs (Tensor' shape a) where
  abs (MkT t) = MkT $ abs t


-- public export
-- dot' : {shape : Vect n Nat} -> {a : Type}
--   -> Rig a => AllAlgebra (vectApplV shape) a
--   => Tensor' shape a -> Tensor' shape a -> Tensor [] a
-- dot' xs ys = TZ $ reduce $ (\(x, y) => x ~*~ y) <$> liftA2Tensor ?xxs ?yys

public export
Array' : (shape : Vect n Nat) -> (dtype : Type) -> Type
Array' [] dtype = dtype
Array' (s :: ss) dtype = Vect s (Array' ss dtype)

public export
fromArrayHelper : {shape : Vect n Nat}
  -> Array' shape a
  -> Tensor (vectApplV shape) a
fromArrayHelper {shape=[]} x = TZ x
fromArrayHelper {shape=(s :: ss)} x
  = TS $ fromVect $ fromArrayHelper <$> x

public export
fromArray' : {shape : Vect n Nat} -> Array' shape a -> Tensor' shape a
fromArray' a = MkT $ fromArrayHelper a

arr : Tensor' [] Int
arr = fromArray' 117

arr0 : Tensor' [3] Int
arr0 = fromArray' [1,2,3]

-- TODO ListCont is not an example anymore! Is this somethign we want?
-- exCont : Tensor [ListCont] Double
-- exCont = fromArray (fromList [1,2,3,4])


namespace IndexT
  -- Given the Extension of a container, and a position in its shape, return the value at that position
  -- Couterpart of 'index' for Vectors
  -- public export
  -- indexCont : (e : Ext ((!>) shp' pos') a) -> pos' (shapeExt e) -> a
  -- indexCont (_ <| payload) = payload

  ||| Machinery for indexing into a Tensor
  ||| Does this depend only on the shape, or also the actual container?
  public export
  data IndexT : (shape : ApplV conts) -> (t : Tensor shape dtype) -> Type where
    Nil : {val : dtype} -> IndexT [] (TZ val)
    (::) :  {e : ((!>) shp' pos') `fof` (Tensor cs dtype)} -> 
      Applicative (Ext ((!>) shp' pos')) =>
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
               -> (index : IndexT (vectApplV shape) (GetT t))
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
    -> (t : Tensor' shape a) -> IndexT (vectApplV shape) (GetT t) -> a
  (@@@) (MkT t) i = indexTensor t i



-- TODO
-- exCont2 : Tensor [BTreeNodeCont, ListCont] Int
-- exCont2 = fromArray $ fromTree $ Node (fromList [1,2,3,4,5]) Leaf' Leaf'

-- TODO
-- indexCont2 : Int
-- indexCont2 = indexTensor exCont2 [Root, 4]


-- TODO
-- exCont3 : Tensor [BTreeLeafCont, ListCont] Int
-- exCont3 = fromArray ?exCont3_rhs

ggh : {x, y : Cont}
  -> Applicative (Ext x) => Applicative (Ext y)
  => {ss : ApplV conts}
  -> (f : Tensor [x] a -> Tensor [y] a)
  -> Tensor [x] (Tensor ss a) -> Tensor [y] (Tensor ss a)
ggh f t = ?ho

tmfa : {x, y : Cont}
  -> Applicative (Ext x) => Applicative (Ext y)
  => {ss : ApplV conts}
  -> (f : Tensor [x] a -> Tensor [y] a)
  -> Tensor (x :: ss) a  -> Tensor (y :: ss) a
tmfa f ta = ?hoo
  -- = let tt = f
  --   in fromNestedTensor $ ?flvl $ toNestedTensor ta

public export
tensorMapFirstAxis : {x, y : Cont}
  -> Applicative (Ext x) => Applicative (Ext y)
  => {ss : ApplV conts}
  -> (f : Tensor [x] (Tensor ss a) -> Tensor [y] (Tensor ss a))
  -> Tensor (x :: ss) a -> Tensor (y :: ss) a
tensorMapFirstAxis f ta = fromNestedTensor $ f $ toNestedTensor ta

exampleList : List' Int
exampleList = fromList [1,2,3,4]


val : Int
val = indexCont exampleList 3

vv : Vect' 3 Int
vv = fromVect [1,2,3]


-- Same as index from Data.Vect!
indexVect : Fin n -> Vect' n a -> a
indexVect x v = indexCont v x



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
