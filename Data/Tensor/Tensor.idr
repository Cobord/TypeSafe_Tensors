module Data.Tensor.Tensor

import Data.Fin
import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Tree
import Misc
import Algebra
import Data.Functor.Naperian

%hide Data.Vect.fromList
%hide Builtin.infixr.(#)

||| Applicative Container
||| Consists of a container and a proof that its extension is an applicative functor
public export
record ApplC where
  constructor (#)
  GetC : Cont
  {auto applPrf : Applicative (Ext GetC)}

public export prefix 0 #

%pair ApplC GetC applPrf

||| Construction to make it ergonomic to deal with vectors of applicative containers
public export
data ApplContList : List ApplC -> Type where
  Nil : ApplContList []
  (::) : (c : Cont) ->
    Applicative (Ext c) =>
    ApplContList cs -> ApplContList ((# c) :: cs)

||| Applicative tensors
||| Tensors whose shape is a list of applicative containers
public export
data TensorA : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> TensorA [] dtype
    TS : Applicative (c `fullOf`) => {cs : ApplContList conts} ->
      c `fullOf` (TensorA cs dtype) -> TensorA (c :: cs) dtype

%name TensorA t, t'

-- TODO this can probably be improved/simplified?
public export
natsToApplConts : (shape : List Nat) -> ApplContList ((\n => # (VectCont n)) <$> shape)
natsToApplConts [] = []
natsToApplConts (s :: ss) = VectCont s :: natsToApplConts ss


public export
ScalarA : (dtype : Type) -> Type
ScalarA dtype = TensorA [] dtype

public export
VectorA : (c : ApplC) -> (dtype : Type) -> Type
VectorA (# c) dtype = TensorA [c] dtype

public export
MatrixA : (row, col : ApplC) -> (dtype : Type) -> Type
MatrixA (# row) (# col) dtype = TensorA [row, col] dtype


namespace EqT
  public export
  data AllEq : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    NilEq : Eq dtype => AllEq [] dtype
    ConsEq : {c : Cont} -> {cs : ApplContList conts} ->
      (applExtc : Applicative (Ext c)) =>
      (eqCont: Eq (c `fullOf` (TensorA cs dtype))) =>
      AllEq (c :: cs) dtype

  public export
  tensorEq : {shape : ApplContList conts} -> (allEq : AllEq shape dtype) =>
    TensorA shape dtype -> TensorA shape dtype -> Bool
  tensorEq {allEq = NilEq} (TZ val) (TZ val') = val == val'
  tensorEq {allEq = ConsEq} (TS xs) (TS xs') = xs == xs'

  public export
  {shape : ApplContList conts} -> (allEq : AllEq shape dtype) =>
    Eq (TensorA shape dtype) where
      (==) = tensorEq



namespace ShowT
  public export
  data AllShow : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    NilShow : Show dtype => AllShow [] dtype
    ConsShow : {c : Cont} -> {cs : ApplContList conts} ->
      Applicative (Ext c) =>
      Show (c `fullOf` (TensorA cs dtype)) =>
      AllShow (c :: cs) dtype

  ||| TODO this works, but we need to actually implement pretty printing
  public export
  tensorShow : {shape : ApplContList conts} -> (allShow : AllShow shape dtype) =>
    TensorA shape dtype -> String
  tensorShow {allShow = NilShow} (TZ val) = show val
  tensorShow {allShow = ConsShow} (TS xs) = show xs

  public export
  {shape : ApplContList conts} ->
  (allShow : AllShow shape dtype) =>
    Show (TensorA shape dtype) where
      show = tensorShow

namespace FunctorT
  public export
  Functor (TensorA shape) where
    map f (TZ val) = TZ $ f val
    map f (TS xs) = TS $ (map f) <$> xs


namespace ApplicativeT
  ||| Datatype for witnessing that all the containers in a shape are applicative
  -- public export -- Not used below since Applicative is baked in to TensorA
  -- data AllApplicative : (shape : Vect n Cont) -> Type where
  --   Nil : AllApplicative []
  --   Cons : Applicative (Ext c) => AllApplicative cs -> AllApplicative (c :: cs)

  ||| Unit of the monoidal functor
  public export
  tensorReplicate : {shape : ApplContList conts}
    -> a -> TensorA shape a
  tensorReplicate {shape = []} a = TZ a
  tensorReplicate {shape = (c :: cs)} a = TS $ pure (tensorReplicate a)

  ||| Laxator of the monoidal functor
  public export
  liftA2TensorA : {shape : ApplContList conts} -> TensorA shape a -> TensorA shape b -> TensorA shape (a, b)
  liftA2TensorA (TZ a) (TZ b) = TZ (a, b)
  liftA2TensorA (TS x) (TS y) = TS $ uncurry liftA2TensorA <$> (liftA2 x y)

  public export
  {shape : ApplContList conts} -> Applicative (TensorA shape) where
    pure = tensorReplicate 
    fs <*> xs = uncurry ($) <$> liftA2TensorA fs xs 

namespace NumericT
  public export
  {shape : ApplContList conts} -> Num a => Num (TensorA shape a) where
    fromInteger i = pure (fromInteger i)
    xs + ys = (uncurry (+)) <$> liftA2 xs ys
    xs * ys = (uncurry (*)) <$> liftA2 xs ys

  public export
  {shape : ApplContList conts} -> Neg a => Neg (TensorA shape a) where
    negate = (negate <$>)
    xs - ys = (uncurry (-)) <$> liftA2 xs ys

  public export
  {shape : ApplContList conts} -> Abs a => Abs (TensorA shape a) where
    abs = (abs <$>)

  public export
  {shape : ApplContList conts} -> Fractional a => Fractional (TensorA shape a) where
    t / v = (uncurry (/)) <$> liftA2 t v

  public export
  {shape : ApplContList conts} -> Exp a => Exp (TensorA shape a) where
    exp = (exp <$>)



namespace AlgebraT
  public export
  data AllAlgebra : (shape : ApplContList conts) -> (dtype : Type) -> Type where
    Nil : AllAlgebra [] a
    (::) : {c : Cont} -> {cs : ApplContList conts} ->
      Applicative (Ext c) =>
      (alg : Algebra (Ext c) (TensorA cs a)) =>
      (allAlg : AllAlgebra cs a) => AllAlgebra (c :: cs) a

  public export
  reduceTensorA : {shape : ApplContList conts} -> (allAlgebra : AllAlgebra shape a) => TensorA shape a -> a
  reduceTensorA {allAlgebra = []} (TZ val) = val
  reduceTensorA {allAlgebra = ((::) {allAlg=cs})} (TS xs) = reduceTensorA @{cs} (reduce xs)


  public export
  {shape : ApplContList conts} ->
  (allAlgebra : AllAlgebra shape a) =>
  Algebra (TensorA shape) a where
    reduce = reduceTensorA

  public export
  [appSumTensorA] {shape : ApplContList conts} ->
    {a : Type} ->
    Num a =>
    Applicative (Ext c) =>
    (allAlg : AllAlgebra shape a) =>
    Algebra (TensorA shape) ((Ext c) a) where
      reduce {allAlg = []} (TZ val) = val
      reduce {shape=(c::cs)} {allAlg = ((::) {allAlg=alg})} (TS xs) -- = ?fvhvh_2
        = let t = reduce {f=(TensorA cs)} <$> xs
          in ?ghhh -- reduce (reduce <$> xs)


namespace FoldableT

  public export
  data AllFoldable : (shape : ApplContList conts) -> Type where
      NilFoldable : AllFoldable []
      ConsFoldable : {c : Cont} -> {cs : ApplContList conts} ->
        Foldable (Ext c) =>
        Applicative (Ext c) =>
        AllFoldable cs ->
        AllFoldable (c :: cs)


  public export
  tensorFoldr : (allFoldable : AllFoldable shape) =>
    (el -> acc -> acc) -> acc -> TensorA shape el -> acc
  tensorFoldr {allFoldable = NilFoldable} f z (TZ val) = f val z
  tensorFoldr {allFoldable = (ConsFoldable recAllFoldable)} f z (TS xs) =
      foldr (\t, acc => tensorFoldr {allFoldable=recAllFoldable} f acc t) z xs

  public export
  {conts : List ApplC} ->
  {shape : ApplContList conts} ->
  (allFoldable : AllFoldable shape) =>
  Foldable (TensorA shape) where
    foldr = tensorFoldr


namespace TensorAContractions
  public export
  dot : {shape : ApplContList conts} -> {a : Type} -> Num a =>
    Algebra (TensorA shape) a =>
    TensorA shape a -> TensorA shape a -> TensorA [] a
  dot xs ys = TZ $ reduce $ (\(x, y) => x * y) <$> liftA2TensorA xs ys


  -- Multiply a matrix and a vector
  public export
  multiplyMV : {a : Type} -> Num a =>
    Applicative (Ext f) => Applicative (Ext g) =>
    AllAlgebra [g] a =>
    TensorA [f, g] a -> TensorA [g] a -> TensorA [f] a
  multiplyMV (TS m) v = TS (dot v <$> m)

  -- Multiply a vector and a matrix
  public export
  multiplyVM : {a : Type} -> {f, g : Cont} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    (allAlgebra : AllAlgebra [f, g] a) =>
    TensorA [f] a -> TensorA [f, g] a -> TensorA [g] a
  multiplyVM {allAlgebra = (::)} (TS v) (TS m)
    = let t = liftA2 v m
          w = (\((TZ val), v') => (val *) <$> v') <$> t
      in reduce {f=(Ext f)} w

  -- ij,jk->ik
  public export
  matMul : {f, g, h : Cont} -> {a : Type} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    Applicative (Ext h) =>
    (allAlgebra : AllAlgebra [g, h] a) =>
    TensorA [f, g] a -> TensorA [g, h] a -> TensorA [f, h] a
  matMul (TS m1) m2 = TS $ m1 <&> (\row => multiplyVM row m2)

  -- ij,kj->ki
  public export
  multiplyMMT : {f, g, h : Cont} -> {a : Type} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    Applicative (Ext h) =>
    (allAlgebra : AllAlgebra [g] a) =>
    TensorA [f, g] a -> TensorA [h, g] a -> TensorA [h, f] a
  multiplyMMT m (TS n) = TS (multiplyMV m <$> n)



-- TODO rename since this is not array for non-cubical tensors
public export
Array : (shape : ApplContList conts) -> (dtype : Type) -> Type
Array [] dtype = dtype
Array (c :: cs) dtype = c `fullOf` (Array cs dtype)

public export
fromArray : {shape : ApplContList conts} -> Array shape a -> TensorA shape a
fromArray {shape = []} x = TZ x
fromArray {shape = (_ :: _)} xs = TS $ fromArray <$> xs

public export
toArray : {shape : ApplContList conts} -> TensorA shape a -> Array shape a
toArray (TZ val) = val
toArray (TS xs) = toArray <$> xs


namespace NestedTensorAStuff
  public export
  toNestedTensorA : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA (n :: ns) a -> TensorA [n] (TensorA ns a)
  toNestedTensorA (TS vs) = TS (TZ <$> vs)

  public export infix 4 <-$

  public export
  (<-$) : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA (n :: ns) a -> TensorA [n] (TensorA ns a)
  (<-$) = toNestedTensorA

  public export
  fromNestedTensorA : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA [n] (TensorA ns a) -> TensorA (n :: ns) a
  fromNestedTensorA (TS vs) = TS $ (\(TZ jk) => jk) <$> vs

  public export infixr 4 $->
  public export
  ($->) : {n : Cont} -> {ns : ApplContList conts} ->
    Applicative (Ext n) =>
    TensorA [n] (TensorA ns a) -> TensorA (n :: ns) a
  ($->) = fromNestedTensorA

  public export
  tensorMapFirstAxis : {rest : Cont}
    -> {s1, s2 : ApplContList conts}
    -> Applicative (Ext rest)
    => (f : TensorA s1 a -> TensorA s2 a)
    -> TensorA (rest :: s1) a -> TensorA (rest :: s2) a
  tensorMapFirstAxis f t = fromNestedTensorA $ map f $ toNestedTensorA t


  public export infixr 4 <-$->

  ||| Map, but for nested tensors
  public export
  (<-$->) : {rest : Cont}
    -> {shape : ApplContList conts}
    -> Applicative (Ext rest)
    => (f : TensorA shape a -> TensorA shape a)
    -> TensorA (rest :: shape) a -> TensorA (rest :: shape) a
  (<-$->) = tensorMapFirstAxis



namespace CubicalTensor
  -- This recovers usual tensors in Tensor.Tensor
  -- public export
  -- Tensor' : (shape : Vect n Nat) -> Type -> Type
  -- Tensor' shape = TensorA $ natsToApplConts shape

  -- public export infixr 5 +++
  -- public export
  -- (+++) : {cs : Vect n ApplC} -> {ds : Vect m ApplC}
  --   -> ApplContList cs -> ApplContList ds -> ApplContList (cs ++ ds)
  -- [] +++ ys = ys
  -- (c :: cs) +++ ys = c :: (cs +++ ys)


  -- vvv : (shape : Vect n Nat) -> Vect n ApplC
  -- vvv shape = (\n => # (VectCont n)) <$> shape



  ||| This is a helper datatype for cubical tensors, i.e. those made only out of VectCont
  ||| It allows specifying a tensor only by the size of the content, and is needed (instead of Tensor') to aid type inference
  ||| There might be a more ergonomic way to do this
  public export
  record Tensor (shape : List Nat) a where
    constructor MkT
    GetT : TensorA (natsToApplConts shape) a

  public export
  toCubicalTensor : {shape : List Nat} -> TensorA (natsToApplConts shape) a -> Tensor shape a
  toCubicalTensor t = MkT t

  public export
  fromCubicalTensor : {shape : List Nat} ->
    Tensor shape a -> TensorA (natsToApplConts shape) a
  fromCubicalTensor t = GetT t

  namespace TensorInterfaces
    public export
    {shape : List Nat} ->
    AllEq (natsToApplConts shape) a =>
    Eq (Tensor shape a) where
        (MkT t) == (MkT t') = tensorEq t t'

    public export
    {shape : List Nat} ->
    AllShow (natsToApplConts shape) a =>
    Show (Tensor shape a) where
      show (MkT t) = show t

    public export
    {shape : List Nat} -> Num a => Num (Tensor shape a) where
      fromInteger i = MkT $ fromInteger {ty=(TensorA (natsToApplConts shape) a)} i
      (MkT xs) + (MkT ys) = MkT $ (+) {ty=(TensorA (natsToApplConts shape) a)} xs ys
      (MkT xs) * (MkT ys) = MkT $ (*) {ty=(TensorA (natsToApplConts shape) a)} xs ys

    public export
    {shape : List Nat} -> Neg a => Neg (Tensor shape a) where
      negate (MkT t) = MkT $ negate t
      (MkT xs) - (MkT ys) = MkT $ (-) {ty=(TensorA (natsToApplConts shape) a)} xs ys

    public export
    {shape : List Nat} -> Abs a => Abs (Tensor shape a) where
      abs (MkT t) = MkT $ abs t

    public export
    Functor (Tensor shape) where
      map f (MkT t) = MkT $ map f t


    public export
    tensorReplicate' : {shape : List Nat}
      -> a -> Tensor shape a
    tensorReplicate' {shape = []} a = MkT $ TZ a
    tensorReplicate' {shape = (c :: cs)} a = MkT $ TS $ pure (tensorReplicate a)

    public export
    {shape : List Nat} ->
    AllAlgebra (natsToApplConts shape) a =>
    Algebra (Tensor shape) a where
        reduce (MkT t) = reduce t

    public export
    tensorCFoldr : {shape : List Nat} ->
      (el -> acc -> acc) -> acc -> TensorA (natsToApplConts shape) el -> acc
    tensorCFoldr {shape = []} f z t = foldr f z t
    tensorCFoldr {shape = (s :: ss)} f z (TS xs)
      = foldr (\t, acc => tensorCFoldr f acc t) z xs


    public export
    {shape : List Nat} ->
    Foldable (Tensor shape) where
      foldr f z (MkT t) = tensorCFoldr f z t

    -- TODO implement Traversable for TensorA, and then port it here
    public export
    tensorCTraverse : {shape : List Nat} -> Applicative f =>
      (a -> f b) -> TensorA (natsToApplConts shape) a -> f (TensorA (natsToApplConts shape) b)
    tensorCTraverse {shape = []} fn (TZ val) = TZ <$> fn val
    tensorCTraverse {shape = (s :: ss)} fn (TS xs)
      = TS <$> ?alllao -- (fromVect <$> traverse (tensorCTraverse fn) (toVect xs))

    public export
    {shape : List Nat} ->
    Traversable (Tensor shape) where
      traverse f (MkT t) = MkT <$> tensorCTraverse f t

  public export
  dot' : {shape : List Nat} -> {a : Type}
    -> Num a => AllAlgebra (natsToApplConts shape) a
    => Tensor shape a -> Tensor shape a -> Tensor [] a
  dot' (MkT xs) (MkT ys) = MkT $ TZ $ reduce $ (\(x, y) => x * y) <$> liftA2TensorA xs ys

  public export
  Array' : (shape : List Nat) -> (dtype : Type) -> Type
  Array' [] dtype = dtype
  Array' (s :: ss) dtype = Vect s (Array' ss dtype)

  public export
  fromArrayHelper : {shape : List Nat}
    -> Array' shape a
    -> TensorA (natsToApplConts shape) a
  fromArrayHelper {shape=[]} x = TZ x
  fromArrayHelper {shape=(_ :: _)} x = TS $ fromVect $ fromArrayHelper <$> x

  public export
  fromArray' : {shape : List Nat} -> Array' shape a -> Tensor shape a
  fromArray' a = MkT $ fromArrayHelper a

namespace IndexT
  public export
  data IndexTData : Type where
    NonCubical : (shape : ApplContList conts) -> IndexTData
    Cubical : (shape : Vect n Nat) -> IndexTData -- assuming every Naperian functor has shape=Fin d for some d, this describes Naperian TensorAs

  -- vnn : IndexTData -> Type -> Type
  -- vnn (NonCubical shape) = TensorA shape
  -- vnn (Cubical shape) = \_ => Unit

  -- -- vnnn : (conts : Vect n ApplC) -> Cont
  -- -- vnnn conts = foldr ?acc CUnit (GetC <$> conts)

  -- ||| TensorAs too are a container
  -- tensorCont : Type -> Cont
  -- tensorCont dtype = (s : IndexTData) !> vnn s
    
  ||| Machinery for indexing into a TensorA
  ||| For general, non-cubical tensors this depends on the tensor itself
  ||| TODO remove this dependence for cubical tensors
  public export
  data IndexT : (shape : ApplContList conts) -> (t : TensorA shape dtype) -> Type where
    Nil : {val : dtype} -> IndexT [] (TZ val)
    (::) :  {e : ((!>) shp' pos') `fullOf` (TensorA cs dtype)} -> 
      Applicative (Ext ((!>) shp' pos')) =>
      (p : pos' (shapeExt e)) ->
      IndexT cs (indexCont e p) -> 
      IndexT ((!>) shp' pos' :: cs) (TS e)

  public export
  indexTensorA : (t : TensorA shape a)
              -> (index : IndexT shape t)
              -> a
  indexTensorA (TZ val) [] = val
  indexTensorA (TS xs) (i :: is) = indexTensorA (indexCont xs i) is 

  public export
  indexTensor : {shape : List Nat}
               -> (t : Tensor shape a)
               -> (index : IndexT (natsToApplConts shape) (GetT t))
               -> a
  indexTensor (MkT t) index = indexTensorA t index



  -- Why can't I use @ here?
  public export infixr 9 @@

  public export
  (@@) : (t : TensorA shape a) -> IndexT shape t -> a
  (@@) = indexTensorA


  public export infixr 9 @@@

  public export
  (@@@) : {shape : List Nat}
    -> (t : Tensor shape a) -> IndexT (natsToApplConts shape) (GetT t) -> a
  (@@@) (MkT t) i = indexTensorA t i


namespace SliceT
  ||| Machinery for slicing cubical tensors
  ||| Crucially, different from the indexing one in the definition of (::)
  ||| Here we have Fin (S m) instead of Fin m
  public export
  data SliceT : (shape : List Nat) -> Type where
    Nil : SliceT []
    (::) : Fin (S m) -> SliceT ms -> SliceT (m :: ms)

  public export
  sliceToShape : {shape : List Nat} -> SliceT shape -> List Nat
  sliceToShape Nil = []
  sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

  public export -- analogus to take in Data.Vect, but for Fin
  takeFinVect' : {n : Nat} ->
    (s : Fin (S n)) -> Vect' n a -> Vect' (finToNat s) a
  takeFinVect' s x = fromVect (takeFin s (toVect x))

  public export --
  takeTensor : {shape : List Nat} ->
    (slice : SliceT shape) ->
    Tensor shape a ->
    Tensor (sliceToShape slice) a
  takeTensor [] (MkT (TZ val)) = MkT (TZ val)
  takeTensor (s :: ss) (MkT (TS xs)) = MkT $ TS $ 
    (\t => GetT ((takeTensor ss) (MkT t))) <$> takeFinVect' s xs




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
