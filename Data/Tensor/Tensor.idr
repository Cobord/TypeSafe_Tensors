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

||| Container and a proof that its extension is an applicative functor
public export
record ApplC where
  constructor (#)
  GetC : Cont
  {auto applPrf : Applicative (Ext GetC)}

public export prefix 0 #

%pair ApplC GetC applPrf

||| Construction to make it ergonomic to deal with vectors of applicative containers
public export
data ApplV : Vect n ApplC -> Type where
  Nil : ApplV []
  (::) : (c : Cont) ->
    Applicative (Ext c) =>
    ApplV cs -> ApplV ((# c) :: cs)

public export
data Tensor : (shape : ApplV conts) -> (dtype : Type) -> Type where
    TZ : (val : dtype) -> Tensor [] dtype
    TS : Applicative (c `fullOf`) => {cs : ApplV conts} ->
      c `fullOf` (Tensor cs dtype) -> Tensor (c :: cs) dtype

-- TODO this can probably be improved/simplified?
public export
vectApplV : (shape : Vect n Nat) -> ApplV ((\n => # (VectCont n)) <$> shape)
vectApplV [] = []
vectApplV (s :: ss) = VectCont s :: vectApplV ss


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


namespace EqT
  public export
  data AllEq : (shape : ApplV conts) -> (dtype : Type) -> Type where
    NilEq : Eq dtype => AllEq [] dtype
    ConsEq : {c : Cont} -> {cs : ApplV conts} ->
      (applExtc : Applicative (Ext c)) =>
      (eqCont: Eq (c `fullOf` (Tensor cs dtype))) =>
      AllEq (c :: cs) dtype

  public export
  tensorEq : {shape : ApplV conts} -> (allEq : AllEq shape dtype) =>
    Tensor shape dtype -> Tensor shape dtype -> Bool
  tensorEq {allEq = NilEq} (TZ val) (TZ val') = val == val'
  tensorEq {allEq = ConsEq} (TS xs) (TS xs') = xs == xs'

  public export
  {shape : ApplV conts} -> (allEq : AllEq shape dtype) =>
    Eq (Tensor shape dtype) where
      (==) = tensorEq



namespace ShowT
  public export
  data AllShow : (shape : ApplV conts) -> (dtype : Type) -> Type where
    NilShow : Show dtype => AllShow [] dtype
    ConsShow : {c : Cont} -> {cs : ApplV conts} ->
      Applicative (Ext c) =>
      Show (c `fullOf` (Tensor cs dtype)) =>
      AllShow (c :: cs) dtype

  ||| TODO this works, but we need to actually implement pretty printing
  public export
  tensorShow : {shape : ApplV conts} -> (allShow : AllShow shape dtype) =>
    Tensor shape dtype -> String
  tensorShow {allShow = NilShow} (TZ val) = show val
  tensorShow {allShow = ConsShow} (TS xs) = show xs

  public export
  {shape : ApplV conts} ->
  (allShow : AllShow shape dtype) =>
    Show (Tensor shape dtype) where
      show = tensorShow

namespace FunctorT
  public export
  Functor (Tensor shape) where
    map f (TZ val) = TZ $ f val
    map f (TS xs) = TS $ (map f) <$> xs


namespace ApplicativeT
  ||| Datatype for witnessing that all the containers in a shape are applicative
  -- public export -- Not used below since Applicative is baked in to Tensor
  -- data AllApplicative : (shape : Vect n Cont) -> Type where
  --   Nil : AllApplicative []
  --   Cons : Applicative (Ext c) => AllApplicative cs -> AllApplicative (c :: cs)

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
    (::) : {c : Cont} -> {cs : ApplV conts} ->
      Applicative (Ext c) =>
      (alg : Algebra (Ext c) (Tensor cs a)) =>
      (allAlg : AllAlgebra cs a) => AllAlgebra (c :: cs) a

  public export
  reduceTensor : {shape : ApplV conts} -> (allAlgebra : AllAlgebra shape a) => Tensor shape a -> a
  reduceTensor {allAlgebra = []} (TZ val) = val
  reduceTensor {allAlgebra = ((::) {allAlg=cs})} (TS xs) = reduceTensor @{cs} (reduce xs)


  public export
  {shape : ApplV conts} ->
  (allAlgebra : AllAlgebra shape a) =>
  Algebra (Tensor shape) a where
    reduce = reduceTensor

  public export
  [appSumTensor] {shape : ApplV conts} ->
    {a : Type} ->
    Num a =>
    Applicative (Ext c) =>
    (allAlg : AllAlgebra shape a) =>
    Algebra (Tensor shape) ((Ext c) a) where
      reduce {allAlg = []} (TZ val) = val
      reduce {shape=(c::cs)} {allAlg = ((::) {allAlg=alg})} (TS xs) -- = ?fvhvh_2
        = let t = reduce {f=(Tensor cs)} <$> xs
          in ?ghhh -- reduce (reduce <$> xs)


namespace FoldableT

  public export
  data AllFoldable : (shape : ApplV conts) -> Type where
      NilFoldable : AllFoldable []
      ConsFoldable : {c : Cont} -> {cs : ApplV conts} ->
        Foldable (Ext c) =>
        Applicative (Ext c) =>
        AllFoldable cs ->
        AllFoldable (c :: cs)


  public export
  tensorFoldr : (allFoldable : AllFoldable shape) =>
    (el -> acc -> acc) -> acc -> Tensor shape el -> acc
  tensorFoldr {allFoldable = NilFoldable} f z (TZ val) = f val z
  tensorFoldr {allFoldable = (ConsFoldable recAllFoldable)} f z (TS xs) =
      foldr (\t, acc => tensorFoldr {allFoldable=recAllFoldable} f acc t) z xs

  public export
  {conts : Vect n ApplC} ->
  {shape : ApplV conts} ->
  (allFoldable : AllFoldable shape) =>
  Foldable (Tensor shape) where
    foldr = tensorFoldr


namespace TensorContractions
  public export
  dot : {shape : ApplV conts} -> {a : Type} -> Num a =>
    Algebra (Tensor shape) a =>
    Tensor shape a -> Tensor shape a -> Tensor [] a
  dot xs ys = TZ $ reduce $ (\(x, y) => x * y) <$> liftA2Tensor xs ys


  -- Multiply a matrix and a vector
  public export
  multiplyMV : {a : Type} -> Num a =>
    Applicative (Ext f) => Applicative (Ext g) =>
    AllAlgebra [g] a =>
    Tensor [f, g] a -> Tensor [g] a -> Tensor [f] a
  multiplyMV (TS m) v = TS (dot v <$> m)

  -- Multiply a vector and a matrix
  public export
  multiplyVM : {a : Type} -> {f, g : Cont} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    (allAlgebra : AllAlgebra [f, g] a) =>
    Tensor [f] a -> Tensor [f, g] a -> Tensor [g] a
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
    Tensor [f, g] a -> Tensor [g, h] a -> Tensor [f, h] a
  matMul (TS m1) m2 = TS $ m1 <&> (\row => multiplyVM row m2)

  -- ij,kj->ki
  public export
  multiplyMMT : {f, g, h : Cont} -> {a : Type} -> Num a =>
    Applicative (Ext f) =>
    Applicative (Ext g) =>
    Applicative (Ext h) =>
    (allAlgebra : AllAlgebra [g] a) =>
    Tensor [f, g] a -> Tensor [h, g] a -> Tensor [h, f] a
  multiplyMMT m (TS n) = TS (multiplyMV m <$> n)


-- TODO rename since this is not array for non-cubical tensors
public export
Array : (shape : ApplV conts) -> (dtype : Type) -> Type
Array [] dtype = dtype
Array (c :: cs) dtype = c `fullOf` (Array cs dtype)

public export
fromArray : {shape : ApplV conts} -> Array shape a -> Tensor shape a
fromArray {shape = []} x = TZ x
fromArray {shape = (_ :: _)} xs = TS $ fromArray <$> xs

public export
toArray : {shape : ApplV conts} -> Tensor shape a -> Array shape a
toArray (TZ val) = val
toArray (TS xs) = toArray <$> xs


namespace NestedTensorStuff
  public export
  toNestedTensor : {n : Cont} -> {ns : ApplV conts} ->
    Applicative (Ext n) =>
    Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
  toNestedTensor (TS vs) = TS (TZ <$> vs)

  public export infix 4 <-$

  public export
  (<-$) : {n : Cont} -> {ns : ApplV conts} ->
    Applicative (Ext n) =>
    Tensor (n :: ns) a -> Tensor [n] (Tensor ns a)
  (<-$) = toNestedTensor

  public export
  fromNestedTensor : {n : Cont} -> {ns : ApplV conts} ->
    Applicative (Ext n) =>
    Tensor [n] (Tensor ns a) -> Tensor (n :: ns) a
  fromNestedTensor (TS vs) = TS $ (\(TZ jk) => jk) <$> vs

  public export infixr 4 $->
  public export
  ($->) : {n : Cont} -> {ns : ApplV conts} ->
    Applicative (Ext n) =>
    Tensor [n] (Tensor ns a) -> Tensor (n :: ns) a
  ($->) = fromNestedTensor

  public export
  tensorMapFirstAxis : {rest : Cont}
    -> {s1, s2 : ApplV conts}
    -> Applicative (Ext rest)
    => (f : Tensor s1 a -> Tensor s2 a)
    -> Tensor (rest :: s1) a -> Tensor (rest :: s2) a
  tensorMapFirstAxis f t = fromNestedTensor $ map f $ toNestedTensor t


  public export infixr 4 <-$->

  ||| Map, but for nested tensors
  public export
  (<-$->) : {rest : Cont}
    -> {shape : ApplV conts}
    -> Applicative (Ext rest)
    => (f : Tensor shape a -> Tensor shape a)
    -> Tensor (rest :: shape) a -> Tensor (rest :: shape) a
  (<-$->) = tensorMapFirstAxis



namespace CubicalTensor
  -- This recovers usual tensors in Tensor.Tensor
  -- public export
  -- Tensor'' : (shape : Vect n Nat) -> Type -> Type
  -- Tensor'' shape = Tensor $ vectApplV shape

  -- public export infixr 5 +++
  -- public export
  -- (+++) : {cs : Vect n ApplC} -> {ds : Vect m ApplC}
  --   -> ApplV cs -> ApplV ds -> ApplV (cs ++ ds)
  -- [] +++ ys = ys
  -- (c :: cs) +++ ys = c :: (cs +++ ys)


  -- vvv : (shape : Vect n Nat) -> Vect n ApplC
  -- vvv shape = (\n => # (VectCont n)) <$> shape



  ||| This is a helper datatype for cubical tensors, i.e. those made only out of VectCont
  ||| It allows specifying a tensor only by the size of the content, and is needed (instead of Tensor'') to aid type inference
  ||| There might be a more ergonomic way to do this
  public export
  record Tensor' (shape : Vect n Nat) a where
    constructor MkT
    GetT : Tensor (vectApplV shape) a

  public export
  toCubicalTensor : {shape : Vect n Nat} -> Tensor (vectApplV shape) a -> Tensor' shape a
  toCubicalTensor t = MkT t

  public export
  fromCubicalTensor : {shape : Vect n Nat} -> Tensor' shape a -> Tensor (vectApplV shape) a
  fromCubicalTensor t = GetT t

  namespace Tensor'Interfaces
    public export
    {shape : Vect n Nat} ->
    AllEq (vectApplV shape) a =>
    Eq (Tensor' shape a) where
        (MkT t) == (MkT t') = tensorEq t t'

    public export
    {shape : Vect n Nat} ->
    AllShow (vectApplV shape) a =>
    Show (Tensor' shape a) where
      show (MkT t) = show t

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

    public export
    Functor (Tensor' shape) where
      map f (MkT t) = MkT $ map f t


    public export
    tensorReplicate' : {shape : Vect n Nat}
      -> a -> Tensor' shape a
    tensorReplicate' {shape = []} a = MkT $ TZ a
    tensorReplicate' {shape = (c :: cs)} a = MkT $ TS $ pure (tensorReplicate a)

    public export
    {shape : Vect n Nat} ->
    AllAlgebra (vectApplV shape) a =>
    Algebra (Tensor' shape) a where
        reduce (MkT t) = reduce t

    public export
    tensorCFoldr : {shape : Vect n Nat} ->
      (el -> acc -> acc) -> acc -> Tensor (vectApplV shape) el -> acc
    tensorCFoldr {shape = []} f z t = foldr f z t
    tensorCFoldr {shape = (s :: ss)} f z (TS xs)
      = foldr (\t, acc => tensorCFoldr f acc t) z xs


    public export
    {shape : Vect n Nat} ->
    Foldable (Tensor' shape) where
      foldr f z (MkT t) = tensorCFoldr f z t

    -- TODO implement Traversable for Tensor, and then port it here
    public export
    tensorCTraverse : {shape : Vect n Nat} -> Applicative f =>
      (a -> f b) -> Tensor (vectApplV shape) a -> f (Tensor (vectApplV shape) b)
    tensorCTraverse {shape = []} fn (TZ val) = TZ <$> fn val
    tensorCTraverse {shape = (s :: ss)} fn (TS xs)
      = TS <$> ?alllao -- (fromVect <$> traverse (tensorCTraverse fn) (toVect xs))

    public export
    {shape : Vect n Nat} ->
    Traversable (Tensor' shape) where
      traverse f (MkT t) = MkT <$> tensorCTraverse f t

  public export
  dot' : {shape : Vect n Nat} -> {a : Type}
    -> Num a => AllAlgebra (vectApplV shape) a
    => Tensor' shape a -> Tensor' shape a -> Tensor' [] a
  dot' (MkT xs) (MkT ys) = MkT $ TZ $ reduce $ (\(x, y) => x * y) <$> liftA2Tensor xs ys

  public export
  Array' : (shape : Vect n Nat) -> (dtype : Type) -> Type
  Array' [] dtype = dtype
  Array' (s :: ss) dtype = Vect s (Array' ss dtype)

  public export
  fromArrayHelper : {shape : Vect n Nat}
    -> Array' shape a
    -> Tensor (vectApplV shape) a
  fromArrayHelper {shape=[]} x = TZ x
  fromArrayHelper {shape=(_ :: _)} x = TS $ fromVect $ fromArrayHelper <$> x

  public export
  fromArray' : {shape : Vect n Nat} -> Array' shape a -> Tensor' shape a
  fromArray' a = MkT $ fromArrayHelper a

namespace IndexT
  public export
  data IndexTData : Type where
    NonCubical : (shape : ApplV conts) -> IndexTData
    Cubical : (shape : Vect n Nat) -> IndexTData -- assuming every Naperian functor has shape=Fin d for some d, this describes Naperian Tensors

  -- vnn : IndexTData -> Type -> Type
  -- vnn (NonCubical shape) = Tensor shape
  -- vnn (Cubical shape) = \_ => Unit

  vnnn : (conts : Vect n ApplC) -> Cont
  vnnn conts = foldr ?acc CUnit (GetC <$> conts)

  -- ||| Tensors too are a container
  -- tensorCont : Type -> Cont
  -- tensorCont dtype = (s : IndexTData) !> vnn s
    
  ||| Machinery for indexing into a Tensor
  ||| For general, non-cubical tensors this depends on the tensor itself
  ||| TODO remove this dependence for cubical tensors
  public export
  data IndexT : (shape : ApplV conts) -> (t : Tensor shape dtype) -> Type where
    Nil : {val : dtype} -> IndexT [] (TZ val)
    (::) :  {e : ((!>) shp' pos') `fullOf` (Tensor cs dtype)} -> 
      Applicative (Ext ((!>) shp' pos')) =>
      (p : pos' (shapeExt e)) ->
      IndexT cs (indexCont e p) -> 
      IndexT ((!>) shp' pos' :: cs) (TS e)

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


namespace SliceT
  ||| Machinery for slicing cubical tensors
  ||| Crucially, different from the indexing one in the definition of (::)
  ||| Here we have Fin (S m) instead of Fin m
  public export
  data SliceT : (shape : Vect n Nat) -> Type where
    Nil : SliceT []
    (::) : Fin (S m) -> SliceT ms -> SliceT (m :: ms)

  public export
  sliceToShape : {shape : Vect n Nat} -> SliceT shape -> Vect n Nat
  sliceToShape Nil = []
  sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

  public export -- analogus to take in Data.Vect, but for Fin
  takeFinVect' : {n : Nat} ->
    (s : Fin (S n)) -> Vect' n a -> Vect' (finToNat s) a
  takeFinVect' s x = fromVect (takeFin s (toVect x))

  public export --
  takeTensor' : {shape : Vect n Nat} ->
    (slice : SliceT shape) ->
    Tensor' shape a ->
    Tensor' (sliceToShape slice) a
  takeTensor' [] (MkT (TZ val)) = MkT (TZ val)
  takeTensor' (s :: ss) (MkT (TS xs)) = MkT $ TS $ 
    (\t => GetT ((takeTensor' ss) (MkT t))) <$> takeFinVect' s xs




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
