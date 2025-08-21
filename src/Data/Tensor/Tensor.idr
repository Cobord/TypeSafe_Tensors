module Data.Tensor.Tensor

import public Data.Vect

import public Data.Container.Definitions
import public Data.Container.Instances
import public Data.Container.SubTerm

import public Data.Algebra
import public Data.Tree
import public Misc
import public Data.Functor.Naperian

%hide Builtin.infixr.(#)

{-----------------------------------------------------------
{-----------------------------------------------------------
This file defines the main constructions of this repository:
Applicative Tensors, Cubical Tensors, and functions for
working with them.

TensorA -> the main applicative tensor type
ConcreteT -> machinery for working with TensorA as nested Idris types
IndexT -> machinery for indexing into TensorA

This file also incluedes most common interfaces, such as
Eq, Show, Functor, Applicative, Foldable, Num,...


Tensor -> the main cubical tensor type
-----------------------------------------------------------}
-----------------------------------------------------------}

||| Applicative tensors
||| Tensors whose shape is a list of applicative containers
public export
data TensorA : (conts : List ContA) -> (dtype : Type) -> Type where
    ||| A scalar value can be turned into a tensor
    TZ : (val : dtype) -> TensorA [] dtype
    ||| A container 'c' full of 'Tensor shape cs' can be turned into
    ||| a tensor of shape (c :: cs)
    TS : (GetC c) `fullOf` (TensorA cs dtype) -> TensorA (c :: cs) dtype

%name TensorA t, t', t''

namespace FunctorTensorA
  public export
  Functor (TensorA shape) where
    map f (TZ val) = TZ $ f val
    map f (TS xs) = TS $ (map f) <$> xs

||| Functions for manipulating nested tensors
namespace NestedTensorA
  public export
  extract : TensorA [] a -> a
  extract (TZ a) = a

  public export
  toNestedA : TensorA (n :: ns) a -> TensorA [n] (TensorA ns a)
  toNestedA (TS vs) = TS (TZ <$> vs)

  public export
  fromNestedA : TensorA [n] (TensorA ns a) -> TensorA (n :: ns) a
  fromNestedA (TS vs) = TS $ extract <$> vs

  ||| Action of nesting on morphisms
  ||| Map, but for nested tensors
  public export
  tensorMapFirstAxisA : (f : TensorA ns a -> TensorA ms a) ->
    TensorA (i :: ns) a -> TensorA (i :: ms) a
  tensorMapFirstAxisA f = fromNestedA . map f . toNestedA

  public export infix 4 <-$
  public export infixr 4 $->
  public export infixr 4 <-$->

  public export
  (<-$) : TensorA (n :: ns) a -> TensorA [n] (TensorA ns a)
  (<-$) = toNestedA

  public export
  ($->) : TensorA [n] (TensorA ns a) -> TensorA (n :: ns) a
  ($->) = fromNestedA

  public export
  (<-$->) : (f : TensorA ns a -> TensorA ms a) ->
    TensorA (i :: ns) a -> TensorA (i :: ms) a
  (<-$->) = tensorMapFirstAxisA


{----------------------------
{----------------------------
It will be immensely useful to leverage the following fact about TensorA:
`Tensor shape a` is isomorphic to the extension of the container that arises as the composition of all the containers in shape.
For instance, `Tensor [c, d] a` is isomorphic to Ext (c . d) a

The maps defining this isomorphism are `toCompProduct` and `fromCompProduct`.

This allows us to define the reshape map using a dependent lens

That is, we have the following chain:
Tensor [c, d] a <=> Ext c (Ext d a) <=> Ext (c . d) a

The first isomorphism almost definitional - up to extra constructors.
Second isomorphism is the non-trivial one
----------------------------}
----------------------------}

||| This frames a tensor as a 
||| composition of extensions of containers making its shape
public export
toExtComposition : {shape : List ContA} ->
  TensorA shape a -> composeExtensionsA shape a
toExtComposition {shape = []} (TZ val) = fromIdentity val
toExtComposition {shape = (_ :: _)} (TS xs) = toExtComposition <$> xs

public export
fromExtComposition : {shape : List ContA} ->
  composeExtensionsA shape a -> TensorA shape a
fromExtComposition {shape = []} ce = TZ $ toIdentity ce
fromExtComposition {shape = (_ :: _)} ce = TS $ fromExtComposition <$> ce

-- TODO commented this out because I'm replacing ToContainerComp 
-- TODO I'm experimenting with being able to use Tensor as a literal container, and that requires 
-- getting rid of ToContainerComp as it requires composeExtensions to be public
-- we already have that functionality in a different place
-- ||| TODO which composition product (name unclear)? Composition product of containers, or composition of extensions of containers
-- public export
-- toCompProduct : {shape : List ContA} ->
--   TensorA shape a -> Ext (composeContainersA shape) a
-- toCompProduct = ToContainerComp . toExtComposition
-- 
-- public export
-- fromCompProduct : {shape : List ContA} ->
--   (composeContainersA shape) `fullOf` a -> TensorA shape a
-- fromCompProduct = fromExtComposition . FromContainerComp
-- 
-- ||| General, dependent-lens based applicative tensor reshaping
-- ||| Should capture views, traversals, and other ops that don't touch content 
-- public export
-- reshapeTensorA : {oldShape, newShape : List ContA} ->
--   (composeContainersA oldShape =%> composeContainersA newShape) ->
--   TensorA oldShape a -> TensorA newShape a
-- reshapeTensorA dLens = fromCompProduct . (contMapExt dLens) . toCompProduct


{----------------------------
ConcreteT
Convenience datatype and functions for constructing a TensorA.
For instance, it enables us to create a literal `TensorA [2, 3] Double`
by writing 
[ [1, 2, 3]
, [4, 5, 6]]
and without using the inductive definition via TS and TZ
----------------------------}

namespace ConcreteTensorA
  ||| A tensor has a concrete instance if all of its shape containers have a concete instance too
  public export
  data AllConcrete : (shape : List ContA) -> Type where
    Nil : AllConcrete []
    Cons : (fr : FromConcrete (GetC c)) =>
      (afr : AllConcrete cs) =>
      AllConcrete (c :: cs)
  
  ||| The input is a nested list of containers with a FromConcrete instance
  ||| Meaning they're matched to a concrete (usually inductively defined) Idris type
  public export
  ConcreteT : (shape : List ContA) ->
    (concr : AllConcrete shape) =>
    Type -> Type
  ConcreteT [] dtype = dtype
  ConcreteT {concr = Cons {fr}} (_ :: cs) dtype
    = concreteType @{fr} (ConcreteT cs dtype)
  
  public export
  fromConcreteA : {shape : List ContA} ->
    (concr : AllConcrete shape) =>
    ConcreteT shape dtype -> TensorA shape dtype
  fromConcreteA {shape = []} x = TZ x
  fromConcreteA {shape = (_ :: _)} {concr = Cons {fr = (MkConcrete f concreteFunctor fromConcreteFn _)}} xs
    = TS $ fromConcreteFn $ fromConcreteA <$> xs
  
  public export
  toConcreteA : {shape : List ContA} ->
    (concr : AllConcrete shape) =>
    TensorA shape dtype -> ConcreteT shape dtype
  toConcreteA (TZ val) = val
  toConcreteA {concr = Cons {fr = (MkConcrete f concreteFunctor _ toConcreteFn)} {afr} } (TS xs) = toConcreteFn $ toConcreteA {concr=afr} <$> xs
  
  public export
  fromConcreteMapA : {oldShape, newShape : List ContA} ->
    (ca : AllConcrete oldShape) => (cb : AllConcrete newShape) =>
    (f : ConcreteT oldShape a -> ConcreteT newShape b) ->
    TensorA oldShape a -> TensorA newShape b
  fromConcreteMapA f = fromConcreteA . f . toConcreteA

  -- public export
  -- {shape : List ContA} ->
  -- (concr : AllConcrete shape) => FromConcrete (composeContainersA shape) where
  --   concreteType = ConcreteT shape
  --   concreteFunctor = ?todooo -- %search TODO we'd need to write an AllFunctor instance? 
  --   fromConcreteTy = ?hhiii -- fromConcreteA
  --   toConcreteTy = ?vnnnn -- toConcreteA


namespace EqTensorA
  -- Different notions of equality, including np.allclose TODO
  public export
  data AllEq : (shape : List ContA) -> (dtype : Type) -> Type where
    Nil : Eq dtype => AllEq [] dtype
    Cons : Eq (GetC c `fullOf` TensorA cs dtype) =>
      AllEq (c :: cs) dtype

  public export
  tensorEq : {shape : List ContA} -> (allEq : AllEq shape dtype) =>
    TensorA shape dtype -> TensorA shape dtype -> Bool
  tensorEq {allEq = Nil} (TZ val) (TZ val') = val == val'
  tensorEq {allEq = Cons} (TS xs) (TS xs') = xs == xs'

  public export
  {shape : List ContA} ->
  (allEq : AllEq shape dtype) =>
  Eq (TensorA shape dtype) where
    (==) = tensorEq

  -- -- For now, for simplicity, simply extending typechecker's notion
  -- -- Is this the right notion? Have not seen a thing like this anywhere
  -- DecEq (TensorA shape dtype) => Eq (TensorA shape dtype) where
  --   t1 == t2 = case decEq t1 t2 of
  --     Yes Refl => True
  --     No _ => False
  -- gheq : Eq (TensorA [List, BinTree] Int)
  -- gheq = %search

namespace ShowTensorA
  public export
  data AllShow : (shape : List ContA) -> (dtype : Type) -> Type where
    Nil : Show dtype => AllShow [] dtype
    Cons : Show (GetC c `fullOf` TensorA cs dtype) =>
      AllShow (c :: cs) dtype

  -- public export
  -- Show a => Show (TensorA [] a) where
  --   show (TZ val) = show val


  -- showTensorList : Show a => TensorA [List] a -> String
  -- showTensorList (TS el) = show $ ConversionFunctions.toList el

  -- public export
  -- Show a => Show (TensorA [List] a) where
  --   show = showTensorList

  ||| TODO this works, but we need to actually implement pretty printing
  public export
  tensorShow : (allShow : AllShow shape dtype) =>
    TensorA shape dtype ->
    String
  tensorShow {allShow = Nil} (TZ val) = show val
  tensorShow {allShow = Cons} (TS xs) = show xs

  public export
  AllShow shape dtype => Show (TensorA shape dtype) where
      show = tensorShow

namespace ApplicativeTensorA
  {-----------
  Unlike with other interfaces, Applicative is baked in to TensorA
  This means that we do not need an AllApplicative data type here.
  -----------}

  ||| Unit of the monoidal functor
  public export
  tensorReplicateA : {shape : List ContA}
    -> a -> TensorA shape a
  tensorReplicateA {shape = []} a = TZ a
  tensorReplicateA {shape = ((# c) :: cs)} a = TS $ pure (tensorReplicateA a)

  ||| Laxator of the monoidal functor
  public export
  liftA2TensorA : {shape : List ContA} ->
    TensorA shape a -> TensorA shape b -> TensorA shape (a, b)
  liftA2TensorA {shape = []} (TZ a) (TZ b) = TZ (a, b)
  liftA2TensorA {shape = ((# c) :: cs)} (TS xs) (TS ys)
    = TS $ uncurry liftA2TensorA <$> (liftA2 xs ys)

  public export
  {shape : List ContA} -> Applicative (TensorA shape) where
    pure = tensorReplicateA 
    fs <*> xs = uncurry ($) <$> liftA2TensorA fs xs 
  
namespace NumericTensorA
  public export
  {shape : List ContA} -> Num a => Num (TensorA shape a) where
    fromInteger i = pure (fromInteger i)
    xs + ys = (uncurry (+)) <$> liftA2 xs ys
    xs * ys = (uncurry (*)) <$> liftA2 xs ys

  public export
  {shape : List ContA} -> Neg a => Neg (TensorA shape a) where
    negate = (negate <$>)
    xs - ys = (uncurry (-)) <$> liftA2 xs ys

  public export
  {shape : List ContA} -> Abs a => Abs (TensorA shape a) where
    abs = (abs <$>)

  public export
  {shape : List ContA} -> Fractional a => Fractional (TensorA shape a) where
    t / v = (uncurry (/)) <$> liftA2 t v

  public export
  {shape : List ContA} -> Exp a => Exp (TensorA shape a) where
    exp = (exp <$>)


namespace NaperianTensorA
  public export
  data AllNaperian : (shape : List ContA) -> Type where
    Nil : AllNaperian []
    (::) : (napC : Naperian (Ext (GetC c))) =>
      AllNaperian cs ->
      AllNaperian (c :: cs)

  namespace IndexTNaperian
    ||| Datatype for indexing into TensorA 
    ||| It made out of containers whose extensions are Naperian
    ||| Meaning we don't need the tensor *term* to be able to index into it, just the type
    ||| TODO need to use this in the rest of the code
    public export
    data IndexTNaperian : (shape : List ContA) -> AllNaperian shape -> Type where
      Nil : IndexTNaperian [] []
      (::) : (napC : Naperian (Ext (GetC c))) =>
        Log {f=(Ext (GetC c))} ->
        {allNapsCs : AllNaperian cs} ->
        IndexTNaperian cs allNapsCs ->
        IndexTNaperian (c :: cs) ((::) allNapsCs)
  
  
  public export
  tensorTabulate : {shape : List ContA} -> (allNaperian : AllNaperian shape) -> (IndexTNaperian shape allNaperian -> a) -> TensorA shape a
  tensorTabulate {shape = []} [] f = TZ $ f []
  tensorTabulate {shape = (_ :: _)} ((::) applS) f
    = TS $ tabulate $ \i => tensorTabulate applS $ \is => f (i :: is)
  
  public export
  {shape : List ContA} ->
  (allNaperian : AllNaperian shape) =>
  Naperian (TensorA shape) where
    Log = IndexTNaperian shape allNaperian
    lookup {allNaperian = []} (TZ val) [] = val
    lookup {allNaperian = ((::) _)} (TS xs) (i :: is) = lookup (lookup xs i) is
    tabulate {allNaperian} = tensorTabulate allNaperian
  
  public export
  transposeMatrixA : {i, j : ContA} ->
    (allNaperian : AllNaperian [i, j]) =>
    TensorA [i, j] a -> TensorA [j, i] a
  transposeMatrixA {allNaperian = ((::) {napC=napI} ((::) {napC=napJ} []))}
    = fromExtComposition . Naperian.transpose . toExtComposition

  ||| Not requiring the Naperian instance here
  public export
  positions : {c : ContA} ->
    {sh : c.shp} -> TensorA [c] (c.pos sh)
  positions = TS (TZ <$> positionsCont)

  -- public export
  -- data IndexTData : Type where
  --   NonCubical : (shape : ContAontList conts) -> IndexTData
  --   Cubical : (shape : Vect n Nat) -> IndexTData -- assuming every Naperian functor has shape=Fin d for some d, this describes Naperian TensorAs

  -- vnn : IndexTData -> Type -> Type
  -- vnn (NonCubical shape) = TensorA shape
  -- vnn (Cubical shape) = \_ => Unit




namespace AlgebraTensorA
  -- Unlike all other instantiations of 'AllX', this one isn't individually stating they're algebras, but rather cumulatively. 
  -- i.e. AllAlgebra [c, d] a is not defined as Algebra c a and Algebra d a, bur rather as Algebra c (Algebra d a)
  public export
  data AllAlgebra : (shape : List ContA) -> (dtype : Type) -> Type where
    Nil : AllAlgebra [] a
    (::) : {c : ContA} -> {cs : List ContA} ->
      (alg : Algebra (Ext (GetC c)) (TensorA cs a)) =>
      (allAlg : AllAlgebra cs a) =>
      AllAlgebra (c :: cs) a

  public export
  reduceTensorA : {shape : List ContA} ->
    (allAlg : AllAlgebra shape a) =>
    TensorA shape a -> a
  reduceTensorA {allAlg = []} (TZ val) = val
  reduceTensorA {allAlg = ((::) {allAlg=cs})} (TS xs)
    = reduceTensorA $ reduce xs


  public export
  {shape : List ContA} ->
  (allAlgebra : AllAlgebra shape a) =>
  Algebra (TensorA shape) a where
    reduce = reduceTensorA

  agtest0 : Algebra BinTreeNode Int
  agtest0 = %search

  agt0 : AllAlgebra [BinTreeNode] Int
  agt0 = %search

  agt : AlgebraTensorA.AllAlgebra [BinTreeNode, Vect 7] Int
  agt = %search

  agtest : Algebra (TensorA [BinTreeNode, Vect 7]) Int
  agtest = %search

  public export
  [appSumTensorA] {c : ContA} ->{shape : List ContA} ->
    {a : Type} -> Num a =>
    (allAlg : AllAlgebra shape a) =>
    Algebra (TensorA shape) ((Ext (GetC c)) a) where
      reduce {allAlg = []} (TZ val) = val
      reduce {shape=(c::cs)} {allAlg = ((::) {allAlg=alg})} (TS xs) -- = ?fvhvh_2
        = ?neww
       --  let t = reduce {f=(TensorA cs)} <$> xs
       --    in ?ghhh -- reduce (reduce <$> xs)


namespace FoldableTensorA
  public export
  data AllFoldable : (shape : List ContA) -> Type where
      Nil : AllFoldable []
      Cons : Foldable (Ext (GetC c)) =>
        AllFoldable cs ->
        AllFoldable (c :: cs)


  public export
  tensorFoldrA : (allFoldable : AllFoldable shape) =>
    (el -> acc -> acc) -> acc -> TensorA shape el -> acc
  tensorFoldrA {allFoldable = Nil} f z (TZ val) = f val z
  tensorFoldrA {allFoldable = (Cons recAllFoldable)} f z (TS xs) =
      foldr (\t, acc => tensorFoldrA {allFoldable=recAllFoldable} f acc t) z xs

  public export
  {shape : List ContA} ->
  (allFoldable : AllFoldable shape) =>
  Foldable (TensorA shape) where
    foldr = tensorFoldrA


namespace TensorAContractions
  public export
  dotA : {shape : List ContA} -> Num a => Algebra (TensorA shape) a =>
    TensorA shape a -> TensorA shape a -> TensorA [] a
  dotA xs ys = TZ $ reduce $ (\(x, y) => x * y) <$> liftA2TensorA xs ys

  public export
  outerAWithFn : {i, j : ContA} -> (a -> b -> c) ->
    TensorA [i] a -> TensorA [j] b -> TensorA [i, j] c
  outerAWithFn f t t' =
    let tt = (\(t, a) => strength a t) <$> strength t' t
    in uncurry f <$> fromNestedA tt

  public export
  outerA : {i, j : ContA} -> {a : Type} -> Num a =>
    TensorA [i] a -> TensorA [j] a -> TensorA [i, j] a
  outerA = outerAWithFn (*)


  -- Multiply a matrix and a vector
  public export
  matrixVectorProductA : {f, g : ContA} -> Num a => AllAlgebra [g] a =>
    TensorA [f, g] a -> TensorA [g] a -> TensorA [f] a
  matrixVectorProductA (TS m) v = TS (dotA v <$> m)

  -- Multiply a vector and a matrix
  public export
  vectorMatrixProductA : Num a => (allAlg : AllAlgebra [f, g] a) =>
    TensorA [f] a -> TensorA [f, g] a -> TensorA [g] a
  vectorMatrixProductA {f=(# fc)} {allAlg = (::)} (TS v) (TS m)
    = let t = liftA2 v m
          w = (\((TZ val), v') => (val *) <$> v') <$> t
      in reduce {f=(Ext fc)} w

  -- ij,jk->ik
  public export
  matMulA : Num a => AllAlgebra [g, h] a =>
    TensorA [f, g] a -> TensorA [g, h] a -> TensorA [f, h] a
  matMulA (TS m1) m2 = TS $ m1 <&> (\row => vectorMatrixProductA row m2)

  -- ij,kj->ki
  public export
  matrixMatrixProductA : {f, g, h : ContA} -> Num a =>
    (allAlgebra : AllAlgebra [g] a) =>
    TensorA [f, g] a -> TensorA [h, g] a -> TensorA [h, f] a
  matrixMatrixProductA m (TS n) = TS (matrixVectorProductA m <$> n)



namespace CubicalTensor
  ||| This is a helper datatype for cubical tensors, i.e. those made only out of Vect
  ||| It allows specifying a tensor only by the size of the content, and is needed (instead of Tensor') to aid type inference
  ||| There might be a more ergonomic way to do this
  public export
  record Tensor (shape : List Nat) a where
    constructor ToCubicalTensor
    FromCubicalTensor : TensorA (Vect <$> shape) a

  public export
  FromCubicalTensorMap : (Tensor oldShape a -> Tensor newShape b) ->
    TensorA (Vect <$> oldShape) a -> TensorA (Vect <$> newShape) b
  FromCubicalTensorMap f = FromCubicalTensor . f . ToCubicalTensor

  public export
  ToCubicalTensorMap :
    (TensorA (Vect <$> oldShape) a ->  TensorA (Vect <$> newShape) b) ->
    Tensor oldShape a -> Tensor newShape b
  ToCubicalTensorMap f = ToCubicalTensor . f . FromCubicalTensor

  public export
  ToCubicalTensorRel : {shape : List Nat} ->
    (TensorA (Vect <$> shape) a -> TensorA (Vect <$> shape) b -> c) ->
    Tensor shape a -> Tensor shape b -> c
  ToCubicalTensorRel f t t' = f (FromCubicalTensor t) (FromCubicalTensor t')

  public export
  FromCubicalTensorRel : {shape : List Nat} ->
    (Tensor shape a -> Tensor shape b -> c) ->
    TensorA (Vect <$> shape) a -> TensorA (Vect <$> shape) b -> c
  FromCubicalTensorRel f t t' = f (ToCubicalTensor t) (ToCubicalTensor t')

  namespace TensorInterfaces
    public export
    {shape : List Nat} ->
    AllEq (Vect <$> shape) a =>
    Eq (Tensor shape a) where
        (==) = ToCubicalTensorRel (==)

    public export
    {shape : List Nat} ->
    AllShow (Vect <$> shape) a =>
    Show (Tensor shape a) where
      show (ToCubicalTensor t) = show t

    public export
    {shape : List Nat} ->
    Num a =>
    Num (Tensor shape a) where
      fromInteger i = ToCubicalTensor $ fromInteger {ty=(TensorA (Vect <$> shape) a)} i
      (ToCubicalTensor xs) + (ToCubicalTensor ys) = ToCubicalTensor $ (+) {ty=(TensorA (Vect <$> shape) a)} xs ys
      (ToCubicalTensor xs) * (ToCubicalTensor ys) = ToCubicalTensor $ (*) {ty=(TensorA (Vect <$> shape) a)} xs ys

    public export
    {shape : List Nat} ->
    Neg a =>
    Neg (Tensor shape a) where
      negate (ToCubicalTensor t) = ToCubicalTensor $ negate t
      (ToCubicalTensor xs) - (ToCubicalTensor ys) = ToCubicalTensor $ (-) {ty=(TensorA (Vect <$> shape) a)} xs ys

    public export
    {shape : List Nat} -> Abs a => Abs (Tensor shape a) where
      abs = ToCubicalTensorMap abs

    public export
    Functor (Tensor shape) where
      map f = ToCubicalTensorMap (map f)

    public export
    liftA2Tensor : {shape : List Nat} -> Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
    liftA2Tensor (ToCubicalTensor xs) (ToCubicalTensor ys)
      = ToCubicalTensor (liftA2TensorA xs ys)

    public export
    {shape : List Nat} ->
    Applicative (Tensor shape) where
      pure = ToCubicalTensor . tensorReplicateA
      fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs

    public export
    {shape : List Nat} ->
    AlgebraTensorA.AllAlgebra (Vect <$> shape) a =>
    Algebra (Tensor shape) a where
        reduce (ToCubicalTensor t) = reduce t

    public export
    tensorFoldr : {shape : List Nat} ->
      (el -> acc -> acc) -> acc -> TensorA (Vect <$> shape) el -> acc
    tensorFoldr {shape = []} f z t = foldr f z t
    tensorFoldr {shape = (s :: ss)} f z (TS xs)
      = foldr (\t, acc => tensorFoldr f acc t) z xs


    public export
    {shape : List Nat} ->
    Foldable (Tensor shape) where
      foldr f z (ToCubicalTensor t) = tensorFoldr f z t

    -- public export
    -- {shape : List Nat} ->
    -- Foldable (TensorA (Vect <$> shape)) where
    --   foldr f z t = tensorFoldr f z t


    -- TODO implement Traversable for TensorA, and then port it here
    -- public export
    -- tensorTraverseA : {shape : List Nat} -> Applicative f =>
    --   (a -> f b) -> TensorA (NatsToContAonts shape) a -> f (TensorA (NatsToContAonts shape) b)
    -- tensorTraverseA {shape = []} fn (TZ val) = TZ <$> fn val
    -- tensorTraverseA {shape = (s :: ss)} fn (TS xs)
    --   = TS <$> (fromVect <$> traverse (tensorCTraverse fn) (toVect xs))

    -- public export
    -- {shape : List Nat} ->
    -- Traversable (Tensor shape) where
    --   traverse f (ToCubicalTensor t) = ToCubicalTensor <$> tensorTraverseA f t

  public export
  dot : {shape : List Nat} -> {a : Type}
    -> Num a => Algebra (TensorA (Vect <$> shape)) a
    => Tensor shape a -> Tensor shape a -> Tensor [] a
  dot t t' = ToCubicalTensor (dotA (FromCubicalTensor t) (FromCubicalTensor t'))


  public export
  outerWithFn : {i, j : Nat} -> {a : Type} -> (a -> b -> c) ->
    Tensor [i] a -> Tensor [j] b -> Tensor [i, j] c
  outerWithFn f t t' = ToCubicalTensor $
    outerAWithFn f (FromCubicalTensor t) (FromCubicalTensor t')

  public export
  outer : {i, j : Nat} -> {a : Type} -> Num a =>
    Tensor [i] a -> Tensor [j] a -> Tensor [i, j] a
  outer = outerWithFn (*)

  public export
  transposeMatrix : {i, j : Nat} ->
    Tensor [i, j] a -> Tensor [j, i] a
  transposeMatrix = ToCubicalTensor . transposeMatrixA . FromCubicalTensor


  public export
  matMul : {i, j, k : Nat} -> {a : Type} -> Num a =>
    Tensor [i, j] a -> Tensor [j, k] a -> Tensor [i, k] a
  matMul m n = ToCubicalTensor $
    matMulA (FromCubicalTensor m) (FromCubicalTensor n)

  public export
  Array : (shape : List Nat) -> (dtype : Type) -> Type
  Array [] dtype = dtype
  Array (s :: ss) dtype = Vect s (Array ss dtype)

  public export
  fromArrayHelper : {shape : List Nat}
    -> Array shape a
    -> TensorA (Vect <$> shape) a
  fromArrayHelper {shape=[]} a = TZ a
  fromArrayHelper {shape=(s :: ss)} xs
    = TS $ fromVect $ fromArrayHelper <$> xs

  public export
  toArrayHelper : {shape : List Nat} ->
    TensorA (Vect <$> shape) a -> Array shape a
  toArrayHelper {shape = []} (TZ a) = a
  toArrayHelper {shape = (s :: ss)} (TS xs) = toVect $ toArrayHelper <$> xs

  public export
  fromConcrete : {shape : List Nat} -> Array shape a -> Tensor shape a
  fromConcrete = ToCubicalTensor . fromArrayHelper
  -- ToCubicalTensor . fromConcrete . fromArrayHelper

  public export
  toConcrete : {shape : List Nat} -> Tensor shape a -> Array shape a
  toConcrete = toArrayHelper . FromCubicalTensor

  public export
  reshapeDLens : {oldShape, newShape : List ContA} ->
    composeContainersA oldShape =%> composeContainersA newShape
  reshapeDLens = ?ff <%! ?bbbw

  -- TODO reshape commented out for the same reason as reshapeTensorA is
  -- public export
  -- reshape : {oldShape, newShape : List Nat} ->
  --   Tensor oldShape a ->
  --   {auto prf : prod oldShape = prod newShape} ->
  --   Tensor newShape a
  -- reshape t = ToCubicalTensorMap (reshapeTensorA reshapeDLens) t
  -- reshape t = ToCubicalTensorMap (reshapeTensorA (cubicalTensorToFlat %>>  %>> flatToCubicalTensor)) t



namespace IndexTensor
  ||| Machinery for indexing into a TensorA
  ||| It depends on shape, but also on the tensor t itself
  ||| Provides a compile-time guarantee that we won't be out of bounds
  ||| This dependency is not needed for cubical tensors
  ||| TODO remove this dependence for cubical tensors
  public export
  data IndexTA : (shape : List ContA) -> (t : TensorA shape dtype) -> Type where
    Nil : {val : dtype} -> IndexTA [] (TZ val)
    (::) :  {e : ((!>) sh ps) `fullOf` (TensorA cs dtype)} -> 
      Applicative (Ext ((!>) sh ps)) =>
      (p : ps (shapeExt e)) ->
      IndexTA cs (indexCont e p) -> 
      IndexTA ((# ((!>) sh ps)) :: cs) (TS e)

  public export
  indexTensorA : (t : TensorA shape a) -> (index : IndexTA shape t) -> a
  indexTensorA (TZ val) [] = val
  indexTensorA (TS xs) (i :: is) = indexTensorA (indexCont xs i) is 

  public export infixr 9 @@ -- Why can't I use @ here?
  public export
  (@@) : (t : TensorA shape a) -> IndexTA shape t -> a
  (@@) = indexTensorA

  -- Lens-like syntax for a Tensor getter
  public export infixr 9 ^. -- Why can't I use @ here?
  public export
  (^.) : (t : TensorA shape a) -> IndexTA shape t -> a
  (^.) = indexTensorA

  namespace AllPosEqNamespace
    public export
    data AllPosEq : (shape : List ContA) -> Type where
      Nil : AllPosEq []
      ConsPosEq : {c : ContA} -> {cs : List ContA} ->
        (apecs : AllPosEq cs) =>
        (pe : (s : (GetC c).shp) -> Eq ((GetC c).pos s)) =>
        AllPosEq (c :: cs)

    -- hm, why isn't this hint found in the cubical part?
    %hint
    public export
    allPosEqCubical : {shape : List Nat} ->
      AllPosEq (Vect <$> shape)
    allPosEqCubical {shape = []} = []
    allPosEqCubical {shape = (_ :: _)} = ConsPosEq {apecs=allPosEqCubical}
      

  -- Lens-like syntax for a Tensor setter
  public export infixr 9 .~
  public export
  (.~) : (allPosEq : AllPosEq shape) =>
    (t : TensorA shape a) -> IndexTA shape t -> a -> TensorA shape a
  (.~) {allPosEq = []} (TZ _) [] val = TZ val
  (.~) {allPosEq = (ConsPosEq)} (TS xs) (i :: is) val
    = TS $ setExt xs i ((.~) (indexCont xs i) is val)


  namespace CubicalIndex
    -- -- ideally we'd remove the allNonZero consraint in the future, but it shouldn't impact things too much for now
    public export
    indexTensor : {shape : List Nat} ->
      (t : Tensor shape a) ->
      (ind : IndexTA (Vect <$> shape) (FromCubicalTensor t)) ->
      a
    indexTensor t index = indexTensorA (FromCubicalTensor t) index

    public export infixr 9 @@
    public export
    (@@) : {shape : List Nat} ->
      (t : Tensor shape a) ->
      (ind : IndexTA (Vect <$> shape) (FromCubicalTensor t)) ->
      a
    (@@) = indexTensor

    public export infixr 9 ^.
    public export
    (^.) : {shape : List Nat} ->
      (t : Tensor shape a) ->
      (ind : IndexTA (Vect <$> shape) (FromCubicalTensor t)) ->
      a
    (^.) = indexTensor


    -- todo figure out how to use the ampersand syntax here 
    public export infixr 9 .~
    public export
    (.~) : {shape : List Nat} ->
      (t : Tensor shape a) ->
      IndexTA (Vect <$> shape) (FromCubicalTensor t) ->
      a ->
      Tensor shape a
    (.~) t i val = ToCubicalTensor $
      (.~) {allPosEq=allPosEqCubical} (FromCubicalTensor t) i val



namespace SliceTensor
  ||| Machinery for slicing cubical tensors
  ||| Crucially, different from the indexing one in the definition of (::)
  ||| Here we have Fin (S m) instead of Fin m
  public export
  data SliceT : (shape : List Nat) -> Type where
    Nil : SliceT []
    (::) : Fin (S m) -> SliceT ms -> SliceT (m :: ms)

  ||| Computes the shape of the tensor after the slicing
  public export
  sliceToShape : {shape : List Nat} -> SliceT shape -> List Nat
  sliceToShape Nil = []
  sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

  -- analogus to take in Data.Vect, but for Fin
  public export 
  takeFinVect' : {n : Nat} ->
    (s : Fin (S n)) -> Vect' n a -> Vect' (finToNat s) a
  takeFinVect' s x = fromVect (takeFin s (toVect x))

  public export --
  takeTensor : {shape : List Nat} ->
    (slice : SliceT shape) ->
    Tensor shape a ->
    Tensor (sliceToShape slice) a
  takeTensor [] (ToCubicalTensor (TZ val)) = ToCubicalTensor (TZ val)
  takeTensor (s :: ss) (ToCubicalTensor (TS xs)) = ToCubicalTensor $ TS $ 
    (\t => FromCubicalTensor ((takeTensor ss) (ToCubicalTensor t))) <$> takeFinVect' s xs

  -- namespace FullSlicing
  --   -- Supporting optional exclusion of an axis in slicing
  --   -- i.e. t[2, :, 1, :] notation
  --   public export
  --   data MSliceT : (shape : List Nat) -> Type where
  --     Nil : MSliceT []
  --     (::) : Maybe (Fin (S m)) -> MSliceT ms -> MSliceT (m :: ms)

  --   ||| Computes the shape of the tensor after the slicing
  --   public export
  --   msliceToShape : {shape : List Nat} -> MSliceT shape -> List Nat
  --   msliceToShape [] = []
  --   msliceToShape {shape = (s :: _)} (Nothing :: sls) = s :: msliceToShape sls
  --   msliceToShape ((Just sl) :: sls) = finToNat sl :: msliceToShape sls
  --   
  --   -- sliceToShape Nil = []
  --   -- sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

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