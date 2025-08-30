module Data.Tensor.TensorCont

import Data.DPair

import public Data.Container

import public Misc

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file re-exports the Tensor container constructions and provides utilities
for working with them.

Includes instances such as:
Functor, Applicative, Foldable, Naperian, Algebra, Eq, Show, Num, Neg, Abs,
Fractional, Exp

Functionality such as
* Converting to and from nested tensors
* Converting to and from concrete types
* Various tensor contractions
* Setters and getters (TODO)
* Slicing for cubical tensors (TODO)


setters/getters and slicing is implemented, finishing UtilsCont is possible

And then architectures can be tested?

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}


-- can later add ContA if needed
||| Need to wrap it in a record to help type inference
public export
record CTensor (shape : List Cont) (a : Type) where
  constructor MkT
  GetT : Ext (Tensor shape) a

%name CTensor t, t', t''

||| Cubical tensors
public export
Tensor : (shape : List Nat) -> Type -> Type
Tensor shape = CTensor (Vect <$> shape)

public export
Functor (CTensor shape) where
  map f (MkT t) = MkT $ map f t

namespace NestedTensorUtils
  public export
  extract : CTensor [] a -> a
  extract (MkT t) = extract t

  public export
  embed : a -> CTensor [] a
  embed a = MkT (toScalar a)

  ||| With the added data of the wrapper around (Ext (Tensor shape) a), this
  ||| effectively states a list version of the following isomorphism 
  ||| Ext c . Ext d = Ext (c . d)
  public export
  fromExtensionComposition : {shape : List Cont} ->
    composeExtensions shape a -> CTensor shape a
  fromExtensionComposition {shape = []} ce = MkT ce
  fromExtensionComposition {shape = (_ :: _)} (sh <| contentAt) = MkT $
    let rest = GetT . fromExtensionComposition . contentAt
    in (sh <| shapeExt . rest) <| \(cp ** fsh) => index (rest cp) fsh
  
  public export
  toExtensionComposition : {shape : List Cont} ->
    CTensor shape a -> composeExtensions shape a
  toExtensionComposition {shape = []} (MkT t) = t
  toExtensionComposition {shape = (_ :: _)} (MkT ((csh <| cpos) <| idx))
    = csh <| \d => toExtensionComposition (MkT (cpos d <| curry idx d))

  ||| For this and the function below, the commented out definition is cleaner 
  ||| but it requires non-erased `c` and `cs`
  public export
  extractTopExt : CTensor (c :: cs) a -> Ext c (CTensor cs a)
  extractTopExt (MkT (sh <| ind)) = shapeExt sh <| \p => MkT $ index sh p <| \p' => ind (p ** p')
  -- extractTopExt t = fromExtensionComposition <$> toExtensionComposition t

  public export
  embedTopExt : Ext c (CTensor cs a) -> CTensor (c :: cs) a
  embedTopExt e =
    let tp = GetT . index e
    in MkT $ (shapeExt e <| shapeExt . tp) <| \(p ** p') => index (tp p) p'
  --embedTopExt e = fromExtensionComposition  $ toExtensionComposition <$> e

  ||| This is useful because container composition adds non-trivial data to the
  ||| vector type (i.e. `c >@ Scalar` is not equal to `c`)
  public export
  extToVector : Ext c a -> CTensor [c] a
  extToVector e = MkT $ (shapeExt e <| \_ => ()) <| \(cp ** ()) => index e cp
   
  public export
  vectorToExt : CTensor [c] a -> Ext c a
  vectorToExt (MkT t) = shapeExt (shapeExt t) <| \cp => index t (cp ** ())

  public export
  toNestedTensor : CTensor (c :: cs) a -> CTensor [c] (CTensor cs a)
  toNestedTensor = extToVector . extractTopExt

  public export
  fromNestedTensor : CTensor [c] (CTensor cs a) -> CTensor (c :: cs) a
  fromNestedTensor = embedTopExt . vectorToExt 

  public export
  tensorMapFirstAxis : (f : CTensor cs a -> CTensor ds a) ->
    CTensor (c :: cs) a -> CTensor (c :: ds) a
  tensorMapFirstAxis f = fromNestedTensor . map f . toNestedTensor

namespace TensorFromConcrete
  public export
  concreteTypeTensor : (shape : List Cont) ->
    (allConcrete : AllConcrete shape) =>
    Type -> Type
  concreteTypeTensor [] {allConcrete = []} = concreteType {cont=Scalar}
  concreteTypeTensor (c :: cs) {allConcrete = Cons @{fc}}
    = (concreteType @{fc}) . (concreteTypeTensor cs)
  
  public export
  concreteTypeFunctor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    Functor (concreteTypeTensor shape)
  concreteTypeFunctor {shape = []} {allConcrete = []}
    = concreteFunctor {cont=Scalar}
  concreteTypeFunctor {shape = (c :: cs)} {allConcrete = Cons @{fc}}
    = Functor.Compose @{concreteFunctor @{fc} } @{concreteTypeFunctor}
  
  
  public export
  concreteToExtensions : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> composeExtensions shape a
  concreteToExtensions {shape = []} {allConcrete = []} ct = fromConcreteTy ct
  concreteToExtensions {shape = (_ :: _)} {allConcrete = Cons} ct = 
    concreteToExtensions <$> fromConcreteTy ct 
  
  public export
  extensionsToConcreteType : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    composeExtensions shape a -> concreteTypeTensor shape a
  extensionsToConcreteType {shape = []} {allConcrete = []} ct = toConcreteTy ct
  extensionsToConcreteType {shape = (_ :: _)} {allConcrete = Cons @{fc}} ct 
    = (map @{concreteFunctor @{fc}} extensionsToConcreteType) (toConcreteTy ct)
  
  public export
  toTensor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> CTensor shape a
  toTensor = fromExtensionComposition . concreteToExtensions
  
  public export
  fromTensor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    CTensor shape a -> concreteTypeTensor shape a
  fromTensor = extensionsToConcreteType . toExtensionComposition

  ||| Many containers have a `FromConcrete` instance, allowing them to easily
  ||| be converted to and from a (usually familiar) Idris type
  ||| This works with tensors defined as a fold over contianers, but it requires
  ||| burdensome shape annotations everywhere
  ||| The decision was made to wrap that fold in `CTensor` as above, and then
  ||| (as this isn't a container anymore) provide equally named functions like
  ||| the ones `FromConcrete` provides. Idris' name resolution should be able to
  ||| detect which one needs to be used at call sites seamlessly
  public export
  fromConcreteTy : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> CTensor shape a
  fromConcreteTy = toTensor
  
  public export
  toConcreteTy : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    CTensor shape a -> concreteTypeTensor shape a
  toConcreteTy = fromTensor


namespace TensorInstances
  namespace ApplicativeInstance
    public export
    tensorReplicate : {shape : List Cont} ->
      (allAppl : AllApplicative shape) =>
      (x : a) -> CTensor shape a
    tensorReplicate {shape = []} x = embed x
    tensorReplicate {shape = (_ :: _)} {allAppl = Cons} x
      = fromExtensionComposition
      $ pure
      $ toExtensionComposition
      $ tensorReplicate x
  
    public export
    liftA2Tensor : {shape : List Cont} ->
      (allAppl : AllApplicative shape) =>
      CTensor shape a -> CTensor shape b -> CTensor shape (a, b)
    liftA2Tensor {shape = []} (MkT t) (MkT t') = embed (index t (), index t' ())
    liftA2Tensor {shape = (_ :: _)} {allAppl = Cons} t t' = embedTopExt $
      uncurry liftA2Tensor <$> liftA2 (extractTopExt t) (extractTopExt t')
  
    public export
    {shape : List Cont} -> (allAppl : AllApplicative shape) =>
    Applicative (CTensor shape) where
      pure = tensorReplicate
      fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs

  namespace EqInstance
    public export
    data AllEq : List Cont -> Type -> Type where
      Nil : Eq a => AllEq [] a
      Cons : Eq (c `fullOf` CTensor cs a) =>
        AllEq (c :: cs) a

    public export
    tensorEq : {shape : List Cont} -> (allEq : AllEq shape a) =>
      CTensor shape a -> CTensor shape a -> Bool
    tensorEq {allEq = []} t1 t2 = extract t1 == extract t2
    tensorEq {allEq = Cons} t1 t2 = (extractTopExt t1) == (extractTopExt t2)

    public export
    {shape : List Cont} -> (allEq : AllEq shape a) =>
      Eq (CTensor shape a) where
        (==) = tensorEq {allEq = allEq}

    {n : Nat} -> Eq ((cp : Fin n ** ())) where
      x == y = fst x == fst y

    -- Turns out only this is sufficient for the setC function to work
    %hint
    public export
    interfacePosEq : {n : Nat} -> InterfaceOnPositions (Examples.Tensor [Vect n]) Eq
    interfacePosEq = MkI

  -- public export
  -- vectInterfacePos : {n : Nat} -> InterfaceOnPositions (Vect n) DecEq
  -- vectInterfacePos = MkI 

  namespace AlgebraInstance
    -- Unlike all other instantiations of 'AllX', this one isn't individually stating they're algebras, but rather cumulatively. 
    -- i.e. AllAlgebra [c, d] a is not defined as Algebra c a and Algebra d a, bur rather as Algebra c (Algebra d a)
    public export
    data AllAlgebra : (shape : List Cont) -> (dtype : Type) -> Type where
      Nil : AllAlgebra [] a
      Cons : (alg : Algebra (Ext c) (CTensor cs a)) =>
        (rest : AllAlgebra cs a) =>
        AllAlgebra (c :: cs) a

    public export
    reduceTensor : {shape : List Cont} ->
      (allAlg : AllAlgebra shape a) =>
      CTensor shape a -> a
    reduceTensor {allAlg = []} = extract
    reduceTensor {allAlg = Cons} = reduceTensor . reduce . extractTopExt

    public export
    {shape : List Cont} -> (allAlg : AllAlgebra shape a) =>
      Algebra (CTensor shape) a where
      reduce = reduceTensor 

  namespace FoldableInstance
    public export
    data AllFoldable : (shape : List Cont) -> Type where
        Nil : AllFoldable []
        Cons : Foldable (Ext c) =>
          AllFoldable cs =>
          AllFoldable (c :: cs)

    public export
    tensorFoldr : (allFoldable : AllFoldable shape) =>
      (a -> acc -> acc) -> acc -> CTensor shape a -> acc
    tensorFoldr {allFoldable = []} f val t = f (extract t) val
    tensorFoldr {allFoldable = Cons} f val t = foldr
      (\ct, acc => tensorFoldr f acc ct) val (extractTopExt t)

    public export
    {shape : List Cont} -> (allFoldable : AllFoldable shape) =>
    Foldable (CTensor shape) where
      foldr = tensorFoldr

  namespace NaperianInstance
    public export
    data AllNaperian : (shape : List Cont) -> Type where
      Nil : AllNaperian []
      Cons : (nap : Naperian (Ext c)) =>
        (rest : AllNaperian cs) =>
        AllNaperian (c :: cs)

    namespace Index
      ||| Datatype for indexing into a tensor
      public export
      data IndexNaperian : (shape : List Cont) ->
        (allNap : AllNaperian shape) =>
        Type where
        Nil : IndexNaperian []
        (::) : (nap : Naperian (Ext c)) =>
          (rest : AllNaperian cs) =>
          Log {f=(Ext c)} ->
          IndexNaperian cs {allNap=rest} ->
          IndexNaperian (c :: cs) {allNap=Cons {rest=rest}}

    public export
    tensorLookup : {shape : List Cont} ->
      (allNaperian : AllNaperian shape) =>
      CTensor shape a ->
      (IndexNaperian shape -> a)
    tensorLookup {shape = []} t _ = extract t
    tensorLookup {shape = (c :: cs)} {allNaperian = Cons} t (i :: is)
      = tensorLookup (lookup (extractTopExt t) i) is

    public export
    tensorTabulate : {shape : List Cont} -> (allNaperian : AllNaperian shape) =>
      (IndexNaperian shape -> a) -> CTensor shape a
    tensorTabulate {shape = []} {allNaperian = []} f = embed (f Nil)
    tensorTabulate {shape = (_ :: _)} {allNaperian = Cons} f
      = embedTopExt $ tabulate $ \i => tensorTabulate $ \is => f (i :: is)

    public export
    {shape : List Cont} ->
    (allAppl : AllApplicative shape) => (allNaperian : AllNaperian shape) =>
    Naperian (CTensor shape) where
      Log = IndexNaperian shape
      lookup = tensorLookup
      tabulate = tensorTabulate

    public export 
    transposeMatrix : {i, j : Cont} ->
      (allNaperian : AllNaperian [i, j]) =>
      CTensor [i, j] a -> CTensor [j, i] a
    transposeMatrix {allNaperian=Cons @{f} @{Cons}}
      = fromExtensionComposition
      . transpose
      . toExtensionComposition


  namespace ShowInstance
    public export
    data AllShow : List Cont -> Type -> Type where
      Nil : Show a => AllShow [] a
      -- for type below, we should be able to define what shExt is without referencing CTensor cs a? 
      Cons : Show (c `fullOf` CTensor cs a) =>
       AllShow (c :: cs) a

    public export
    show' : {shape : List Cont} -> (allShow : AllShow shape a) =>
      CTensor shape a -> String
    show' {allShow = Nil} t = show (extract t)
    show' {allShow = Cons} t = show (extractTopExt t)

    public export
    {shape : List Cont} -> (allShow : AllShow shape a) =>
    Show (CTensor shape a) where
        show t = show' {allShow = allShow} t

  public export
  {shape : List Cont} -> Num a => AllApplicative shape =>
  Num (CTensor shape a) where
      fromInteger i = tensorReplicate {shape=shape} (fromInteger i)
      t + t' = uncurry (+) <$> liftA2Tensor {shape=shape} t t'
      t * t' = uncurry (*) <$> liftA2Tensor {shape=shape} t t'

  public export
  {shape : List Cont} -> Neg a => AllApplicative shape =>
  Neg (CTensor shape a) where
    negate = (negate <$>)
    xs - ys = (uncurry (-)) <$> liftA2 xs ys

  public export
  {shape : List Cont} -> Abs a => AllApplicative shape =>
  Abs (CTensor shape a) where
    abs = (abs <$>)

  public export
  {shape : List Cont} -> Fractional a => AllApplicative shape => Fractional (CTensor shape a) where
    t / v = (uncurry (/)) <$> liftA2 t v

  public export
  {shape : List Cont} -> Exp a => AllApplicative shape =>
  Exp (CTensor shape a) where
    exp = (exp <$>)


  namespace TensorContractions
    public export
    dotWith : {shape : List Cont} ->
      Algebra (CTensor shape) c => AllApplicative shape =>
      (a -> b -> c) ->
      CTensor shape a -> CTensor shape b -> CTensor [] c
    dotWith f xs ys = embed $ reduce $ uncurry f <$> liftA2Tensor xs ys

    public export
    dot : {shape : List Cont} -> Num a =>
      Algebra (CTensor shape) a => AllApplicative shape =>
      CTensor shape a -> CTensor shape a -> CTensor [] a
    dot xs ys = dotWith (*) xs ys
    
    public export
    outerWith : {i, j : Cont} -> (allAppl : AllApplicative [i, j]) =>
      (a -> b -> c) ->
      CTensor [i] a -> CTensor [j] b -> CTensor [i, j] c
    outerWith {allAppl = Cons} f t t' =
      let tt = (\(t, a) => strength a t) <$> strength t' t
      in uncurry f <$> fromNestedTensor tt

    public export
    outer : {i, j : Cont} -> Num a => 
      (allAppl : AllApplicative [i, j]) =>
      CTensor [i] a -> CTensor [j] a -> CTensor [i, j] a
    outer = outerWith (*)

    public export
    matrixVectorProduct : Num a => {f, g : Cont} -> AllApplicative [g] =>
      AllAlgebra [g] a =>
      CTensor [f, g] a -> CTensor [g] a -> CTensor [f] a
    matrixVectorProduct m v = fromNestedTensor $
      dot v <$> toNestedTensor m


    public export
    vectorMatrixProduct : Num a => {f, g : Cont} -> AllApplicative [f] =>
      Algebra (CTensor [f]) (CTensor [g] a) =>
      CTensor [f] a -> CTensor [f, g] a -> CTensor [g] a
    vectorMatrixProduct v m =
      let t : CTensor [f] (CTensor [g] a) := toNestedTensor m
      in extract $ dotWith (\x, gx => (x *) <$> gx) v t

    public export
    matMul : Num a => {f, g, h : Cont} -> AllApplicative [g] =>
      Algebra (CTensor [g]) (CTensor [h] a) =>
      CTensor [f, g] a -> CTensor [g, h] a -> CTensor [f, h] a
    matMul m1 m2 = fromNestedTensor $ 
      toNestedTensor m1 <&> (\row => vectorMatrixProduct row m2)

    public export
    matrixMatrixProduct : {f, g, h : Cont} -> Num a =>
      AllAlgebra [g] a =>
      AllApplicative [g] =>
      CTensor [f, g] a -> CTensor [h, g] a -> CTensor [h, f] a
    matrixMatrixProduct m1 m2 = fromNestedTensor $ 
      matrixVectorProduct m1 <$> toNestedTensor m2

t0 : CTensor [] Int
t0 = pure 13

fg : CTensor [Vect 7] Int
fg = pure 5

fgh : CTensor [Vect 7, Vect 7] Int
fgh = pure 13

sht0 : String
sht0 = show t0

fsh0 : Show (Vect 8 `fullOf` (CTensor [] Int))
fsh0 = %search

fsh : String
fsh = show fg

fshh : String
fshh = show fgh

ll : List' Int
ll = fromConcreteTy [1,2,3,4,5]

bt : BinTree' Int
bt = fromConcreteTy $ Node 1 (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)

rt : RoseTree' Char
rt = fromConcreteTy (Node 'c' [Leaf 'c', Leaf 'd'])


namespace SetterGetter
  -- hh : CTensor [List, BinTree] a -> Double
  -- hh (MkT (shapeExt <| index)) = ?qoooo_1
  -- public export
  hh : {shape : List Cont} -> CTensor shape a -> List Type
  hh {shape = []} t = []
  hh {shape = [c]} (MkT (sh <| _)) = [c.pos (shapeExt sh)]
  hh {shape = (c :: d :: cs)} (MkT (sh <| index)) = c.pos (shapeExt sh) ::
    (hh {shape=d::cs} $ let tt = index in ?ooooo)

  -- hhg : {shape : List Cont} -> CTensor shape a -> Double
  -- hhg (MkT t) = let tt = (Tensor shape).pos (shapeExt t) in ?qooo_0

  -- namespace II
  --   data Index2 : (shape : List Cont) -> (t : CTensor shape a) -> Type where
  --     Nil : {val : a} -> Index2 [] (embed val)
  --     (::) : 


  -- ||| Machinery for indexing into a TensorA
  -- ||| It depends on shape, but also on the tensor t itself
  -- ||| Provides a compile-time guarantee that we won't be out of bounds
  -- ||| This dependency is not needed for cubical tensors
  -- ||| TODO remove this dependence for cubical tensors
  -- public export
  -- data Index : (shape : List Cont) -> (t : CTensor shape dtype) -> Type where
  --   Nil : {val : dtype} -> Index [] (embed val)
  --   (::) :  {e : ((!>) sh ps) `fullOf` (CTensor cs dtype)} -> 
  --     (p : ps (shapeExt e)) ->
  --     Index cs (index e p) -> 
  --     Index (((!>) sh ps) :: cs) (embedTopExt e)

  --public export
  --index : {shape : List Cont} ->
  --  (t : CTensor shape a) -> (is : Index shape t) -> a
  --index {shape = []} (embed val) [] = val
  --index {shape = (_ :: _)} (embedTopExt e) (sh :: ind)
  --  = index (index e sh) ind

  -- data Index : (shape : List Cont) -> (t : CTensor shape a) -> Type where
  --   Nil : {val : a} -> Index [] (embed val)
  --   (::) : 

  public export
  index : {shape : List Cont} ->
    (t : CTensor shape a) -> (Tensor shape).pos (shapeExt (GetT t)) -> a
  index t = Ext.index (GetT t)

  public export
  t00 : CTensor [Maybe, List] Int
  t00 = fromConcreteTy $ Just [10, 20, 30, 40, 50, 60, 70]
  
  public export
  t11 : Tensor [2, 3] Int
  t11 = fromConcreteTy [[1,2,3], [4,5,6]]
  
  public export
  t22 : CTensor [BinTree, List] Int
  t22 = fromConcreteTy (Node [1,2] (Leaf [3,4]) (Leaf [5,6]))

  t33 : CTensor [BinTree] Int
  t33 = fromConcreteTy (Node 1 (Leaf 2) (Leaf 3))
  
  t44 : CTensor [] Int
  t44 = fromConcreteTy 13

  jj : Int
  jj = index t44 ?tuulu


namespace CubicalSetterGetter
  public export
  data IndexC : List Nat -> Type where
    Nil : IndexC []
    (::) : Fin n -> IndexC ns -> IndexC (n :: ns)
  
  public export
  indexC : {shape : List Nat} -> Tensor shape a -> IndexC shape -> a
  indexC t [] = index (GetT t) ()
  indexC t (i :: is) = indexC (index (GetT $ toNestedTensor t) (i ** ())) is 

  public export
  setC : {shape : List Nat} ->
    Tensor shape a -> IndexC shape -> a -> Tensor shape a
  setC t [] x = MkT $ set (GetT t) () x
  setC {shape=(s::ss)} t (i :: is) x =
    let tNested : Tensor [s] (Tensor ss a) := toNestedTensor t
        ts : Tensor ss a := setC (indexC tNested [i]) is x
    in fromNestedTensor $ MkT $ set (GetT tNested) (i ** ()) ts

i : Int
i = indexC t11 [1, 1]

s : Tensor [2, 3] Int
s = setC t11 [1, 1] 100