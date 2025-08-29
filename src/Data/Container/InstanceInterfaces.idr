module Data.Container.InstanceInterfaces

import Data.Vect
import Decidable.Equality


import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Concrete.Definition
import Data.Container.Concrete.Instances
import Data.Container.Extension.Definition
import Data.Container.Extension.Instances
import Data.Container.Applicative.Definition
import Data.Container.Applicative.Instances

import Data.Tree
import Data.Algebra
import Misc

%hide Prelude.toList
%hide Data.Vect.Fin.tabulate
%hide Data.Vect.Subset.tabulate

namespace VectInstances
  public export
  {n : Nat} -> Eq x => Eq (Vect' n x) where
    v == v' = (toVect v) == (toVect v')
 
  public export
  {n : Nat} -> Show x => Show (Vect' n x) where
    show v = show (toVect v)

  public export
  {n : Nat} -> Foldable (Vect' n) where
    foldr f z v = foldr f z (toVect v)
  
  public export
  {n : Nat} -> Num a => Algebra (Vect' n) a where
    reduce v = reduce (toVect v)


  -- %hint
  -- public export
  -- vectInterfacePos : {n : Nat} -> InterfaceOnPositions (Vect n) DecEq
  -- vectInterfacePos = MkI 

  aiqi : InterfaceOnPositions (Vect 3) Eq
  aiqi = MkI

{---
Ideally, all instances would be defined in terms of ConcreteTypes,
but there are totality checking issues with types whose size isn't known
at compile time
---}
namespace ListInstances
  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Show a => Show (List' a) where
    show x = show (toList x)

  -- some attempts at fixing partiality below
  -- public export
  -- showListHelper : Show a => List' a -> String
  -- showListHelper (0 <| _) = ""
  -- showListHelper (1 <| index) = show $ index FZ
  -- showListHelper ((S k) <| index)
  --   = let (s, rest) = removeBeginning index
  --     in show s ++ ", " ++ showListHelper (k <| rest)

  -- public export
  -- showListHelper : Show a => List' a -> String
  -- showListHelper x = show (toList x)


namespace BinTreeInstances
  partial
  public export
  Eq a => Eq (BinTree' a) where
    t == t' = (toBinTreeSame t) == (toBinTreeSame t')

  partial
  public export
  Show a => Show (BinTree' a) where
    show = show . toBinTreeSame

  public export
  binTreePosInterface : InterfaceOnPositions BinTree DecEq
  binTreePosInterface = MkI


namespace BinTreeLeafInstances
  partial
  public export
  Eq a => Eq (BinTreeLeaf' a) where
    t == t' = (toBinTreeLeaf t) == (toBinTreeLeaf t')

  partial
  public export
  Show a => Show (BinTreeLeaf' a) where
    show = show . toBinTreeLeaf

  ||| Summing up elements of the tree given by the Num a structure
  public export
  Num a => Algebra BinTreeLeaf' a where
    reduce = reduce {f=BinTreeLeaf} . toBinTreeLeaf


namespace BinTreeNodeInstances
  partial
  public export
  Eq a => Eq (BinTreeNode' a) where
    t == t' = (toBinTreeNode t) == (toBinTreeNode t')

  partial
  public export
  Show a => Show (BinTreeNode' a) where
    show = show . toBinTreeNode

  partial
  public export
  Num a => Algebra BinTreeNode' a where
    reduce = reduce {f=BinTreeNode} . toBinTreeNode


namespace TensorInstances
  namespace EqInstance
    public export
    data AllEq : List Cont -> Type -> Type where
      Nil : Eq a => AllEq [] a
      Cons : (shExt : Eq (c `fullOf` Tensor' cs a)) =>
        AllEq (c :: cs) a

    public export
    tensorEq : {shape : List Cont} -> (allEq : AllEq shape a) =>
      Tensor' shape a -> Tensor' shape a -> Bool
    tensorEq {allEq = []} t1 t2 = extract t1 == extract t2
    tensorEq {allEq = Cons} t1 t2 = (extractExt t1) == (extractExt t2)

    public export
    (allEq : AllEq [] a) =>
      Eq (Tensor' [] a) where
        (==) = tensorEq {allEq = allEq}

    public export
    {c : Cont} -> (allEq : AllEq [c] a) =>
      Eq (Tensor' [c] a) where
        (==) = tensorEq {allEq = allEq}

    public export
    {c, d : Cont} -> (allEq : AllEq [c, d] a) =>
      Eq (Tensor' [c, d] a) where
        (==) = tensorEq {allEq = allEq}

    public export
    {c, d, e : Cont} -> (allEq : AllEq [c, d, e] a) =>
      Eq (Tensor' [c, d, e] a) where
        (==) = tensorEq {allEq = allEq}

    public export
    {c, d, e, f : Cont} -> (allEq : AllEq [c, d, e, f] a) =>
      Eq (Tensor' [c, d, e, f] a) where
        (==) = tensorEq {allEq = allEq}
    
    public export
    {c, d, e, f, g : Cont} -> (allEq : AllEq [c, d, e, f, g] a) =>
      Eq (Tensor' [c, d, e, f, g] a) where
        (==) = tensorEq {allEq = allEq}

    -- ttv : InterfaceOnPositions (Vect 4) Eq
    -- ttv = %search

    tt1 : InterfaceOnPositions (Tensor []) Eq
    tt1 = MkI

    %hint
    tt2 : {c : Cont} -> InterfaceOnPositions (Tensor [c]) Eq
    tt2 = let tt = (Tensor [c]).pos in MkI @{?what}


    -- tt3 : {c : Cont} -> InterfaceOnPositions (Tensor [c]) Eq
    -- tt3 = MkI @{%search}

    hh : {n : Nat} -> Eq (Fin n)
    hh = %search

    {n : Nat} -> Eq ((cp : Fin n ** ())) where
      x == y = fst x == fst y

    public export
    toNestedFins : (shape : List Nat) -> Type
    toNestedFins [] = ()
    toNestedFins (n :: ns) = (x : Fin n ** toNestedFins ns)

    public export
    nestedFinsEq : {shape : List Nat} ->
      toNestedFins shape -> toNestedFins shape -> Bool
    nestedFinsEq {shape = []} _ _ = True
    nestedFinsEq {shape = (n :: ns)} (x ** xs) (y ** ys)
      = x == y && nestedFinsEq xs ys

    public export
    {shape : List Nat} -> Eq (toNestedFins shape) where
      (==) = nestedFinsEq

    %hint
    public export
    tensorPosDecEq : {shape : List Nat} ->
      (s : (TensorC shape).shp) ->
      (t1 : (TensorC shape).pos s) ->
      (t2 : (TensorC shape).pos s) ->
      Dec (t1 = t2)
    tensorPosDecEq {shape = []} s () () = Yes Refl
    tensorPosDecEq {shape = (n :: ns)} s (x ** xs) (y ** ys)
      = case decEq x y of
        Yes Refl => case tensorPosDecEq {shape=ns} (index s x) xs ys of
          Yes Refl => Yes Refl
          No cf => No $ \c => cf ?hm -- (cong snd c)
        No cf => No $ \c => cf (cong fst c)

    -- {shape : List Nat} -> (s : (TensorC shape).shp)

    %hint
    tthiS : {shape : List Nat} -> InterfaceOnPositions (TensorC shape) DecEq
    tthiS = MkI @{\s => let t = tensorPosDecEq {shape=shape} s in ?hmmm} -- constructor for DecEq?

    -- why doesn't hint work here?
    -- tthiS2 : {shape : List Nat} -> InterfaceOnPositions (TensorC shape) DecEq
    -- tthiS2 = %search


    tensorPosDecEqInt : {shape : List Nat} ->
      (s : (TensorC shape).shp) ->
      DecEq ((TensorC shape).pos s)
    tensorPosDecEqInt s = ?tensorPosDecEqInt_rhs -- what is the constructor for DecEq?
    -- are there default interface constructors?

    -- decEqDepPair : {x : Type} -> {y : x -> Type} ->
    --   {a : x} ->
    --   (xs, ys : y a) ->
    --   Dec (xs = ys) ->
    --   Dec ((a ** xs) = (a ** ys))


    -- tensorPosEq {shape = []} sh = %search
    -- tensorPosEq {shape = (n :: ns)} sh =
    --   MkEq (\t1, t2 => ?fn_rhs_1) ?fn_rhs_2


    -- Turns out only this is sufficient for the setC function to work
    %hint
    public export
    interfacePosEq : {n : Nat} -> InterfaceOnPositions (TensorC [n]) Eq
    interfacePosEq = MkI

    -- public export
    -- tthiD : {n, m : Nat} -> InterfaceOnPositions (TensorC [n, m]) Eq
    -- tthiD = let tg = (TensorC [n, m]).pos in MkI @{?ssearch}

    tensorPosEq : {shape : List Nat} ->
      (s : (TensorC shape).shp) ->
      (TensorC shape).pos s ->
      (TensorC shape).pos s ->
      Bool
    tensorPosEq {shape = []} s _ _ = True
    tensorPosEq {shape = (n :: ns)} s (x ** xs) (y ** ys) = x == y &&
      let g = tensorPosEq {shape=ns} (index s x) xs
          -- ss : Ext (Vect n) (TensorC ns)
          -- ss = index s x
      in ?whatt



  public export 
  tensorCInterfacePos : {shape : List Nat} ->
    InterfaceOnPositions (TensorC shape) Eq


  -- public export
  -- vectInterfacePos : {n : Nat} -> InterfaceOnPositions (Vect n) DecEq
  -- vectInterfacePos = MkI 

  namespace AlgebraInstance
    -- Unlike all other instantiations of 'AllX', this one isn't individually stating they're algebras, but rather cumulatively. 
    -- i.e. AllAlgebra [c, d] a is not defined as Algebra c a and Algebra d a, bur rather as Algebra c (Algebra d a)
    public export
    data AllAlgebra : (shape : List Cont) -> (dtype : Type) -> Type where
      Nil : AllAlgebra [] a
      Cons : (alg : Algebra (Ext c) (Tensor' cs a)) =>
        (allAlg : AllAlgebra cs a) =>
        AllAlgebra (c :: cs) a

    public export
    reduceTensor : {shape : List Cont} ->
      (allAlg : AllAlgebra shape a) =>
      Tensor' shape a -> a
    reduceTensor {allAlg = []} = extract
    reduceTensor {allAlg = Cons} = reduceTensor . reduce . extractExt

    public export
    (allAlg : AllAlgebra [] a) =>
      Algebra (Tensor' []) a where
      reduce = reduceTensor {allAlg = allAlg}

    public export
    {c : Cont} -> (allAlg : AllAlgebra [c] a) =>
      Algebra (Tensor' [c]) a where
      reduce = reduceTensor {allAlg = allAlg}

    public export
    {c, d : Cont} -> (allAlg : AllAlgebra [c, d] a) =>
      Algebra (Tensor' [c, d]) a where
      reduce = reduceTensor {allAlg = allAlg}

    public export
    {c, d, e : Cont} -> (allAlg : AllAlgebra [c, d, e] a) =>
      Algebra (Tensor' [c, d, e]) a where
      reduce = reduceTensor {allAlg = allAlg}

    public export
    {c, d, e, f : Cont} -> (allAlg : AllAlgebra [c, d, e, f] a) =>
      Algebra (Tensor' [c, d, e, f]) a where
      reduce = reduceTensor {allAlg = allAlg}

    public export
    {c, d, e, f, g : Cont} -> (allAlg : AllAlgebra [c, d, e, f, g] a) =>
      Algebra (Tensor' [c, d, e, f, g]) a where
      reduce = reduceTensor {allAlg = allAlg}

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
      data IndexNaperian : (shape : List Cont) -> (allNap : AllNaperian shape) => Type where
        Nil : IndexNaperian []
        (::) : (nap : Naperian (Ext c)) =>
          (rest : AllNaperian cs) =>
          Log {f=(Ext c)} ->
          IndexNaperian cs {allNap=rest} ->
          IndexNaperian (c :: cs) {allNap=Cons {rest=rest}}

    public export
    tensorLookup : {shape : List Cont} ->
      (allNaperian : AllNaperian shape) =>
      Tensor' shape a ->
      (IndexNaperian shape -> a)
    tensorLookup {shape = []} t _ = extract t
    tensorLookup {shape = (c :: cs)} {allNaperian = Cons} t (i :: is)
      = tensorLookup (lookup (extractExt t) i) is

    public export
    tensorTabulate : {shape : List Cont} -> (allNaperian : AllNaperian shape) =>
      (IndexNaperian shape -> a) -> Tensor' shape a
    tensorTabulate {shape = []} {allNaperian = []} f = toScalar (f Nil)
    tensorTabulate {shape = (_ :: _)} {allNaperian = Cons} f
      = embedExt $ tabulate $ \i => tensorTabulate $ \is => f (i :: is)

    public export
    Naperian (Tensor' []) where
      Log = IndexNaperian []
      lookup = tensorLookup
      tabulate = tensorTabulate

    {c : Cont} ->
    (allAppl : AllApplicative [c]) => (allNaperian : AllNaperian [c]) =>
    Naperian (Tensor' [c]) where
      Log = IndexNaperian [c]
      lookup = tensorLookup
      tabulate = tensorTabulate

    {c, d : Cont} ->
    (allAppl : AllApplicative [c, d]) => (allNaperian : AllNaperian [c, d]) =>
    Naperian (Tensor' [c, d]) where
      Log = IndexNaperian [c, d]
      lookup = tensorLookup
      tabulate = tensorTabulate

    {c, d, e : Cont} ->
    (allAppl : AllApplicative [c, d, e]) => (allNaperian : AllNaperian [c, d, e]) =>
    Naperian (Tensor' [c, d, e]) where
      Log = IndexNaperian [c, d, e]
      lookup = tensorLookup
      tabulate = tensorTabulate

    {c, d, e, f : Cont} ->
    (allAppl : AllApplicative [c, d, e, f]) => (allNaperian : AllNaperian [c, d, e, f]) =>
    Naperian (Tensor' [c, d, e, f]) where
      Log = IndexNaperian [c, d, e, f]
      lookup = tensorLookup
      tabulate = tensorTabulate

    {c, d, e, f, g : Cont} ->
    (allAppl : AllApplicative [c, d, e, f, g]) => (allNaperian : AllNaperian [c, d, e, f, g]) =>
    Naperian (Tensor' [c, d, e, f, g]) where
      Log = IndexNaperian [c, d, e, f, g]
      lookup = tensorLookup
      tabulate = tensorTabulate


    public export 
    transposeMatrix : {i, j : Cont} ->
      (allNaperian : AllNaperian [i, j]) =>
      Tensor' [i, j] a -> Tensor' [j, i] a
    transposeMatrix {allNaperian=Cons @{f} @{Cons}} t =
      fromExtensionComposition {shape=[j, i]} (transpose $ toExtensionComposition {shape=[i,j]} t)


  namespace ShowInstance
    public export
    data AllShow : List Cont -> Type -> Type where
      Nil : Show a => AllShow [] a
      -- for type below, we should be able to define what shExt is without referencing Tensor' cs a? 
      Cons : (shExt : Show (c `fullOf` Tensor' cs a)) =>
       AllShow (c :: cs) a

    public export
    show' : {shape : List Cont} -> (allShow : AllShow shape a) =>
      Tensor' shape a -> String
    show' {allShow = Nil} t = show (extract t)
    show' {allShow = Cons} t = show (extractExt t)

    public export
    (allShow : AllShow [] a) =>
      Show (Tensor' [] a) where
      show {allShow = Nil} t = show (extract t)

    public export
    {c : Cont} -> (allShow : AllShow [c] a) =>
      Show (Tensor' [c] a) where
        show t = show' {allShow = allShow} t

    public export
    {c, d : Cont} -> (allShow : AllShow [c, d] a) =>
      Show (Tensor' [c, d] a) where
        show t = show' {allShow = allShow} t

    public export
    {c, d, e : Cont} -> (allShow : AllShow [c, d, e] a) =>
      Show (Tensor' [c, d, e] a) where
        show t = show' {allShow = allShow} t

    public export
    {c, d, e, f : Cont} -> (allShow : AllShow [c, d, e, f] a) =>
      Show (Tensor' [c, d, e, f] a) where
        show t = show' {allShow = allShow} t

    public export
    {c, d, e, f, g : Cont} -> (allShow : AllShow [c, d, e, f, g] a) =>
      Show (Tensor' [c, d, e, f, g] a) where
        show t = show' {allShow = allShow} t

  namespace NumInstance 
    public export
    Num a => AllApplicative [] =>
      Num (Tensor' [] a) where
        fromInteger i = tensorReplicate {shape=[]} (fromInteger i)
        t + t' = uncurry (+) <$> liftA2Tensor {shape=[]} t t'
        t * t' = uncurry (*) <$> liftA2Tensor {shape=[]} t t'



    public export
    {c : Cont} -> Num a => AllApplicative [c] =>
      Num (Tensor' [c] a) where
        fromInteger i = tensorReplicate {shape=[c]} (fromInteger i)
        t + t' = uncurry (+) <$> liftA2Tensor {shape=[c]} t t'
        t * t' = uncurry (*) <$> liftA2Tensor {shape=[c]} t t'

    public export
    {c, d : Cont} -> Num a => AllApplicative [c, d] =>
      Num (Tensor' [c, d] a) where
        fromInteger i = tensorReplicate {shape=[c, d]} (fromInteger i)
        t + t' = uncurry (+) <$> liftA2Tensor {shape=[c, d]} t t'
        t * t' = uncurry (*) <$> liftA2Tensor {shape=[c, d]} t t'

    public export
    {c, d, e : Cont} -> Num a => AllApplicative [c, d, e] =>
      Num (Tensor' [c, d, e] a) where
        fromInteger i = tensorReplicate {shape=[c, d, e]} (fromInteger i)
        t + t' = uncurry (+) <$> liftA2Tensor {shape=[c, d, e]} t t'
        t * t' = uncurry (*) <$> liftA2Tensor {shape=[c, d, e]} t t'

    public export
    {c, d, e, f : Cont} -> Num a => AllApplicative [c, d, e, f] =>
      Num (Tensor' [c, d, e, f] a) where
        fromInteger i = tensorReplicate {shape=[c, d, e, f]} (fromInteger i)
        t + t' = uncurry (+) <$> liftA2Tensor {shape=[c, d, e, f]} t t'
        t * t' = uncurry (*) <$> liftA2Tensor {shape=[c, d, e, f]} t t'

    public export
    {c, d, e, f, g : Cont} -> Num a => AllApplicative [c, d, e, f, g] =>
      Num (Tensor' [c, d, e, f, g] a) where
        fromInteger i = tensorReplicate {shape=[c, d, e, f, g]} (fromInteger i)
        t + t' = uncurry (+) <$> liftA2Tensor {shape=[c, d, e, f, g]} t t'
        t * t' = uncurry (*) <$> liftA2Tensor {shape=[c, d, e, f, g]} t t'

  namespace NegInstance
    public export
    Neg a => AllApplicative [] => Neg (Tensor' [] a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    public export
    {c : Cont} -> Neg a => AllApplicative [c] => Neg (Tensor' [c] a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    public export
    {c, d : Cont} -> Neg a => AllApplicative [c, d] => Neg (Tensor' [c, d] a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    public export
    {c, d, e : Cont} -> Neg a => AllApplicative [c, d, e] => Neg (Tensor' [c, d, e] a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    public export
    {c, d, e, f : Cont} -> Neg a => AllApplicative [c, d, e, f] => Neg (Tensor' [c, d, e, f] a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    public export
    {c, d, e, f, g : Cont} -> Neg a => AllApplicative [c, d, e, f, g] => Neg (Tensor' [c, d, e, f, g] a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

  namespace AbsInstance
    public export
    Abs a => AllApplicative [] => Abs (Tensor' [] a) where
      abs = (abs <$>)

    public export
    {c : Cont} -> Abs a => AllApplicative [c] => Abs (Tensor' [c] a) where
      abs = (abs <$>)

    public export
    {c, d : Cont} -> Abs a => AllApplicative [c, d] => Abs (Tensor' [c, d] a) where
      abs = (abs <$>)

    public export
    {c, d, e : Cont} -> Abs a => AllApplicative [c, d, e] => Abs (Tensor' [c, d, e] a) where
      abs = (abs <$>)
      
    public export
    {c, d, e, f : Cont} -> Abs a => AllApplicative [c, d, e, f] => Abs (Tensor' [c, d, e, f] a) where
      abs = (abs <$>)

    public export
    {c, d, e, f, g : Cont} -> Abs a => AllApplicative [c, d, e, f, g] => Abs (Tensor' [c, d, e, f, g] a) where
      abs = (abs <$>)
  
  namespace FractionalInstance
    public export
    Fractional a => AllApplicative [] => Fractional (Tensor' [] a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {c : Cont} -> Fractional a => AllApplicative [c] => Fractional (Tensor' [c] a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {c, d : Cont} -> Fractional a => AllApplicative [c, d] => Fractional (Tensor' [c, d] a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {c, d, e : Cont} -> Fractional a => AllApplicative [c, d, e] => Fractional (Tensor' [c, d, e] a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {c, d, e, f : Cont} -> Fractional a => AllApplicative [c, d, e, f] => Fractional (Tensor' [c, d, e, f] a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {c, d, e, f, g : Cont} -> Fractional a => AllApplicative [c, d, e, f, g] => Fractional (Tensor' [c, d, e, f, g] a) where
      t / v = (uncurry (/)) <$> liftA2 t v
  
  namespace ExpInstance
    public export
    Exp a => AllApplicative [] => Exp (Tensor' [] a) where
      exp = (exp <$>)

    public export
    {c : Cont} -> Exp a => AllApplicative [c] => Exp (Tensor' [c] a) where
      exp = (exp <$>)

    public export
    {c, d : Cont} -> Exp a => AllApplicative [c, d] => Exp (Tensor' [c, d] a) where
      exp = (exp <$>)

    public export
    {c, d, e : Cont} -> Exp a => AllApplicative [c, d, e] => Exp (Tensor' [c, d, e] a) where
      exp = (exp <$>)

    public export
    {c, d, e, f : Cont} -> Exp a => AllApplicative [c, d, e, f] => Exp (Tensor' [c, d, e, f] a) where
      exp = (exp <$>)

    public export
    {c, d, e, f, g : Cont} -> Exp a => AllApplicative [c, d, e, f, g] => Exp (Tensor' [c, d, e, f, g] a) where
      exp = (exp <$>)
    


  {---
  All of these are implemented for tensors up to depth 5:

  Eq ✓
  Num ✓
    * Neg ✓
    * Abs ✓
    * Fractional ✓
    * Exp ✓
  Functor ✓ (follows from Ext)
  Concrete ✓ 
  Applicative ✓
  Show ✓
  Algebra ✓
  Naperian ✓
  

  Also implemented:
  Tensor contractions ✓
  Foldable? Not sure if it was working before
  ---}
  
  namespace TensorContractions
    public export
    dotWith : {shape : List Cont} -> Algebra (Tensor' shape) c =>
      AllApplicative shape =>
      (a -> b -> c) ->
      Tensor' shape a -> Tensor' shape b -> Tensor' [] c
    dotWith f xs ys = toScalar $ reduce $ uncurry f <$> liftA2Tensor xs ys

    public export
    dot : {shape : List Cont} -> Num a => Algebra (Tensor' shape) a =>
      AllApplicative shape =>
      Tensor' shape a -> Tensor' shape a -> Tensor' [] a
    dot xs ys = dotWith (*) xs ys
    
    public export
    outerWith : {i, j : Cont} -> (allAppl : AllApplicative [i, j]) =>
      (a -> b -> c) ->
      Tensor' [i] a -> Tensor' [j] b -> Tensor' [i, j] c
    outerWith {allAppl = Cons @{fst} @{rst}} f t t' =
      let tt : Tensor' [i] (Tensor' [j] (a, b)) := (\(t, a) => strength a t) <$> strength t' t
      in uncurry f <$> fromNestedTensor {cs=[j]} tt

    public export
    outer : {i, j : Cont} -> (allAppl : AllApplicative [i, j]) =>
      Num a =>
      Tensor' [i] a -> Tensor' [j] a -> Tensor' [i, j] a
    outer = outerWith (*)


    public export
    matrixVectorProduct : Num a => {f, g : Cont} -> AllApplicative [g] =>
      AllAlgebra [g] a =>
      Tensor' [f, g] a -> Tensor' [g] a -> Tensor' [f] a
    matrixVectorProduct m v = fromNestedTensor {cs=[]} $
      dot {shape=[g]} v <$> toNestedTensor {c=f} {cs=[g]} m


    public export
    vectorMatrixProduct : Num a => {f, g : Cont} -> AllApplicative [f] =>
      (allAlg : Algebra (Tensor' [f]) (Tensor' [g] a)) =>
      Tensor' [f] a -> Tensor' [f, g] a -> Tensor' [g] a
    vectorMatrixProduct v m =
      let t : Tensor' [f] (Tensor' [g] a) := toNestedTensor {c=f} {cs=[g]} m
      in extract $ dotWith {shape=[f]} (\x, gx => (x *) <$> gx) v t

    public export
    matMul : Num a => {f, g, h : Cont} -> AllApplicative [g] =>
      (allAlg : Algebra (Tensor' [g]) (Tensor' [h] a)) =>
      Tensor' [f, g] a -> Tensor' [g, h] a -> Tensor' [f, h] a
    matMul m1 m2 =
      let t : Tensor' [f] (Tensor' [g] a) := toNestedTensor {cs=[g]} m1
      in fromNestedTensor {cs=[h]} (t <&> (\row => vectorMatrixProduct row m2))

    public export
    matrixMatrixProduct : {f, g, h : Cont} -> Num a =>
      (allAlgebra : AllAlgebra [g] a) =>
      AllApplicative [g] =>
      Tensor' [f, g] a -> Tensor' [h, g] a -> Tensor' [h, f] a
    matrixMatrixProduct m1 m2 =
      let t : Tensor' [h] (Tensor' [g] a) := toNestedTensor {cs=[g]} m2
      in fromNestedTensor {cs=[f]} (matrixVectorProduct m1 <$> t)


t0 : Tensor' [] Int
t0 = pure 13

fg : Tensor' [Vect 7] Int
fg = pure 5

fgh : Tensor' [Vect 7, Vect 7] Int
fgh = pure 13

sht0 : String
sht0 = show t0

fsh0 : Show (Vect 8 `fullOf` (Tensor' [] Int))
fsh0 = %search

fsh : String
fsh = show fg

fshh : String
fshh = show fgh


{-
public export
data AllAlgebra : (shape : List Cont) -> (dtype : Type) -> Type where
  Nil : AllAlgebra [] a
  Cons : {c : Cont} -> {cs : List Cont} ->
    (alg : Algebra (Ext c) (Tensor' cs a)) =>
    (allAlg : AllAlgebra cs a) =>
    AllAlgebra (c :: cs) a


public export
reduceTensor : {shape : List Cont} ->
  (allAlgebra : AllAlgebra shape a) =>
  Tensor' shape a -> a
-- reduceTensor {shape = []} {allAlgebra = []} t = extract t
-- reduceTensor {shape = (c :: cs)} {allAlgebra = Cons {alg} {allAlg}} t
--   = ((reduceTensor {allAlgebra=allAlg}) . (reduce @{alg}))
--       (toContainerComp <$> (fromContainerComp {shape=(c :: cs)} t))

public export
{shape : List Cont} ->
(allAlgebra : AllAlgebra shape a) =>
Algebra (Tensor' shape) a where
  reduce = reduceTensor


agtest0 : Algebra BinTreeNode Int
agtest0 = %search

attt : AllAlgebra [] Int
attt = %search

-- attt1 : Algebra (Ext BinTreeNode) (Tensor' [] Int)
-- attt1 = %search
-- 
-- agt0 : AllAlgebra [BinTreeNode] Int
-- agt0 = %search
-- 
-- agt : AllAlgebra [BinTreeNode, Vect 7] Int
-- agt = %search
-- 
-- agtest : Algebra (Tensor' [BinTreeNode, Vect 7]) Int
-- agtest = %search
-}
