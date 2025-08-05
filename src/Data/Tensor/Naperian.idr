module Data.Tensor.Naperian

import Data.Fin
import Data.Vect

import Data.Container.Definition
import Data.Container.Instances
import Data.Tensor
import Data.Functor.Naperian

%hide Builtin.infixr.(#)

namespace NaperianConstraint
  -- This particular interface, for some reason, makes the compile time incredibly long
  -- The second constructor is the culiprit, removing it solves the problem
  -- I tried performing the elaboration myself as much as possible in the type, but it's not clear why it is slow
  public export
  data AllNaperian : (shape : List ContA) -> Type where
    Nil : AllNaperian []
    (::) : {0 c : ContA} -> {cs : List ContA} ->
       (napC : Naperian (Ext (GetC c))) => AllNaperian cs ->
       AllNaperian (c :: cs)
  

namespace IndexTNaperian
  ||| Datatype for indexing into TensorA 
  ||| It made out of containers whose extensions are Naperian
  ||| Meaning we don't need the tensor *term* to be able to index into it, just the type
  ||| TODO need to use this in the rest of the code
  public export
  data IndexTNaperian :
    (shape : List ContA) ->
    AllNaperian shape ->
    Type where
    Nil : IndexTNaperian [] []
    (::) : {c : ContA} -> {cs : List ContA} ->
      (napC : Naperian (Ext (GetC c))) =>
      Log {f=(Ext (GetC c))} ->
      {allNapsCs : AllNaperian cs} ->
      IndexTNaperian cs allNapsCs ->
      IndexTNaperian (c :: cs) ((::) {napC=napC} allNapsCs)

public export
tensorTabulate : {shape : List ContA} -> (allNaperian : AllNaperian shape) -> (IndexTNaperian shape allNaperian -> a) -> TensorA shape a
tensorTabulate {shape = []} [] f = TZ $ f []
tensorTabulate {shape = (_ :: _)} ((::) applS) f
  = TS $ tabulate $ \i => tensorTabulate applS $ \is => f (i :: is)

public export
{shape : List ContA} -> (allNaperian : AllNaperian shape) =>
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


public export
transposeMatrix : {i, j : Nat} ->
  Tensor [i, j] a -> Tensor [j, i] a
transposeMatrix = ToCubicalTensor . transposeMatrixA . FromCubicalTensor

  -- public export
  -- data IndexTData : Type where
  --   NonCubical : (shape : ContAontList conts) -> IndexTData
  --   Cubical : (shape : Vect n Nat) -> IndexTData -- assuming every Naperian functor has shape=Fin d for some d, this describes Naperian TensorAs

  -- vnn : IndexTData -> Type -> Type
  -- vnn (NonCubical shape) = TensorA shape
  -- vnn (Cubical shape) = \_ => Unit
