module Data.Tensor.NaperianTensor

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
  -- I tried performign the elaboration myself as much as possible, but it's not clear why it is slow
  public export
  data AllNaperian : (shape : ApplContList conts) -> Type where
    Nil : AllNaperian []
    (::) : {0 c : Cont} -> {cs : ApplContList csConts} -> Applicative (Ext c) =>
       (napC : Naperian (Ext c)) => AllNaperian {conts=csConts} cs -> AllNaperian {conts=((# c):: csConts)} (c :: cs)
  

namespace IndexTNaperian
  ||| Datatype for indexing into TensorA 
  ||| It made out of containers whose extensions are Naperian
  ||| Meaning we don't need the tensor *term* to be able to index into it, just the type
  ||| TODO need to use this in the rest of the code
  public export
  data IndexTNaperian :
    (shape : ApplContList conts) ->
    AllNaperian shape ->
    Type where
    Nil : IndexTNaperian [] []
    (::) : Applicative (Ext c) =>
      (napC : Naperian (Ext c)) =>
      Log {f=Ext c} ->
      {cs : ApplContList conts} ->
      {allNapsCs : AllNaperian cs} ->
      IndexTNaperian cs allNapsCs ->
      IndexTNaperian (c :: cs) ((::) {napC=napC} allNapsCs)

public export
tensorTabulate : {shape : ApplContList conts} -> (allNaperian : AllNaperian shape) -> (IndexTNaperian shape allNaperian -> a) -> TensorA shape a
tensorTabulate {shape = []} [] f = TZ $ f []
tensorTabulate {shape = (_ :: _)} ((::) applS) f
  = TS $ tabulate $ \i => tensorTabulate applS $ \is => f (i :: is)

public export
{conts : List ApplC} -> {shape : ApplContList conts} -> (allNaperian : AllNaperian shape) =>
Naperian (TensorA shape) where
  Log = IndexTNaperian shape allNaperian
  lookup {allNaperian = []} (TZ val) [] = val
  lookup {allNaperian = ((::) _)} (TS xs) (i :: is) = lookup (lookup xs i) is
  tabulate {allNaperian} = tensorTabulate allNaperian

public export
transposeMatrixA : {i, j : Cont} ->
  Applicative (Ext i) =>
  Applicative (Ext j) =>
  (allNaperian : AllNaperian [i, j]) =>
  TensorA [i, j] a -> TensorA [j, i] a
transposeMatrixA {allNaperian = ((::) {napC=napI} ((::) {napC=napJ} []))}
  = fromExtComposition . Naperian.transpose . toExtComposition


public export
transposeMatrix : {i, j : Nat} ->
  Tensor [i, j] a -> Tensor [j, i] a
transposeMatrix t
  = let tt = transposeMatrixA 
    in ToCubicalTensor $ ?hooo $ FromCubicalTensor t -- ToCubicalTensor . transposeMatrixA . FromCubicalTensor
