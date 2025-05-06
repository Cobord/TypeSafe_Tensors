module Tensor.ContainerTensor.NaperianTensor

import Data.Fin
import Data.Vect


import Data.Container.Definition
import Data.Container.Instances
import Tensor.ContainerTensor.Tensor
import Data.Functor.Naperian



public export
data AllNaperian : (shape : ApplV conts) -> Type where
  Nil : AllNaperian []
  (::) : {cs : ApplV conts} -> Applicative (Ext c) =>
    (napC : Naperian (Ext c)) => AllNaperian cs -> AllNaperian (c :: cs)

namespace IndexTNaperian
  ||| Datatype for indexing into Tensors made out of containers whose extensions are Naperian
  ||| Meaning we don't need the tensor *term* to be able to index into it, just the type
  public export
  data IndexTNaperian : (shape : ApplV conts) -> AllNaperian shape -> Type where
    Nil : IndexTNaperian [] []
    (::) : (Applicative (Ext c)) =>
      (napC : Naperian (Ext c)) =>
      Log {f=Ext c} ->
      {cs : ApplV conts} ->
      {allNapsCs : AllNaperian cs} ->
      IndexTNaperian cs allNapsCs ->
      IndexTNaperian (c :: cs) ((::) {napC=napC} allNapsCs)

public export
tensorTabulate : {shape : ApplV conts} -> (allNaperian : AllNaperian shape) -> (IndexTNaperian shape allNaperian -> a) -> Tensor shape a
tensorTabulate {shape = []} [] f = TZ $ f []
tensorTabulate {shape = (_ :: _)} ((::) applS) f
  = TS $ tabulate $ \i => tensorTabulate applS $ \is => f (i :: is)

public export
{conts : Vect n ApplC} -> {shape : ApplV conts} -> (allNaperian : AllNaperian shape) =>
Naperian (Tensor shape) where
  Log = IndexTNaperian shape allNaperian
  lookup {allNaperian = []} (TZ val) [] = val
  lookup {allNaperian = ((::) _)} (TS xs) (i :: is) = lookup (lookup xs i) is
  tabulate {allNaperian} = tensorTabulate allNaperian

public export
transposeMatrix : {i, j : Cont} ->
  Applicative (Ext i) =>
  Applicative (Ext j) =>
  (allNaperian : AllNaperian [i, j]) =>
  Tensor [i, j] a -> Tensor [j, i] a
transposeMatrix {allNaperian = ((::) {napC=napI} ((::) {napC=napJ} []))} m
  = fromArray $ Naperian.transpose {f=(Ext i)} {g=(Ext j)} (toArray m)
    -- This can be written a bit more succintly, but compiler gets slow with all the ambiguity?
