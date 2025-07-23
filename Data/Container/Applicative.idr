module Data.Container.Applicative

import Data.Fin

import Data.Container.Definition
import Data.Container.Instances

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

||| Every natural number n corresponds to an VectCont n, which is applicative
||| Used in cubical tensors whose shapes are defined by lists of natural numbers
public export
NatToVectCont : (n : Nat) -> ApplC
NatToVectCont n = # (VectCont n)

||| Data type for ergonomic construction of lists of applicative containers
||| Allows us to use the usual list syntax with *only the container explicit*, with the proof of its extension being applicative is done automatically
public export
data ApplContList : List ApplC -> Type where
  Nil : ApplContList []
  (::) : (c : Cont) ->
    Applicative (Ext c) =>
    ApplContList cs -> ApplContList ((# c) :: cs)

||| Used to convert a cubical tensor's shape to an applicative container list
public export
natsToApplConts : (shape : List Nat) -> ApplContList (NatToVectCont <$> shape)
natsToApplConts [] = []
natsToApplConts (s :: ss) = VectCont s :: natsToApplConts ss

public export
applContListToContList : ApplContList conts -> List Cont
applContListToContList [] = []
applContListToContList (c :: cs) = c :: applContListToContList cs

||| Specialised to Hancock tensor product
public export
prodApplConts : {conts : List ApplC} ->
  ApplContList conts -> Cont
prodApplConts cs = prodConts (applContListToContList cs)



public export
prodApplConts' : {conts : List ApplC} ->
  ApplContList conts -> ApplC
prodApplConts' [] = # CUnit
prodApplConts' (c :: cs) =
  (#) (c >< prodConts (applContListToContList cs))
    {applPrf = ?prodApplConts_rhs_1}
