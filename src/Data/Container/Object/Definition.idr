module Data.Container.Object.Definition

-- Inspired by Andre's code: https://gitlab.com/avidela/types-laboratory/-/tree/main/src/Data/Container?ref_type=heads

||| A container is a pair: a shape and a set of positions indexed by that shape
||| They can be used to describe various data types
public export
record Cont where
  constructor (!>)
  ||| A type of shapes
  shp : Type
  ||| For each shape, a position
  pos : shp -> Type

export typebind infixr 0 !>

%name Cont c, c', c''

||| Convenience interface to denote that a container 
||| has a given interface on positions
public export
data InterfaceOnPositions : (i : Type -> Type) -> (c : Cont) -> Type where
  ||| For every shape we need to show that the interface is satisfied
  PosInterface : (p : (s : c.shp) -> i (c.pos s)) =>
    InterfaceOnPositions i c

public export
GetInterface : InterfaceOnPositions i c -> (s : c.shp) -> i (c.pos s)
GetInterface (PosInterface @{j}) = j
