module Data.Container.Definition

import Decidable.Equality
import Data.Fin
import Data.Vect
import Data.DPair

import Data.Tree
import Data.Functor.Naperian
import Misc

%hide Data.Vect.fromList
%hide Builtin.fst

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

public export
Const2 : Type -> Type -> Cont
Const2 x y = (_ : x) !> y

||| Naperian container
public export
Nap : Type -> Cont
Nap x = Const2 () x

public export
Const : Type -> Cont
Const x = Const2 x x

public export
CUnit : Cont
CUnit = Const Unit

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

||| Extension of a container
||| This allows us to talk about the content, or payload of a container
public export
record Ext (c : Cont) (x : Type) where
  constructor (<|)
  shapeExt : c.shp
  indexCont : c.pos shapeExt -> x

||| Container c can be said to be "full off" a type x
||| Sometimes used as infix operator to aid readability
||| c `fullOf` x is easier to read than Ext c x
public export
fullOf : Cont -> Type -> Type
fullOf c x = Ext c x 

||| Notably, Eq instance is not possible to write for a general Ext c a
||| This is because Eq needs to be total, and some containers have an infinite number of positions, meaning they cannot be checked in finite time
||| However, we can write ...
||| TODO do I even need this? Computing equality for general extensions is hard, and at best this piece of code can sometmes be 
namespace EqExt
  ||| Structure needed to store the equality data for Ext
  public export
  record EqExt (e1, e2 : Ext c a) where
    constructor MkEqExt
    ||| The shapes must be equal
    shapesEqual : e1.shapeExt = e2.shapeExt
    ||| For each position in that shape, the values must be equal
    ||| Relying on rewrite to get the correct type for the position
    valuesEqual : (p : c.pos (e1.shapeExt)) ->
      e1.indexCont p =
      e2.indexCont (rewrite__impl (c.pos) (sym shapesEqual) p)
    {-
    Another alternative is to use DecEq, and a different explicit rewrite
     -}

  public export
  decEqExt : (e1, e2 : Ext c a) ->
    EqExt e1 e2 ->
    Dec (e1 = e2)
  decEqExt e1 e2 (MkEqExt shapesEqual valuesEqual)
    = Yes ?decEqExt_rhs_0 -- complicated, but doable?

  
||| Every extension is a functor : Type -> Type
public export
Functor (Ext c) where
  map {c=shp !> pos} f (s <| v) = s <| f . v

||| Map preserves the shape of the extension
public export
mapShapeExt : {c : Cont} ->
  (l : c `fullOf` a) ->
  shapeExt (f <$> l) = shapeExt l
mapShapeExt {c=shp !> pos} (sh <| _) = Refl

public export
mapIndexCont : {0 f : a -> b} -> {c : Cont} ->
  (l : c `fullOf` a) ->
  (ps : c.pos (shapeExt (f <$> l))) ->
  f (indexCont l (rewrite sym (mapShapeExt {f=f} l) in ps))
    = indexCont (f <$> l) ps
mapIndexCont {c=shp !> pos} (sh <| contentAt) ps = Refl

public export
Functor ((Ext d) . (Ext c)) where
  map f e = (map f) <$> e

public export
composeExtensions : List Cont -> Type -> Type
composeExtensions [] a = Ext CUnit a
composeExtensions [c] a = Ext c a
composeExtensions (c :: d :: cs) a = Ext c (composeExtensions (d :: cs) a)

public export
[fe] {shape : List Cont} -> Functor (composeExtensions shape) where
  map {shape = []} f = map f
  map {shape = [s]} f = map f
  map {shape = (s :: s' :: ss)} f = (map @{fe} f <$>)

public export
EmptyExt : Ext (Nap l) ()
EmptyExt = () <| \_ => ()

public export
liftA2ConstCont : Ext (Nap l) a -> Ext (Nap l) b -> Ext (Nap l) (a, b)
liftA2ConstCont (() <| va) (() <| vb) = () <| (\x => (va x, vb x))

||| The extension of any container with a unit shape
||| is an applicative functor
||| Examples: Scalar, Pair, Vect n, Stream
||| Notably, List and Maybe are also applicative
public export
Applicative (Ext (Nap l)) where
  pure a = () <| (\_ => a)
  fs <*> xs = uncurry ($) <$> liftA2ConstCont fs xs 

||| The extension of any container with a unit shape
||| is an Naperian functor
||| Notably, lists are not applicative
public export
{l : Type} -> Naperian (Ext (Nap l)) where
  Log = l
  lookup = indexCont
  tabulate t = () <| t

||| Generalisation of 'positions' from Data.Functor
||| Works for an arbitrary container, as long as we supply its shape
||| The definition in Data.Functor.positions is for Naperian containers
||| i.e. containers with a unit shape
public export
positionsCont : {sh : c.shp} -> Ext c (c.pos sh)
positionsCont = sh <| id

--ex1 : String
--ex1 = let g = toConcreteTy $ Definition.positions {c=Vect 3} ()
--          gg = toConcreteTy $ Definition.positions {c=BinTree} (NodeS LeafS LeafS)
--          h = toConcreteTy $ Definition.positions {c=List} 4
--      in show gg


||| Container setter
public export
setExt : (e : Ext ((!>) sh ps) x) ->
  ((s : sh) -> Eq (ps s)) =>
  (i : ps (shapeExt e)) ->
  x ->
  Ext ((!>) sh ps) x
setExt (sh <| contentAt) i x
  = sh <| updateAt contentAt (i, x)


namespace ConcreteContainer
  ||| Idris already has concrete implementations of many containers 
  ||| we're interested in, and often for concrete instantiations of 
  ||| various container types it's useful to be able to do it using 
  ||| the Idris instance
  public export
  interface FromConcrete (cont : Cont) where
    constructor MkConcrete
    concreteType : Type -> Type
    concreteFunctor : Functor concreteType
    fromConcreteTy : concreteType a -> Ext cont a
    toConcreteTy : Ext cont a -> concreteType a
  
  
  public export
  data AllConcrete : List Cont -> Type where
    Nil : AllConcrete []
    Cons : {c : Cont} -> {cs : List Cont} ->
      (firstConcrete : FromConcrete c) =>
      (restConcrete : AllConcrete cs) =>
      AllConcrete (c :: cs)


-- public export
-- fromConcreteMap : {cont1, cont2 : Cont} ->
--   (fc1 : FromConcrete cont1) => (fc2 : FromConcrete cont2) =>
--   (concreteType @{fc1} a -> concreteType @{fc2} b) ->
--   cont1 `fullOf` a -> cont2 `fullOf` b
-- fromConcreteMap f = fromConcrete @{fc2} . f . toConcrete @{fc1}


 
||| Derivative of a container
Deriv : Cont -> Cont


public export infixr 0 ><
||| Hancock, Dirichlet, or tensor product of containers
||| Monoid with CUnit
public export
(><) : Cont -> Cont -> Cont
(shp !> pos) >< (shp' !> pos') = ((s, s') : (shp, shp')) !> (pos s, pos' s')

public export infixr 0 >+<
||| Coproduct of containers
public export
(>+<) : Cont -> Cont -> Cont
(shp !> pos) >+< (shp' !> pos') = (es : Either shp shp') !> (case es of
  Left s => pos s
  Right s' => pos' s')


namespace ContainerComposition
  public export infixr 0 >@<
  ||| Composition of containers (polynomial composition)
  ||| Non-symmetric in general
  ||| Monoid with CUnit
  public export
  (>@<) : Cont -> Cont -> Cont
  c >@< d = ((sh <| ind) : Ext c (d.shp)) !> (cp : c.pos sh ** d.pos (ind cp))
  -- c >@< d = ((sh <| ind) : Ext c (d.shp)) !> (cp : c.pos sh ** d.pos (ind cp))
  
  ||| We pattern match on three cases to simplify resulting expressions
  ||| This isn't 'public', not sure if that's a good idea, but it prevents the typechecker from reducing this composition at callsites when trying to create tensors from concrete ones
  public export
  composeContainers : List Cont -> Cont
  composeContainers [] = CUnit
  composeContainers [c] = c
  composeContainers (c :: d :: cs) = c >@< composeContainers (d :: cs)

  ||| This states a list version of 
  ||| Ext c2 . Ext c1 = Ext (c2 . c1)
  public export
  toContainerComp : {shape : List Cont} ->
    composeExtensions shape a -> Ext (composeContainers shape) a
  toContainerComp {shape = []} ce = ce
  toContainerComp {shape = [c]} ce = ce
  toContainerComp {shape = (c :: d :: cs)} (shp <| idx) = 
    let rst = (toContainerComp {shape=(d :: cs)}) . idx
    in (shp <| shapeExt . rst) <| (\(cp ** fsh) => indexCont (rst cp) fsh)

  public export
  fromContainerComp : {shape : List Cont} ->
    Ext (composeContainers shape) a -> composeExtensions shape a
  fromContainerComp {shape = []} ce = ce
  fromContainerComp {shape = [c]} ce = ce
  fromContainerComp {shape = (c :: d :: cs)} ((csh <| cpos) <| idx)
    = csh <| \d => fromContainerComp (cpos d <| curry idx d)



||| Specialised to Hancock tensor product
||| Could be as simple as foldr (><) CUnit, but want to take care of associativity
public export
prodConts : List Cont -> Cont
prodConts = foldr (><) CUnit
-- prodConts [] = CUnit
-- prodConts (c :: cs) = c >< prodConts cs

