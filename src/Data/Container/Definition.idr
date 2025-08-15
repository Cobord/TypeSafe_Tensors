module Data.Container.Definition

import Data.Fin
import Data.Vect

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

||| Every extension is a functor : Type -> Type
public export
Functor (Ext c) where
  map {c=shp !> pos} f (s <| v) = s <| f . v

public export
Functor (Ext c) => Functor (Ext d) => Functor ((Ext d) . (Ext c)) where
  map f e = (map f) <$> e

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
||| Data.Functor.positions is this definition for Naperian containers
||| i.e. containers with a unit shape
public export
positionsCont : {c : Cont} -> {sh : c.shp} ->
  Ext c (c.pos sh)
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
setExt (shapeExt <| indexCont) i x
  = shapeExt <| updateAt indexCont (i, x)

||| Convenience interface to denote that a container 
||| has a given interface on positions
public export
data InterfaceOnPositions : (i : Type -> Type) -> (c : Cont) -> Type where
  PosInterface : (p : (s : c.shp) -> i (c.pos s)) =>
    InterfaceOnPositions i c

 


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


public export infixr 0 >@<
||| Composition of containers (polynomial composition)
||| Non-symmetric in general
||| Monoid with CUnit
public export
(>@<) : Cont -> Cont -> Cont
c >@< d = ((sh <| ind) : Ext c (d.shp)) !> (cp : c.pos sh ** d.pos (ind cp))



||| Specialised to Hancock tensor product
||| Could be as simple as foldr (><) CUnit, but want to take care of associativity
public export
prodConts : List Cont -> Cont
prodConts = foldr (><) CUnit
-- prodConts [] = CUnit
-- prodConts (c :: cs) = c >< prodConts cs

