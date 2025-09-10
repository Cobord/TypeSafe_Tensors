module Data.Container.Products

import Data.DPair
import Decidable.Equality

import Data.Container.Object.Definition
import Data.Container.Extension.Definition

import Misc

public export infixr 0 ><
public export infixr 0 >*<
public export infixr 0 >+<
public export infixr 0 >@

||| Hancock, Dirichlet, or tensor product of containers
||| Monoid with CUnit
public export
(><) : Cont -> Cont -> Cont
(shp !> pos) >< (shp' !> pos') = ((s, s') : (shp, shp')) !> (pos s, pos' s')

||| Product of containers
public export
(>*<) : Cont -> Cont -> Cont
(shp !> pos) >*< (shp' !> pos')
  = ((s, s') : (shp, shp')) !> Either (pos s) (pos' s')

||| Coproduct of containers
public export
(>+<) : Cont -> Cont -> Cont
(shp !> pos) >+< (shp' !> pos') = (es : Either shp shp') !> (case es of
  Left s => pos s
  Right s' => pos' s')

||| Composition of containers making Ext (c >@ d) = (Ext c) . (Ext d)
||| Non-symmetric in general, and not in diagrammatic order
||| Monoid with Scalar
public export
(>@) : Cont -> Cont -> Cont
c >@ d = (ex : Ext c d.shp) !> (cp : c.pos (shapeExt ex) ** d.pos (index ex cp))

public export infixr 0 @>

||| Diagrammatic composition of containers
public export
(@>) : Cont -> Cont -> Cont
c @> d = (ex : Ext d c.shp) !> (dp : d.pos (shapeExt ex) ** c.pos (index ex dp))


||| Derivative of a container
||| Given c=(shp !> pos) the derivative can be thought of as 
||| a shape s : shp, a distinguished position p : pos s, and the set of *all other positions*
public export
Deriv : (c : Cont) ->
  InterfaceOnPositions c DecEq =>
  Cont
Deriv (shp !> pos) @{MkI}
  = ((s ** p) : DPair shp pos) !> (p' : pos s ** IsNo (decEq p p'))


public export
shapesOnly : (a : Type) -> Cont
shapesOnly a = (x : a) !> Void

public export
DecEq Void where
  decEq x1 _ = void x1

shapesIoP : InterfaceOnPositions (shapesOnly a) DecEq
shapesIoP = MkI

derivConst : (a : Type) -> Ext (Deriv (shapesOnly a)) Integer
derivConst a = ?aa <| ?bb
