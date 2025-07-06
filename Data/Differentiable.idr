module Data.Differentiable

import Data.Container.Definition
import Data.Container.Morphism
import Data.Vect
import Data.Fin
import Data.Stream

{-
Existing diff frameworks:
https://blog.jle.im/entry/purely-functional-typed-models-1.html
https://hackage.haskell.org/package/grenade-0.1.0
 -}

||| Tangent space of a type via containers
||| Every fiber needs to be a commutative monoid
data D : (a : Type) -> Type where
  MkTangent :
    (c : Cont) ->
    {auto mon : (a : c.shp) -> Monoid (c.pos a)} ->
    D (c.shp)

||| Convenience function to create a tangent space
MkD : {a : Type} ->
  (b : a -> Type) ->
  {auto mon : (x : a) -> Monoid (b x)} ->
  D a
MkD b = MkTangent $ (x : a) !> b x

||| Extract the tangent space
T : D a -> a -> Type
T (MkTangent c) = c.pos

-- Concrete instances
%hint
doubleTangent : D Double
doubleTangent = MkD (\_ => Double) {mon=(\_ => Additive)}

%hint
numTangent : {a : Type} ->
  Num a => D a
numTangent = MkD (\_ => a) {mon=(\_ => Additive)}

%hint
unitTangent : D Unit
unitTangent = MkD (\_ => ())

%hint
public export
pairD : D a -> D (a, a)
pairD (MkTangent (_ !> pos)) = MkD
  (\(a1, a2) => (pos a1, pos a2))
  {mon=(\(a1, a2) => %search)}

-- Can't really do lists, not sure why
listD : D a -> D (List a)
listD (MkTangent (shp !> pos)) = MkD
  (\xs => let tt = pos <$> xs in ?listD_rhs_1)
  {mon=(\x => ?llll)}

-- But vectors work
vectD : {n : Nat} -> D a -> D (Vect n a)
vectD (MkTangent (shp !> pos) {mon=monV}) = MkD
  (\xs => (i : Fin n) -> pos (index i xs))
  {mon=(\xs => ?vectD_mon)}

||| Differentiable functions, using dependent charts
data IsDifferentiable : (f : a -> b) -> Type where
  MkIsDifferentiable :
    {c, d : Cont} -> 
    {auto monc : (a : c.shp) -> Monoid (c.pos a)} ->
    {auto mond : (b : d.shp) -> Monoid (d.pos b)} ->
    (dChart : c =&> d) ->
    IsDifferentiable (dChart.fwd)

MkDiff :
  {a, b : Type} -> {auto da : D a} -> {auto db : D b} ->
  {f : a -> b} ->
  (f' : (x : a) -> T da x -> T db (f x)) ->
  IsDifferentiable f
MkDiff {f} {da = (MkTangent (a !> a'))}
           {db = (MkTangent (b !> b'))} f'
  = MkIsDifferentiable
  {c=(x : a) !> a' x}
  {d=(y : b) !> b' y}
  (f <&! f')

MulC : Num a => (a, a) -> a
MulC = uncurry (*)

AddC : Num a => (a, a) -> a
AddC = uncurry (+)

ZeroC : Num a => Unit -> a
ZeroC = const 0

Del : a -> Unit
Del _ = ()

Copy : a -> (a, a)
Copy a = (a, a)

-- Example differentiable function
mulDifferentiable : IsDifferentiable MulC
mulDifferentiable = MkDiff (\(a1, a2), (da, db) => a2 * da + a1 * db)

addDifferentiable : IsDifferentiable AddC
addDifferentiable = MkDiff (\(a1, a2), (da, db) => da + db)

zeroDifferentiable : IsDifferentiable ZeroC
zeroDifferentiable = MkDiff (\_, _ => 0)

delDifferentiable : {a : Type} -> Num a => IsDifferentiable (Del {a})
delDifferentiable = MkDiff (\_, _ => ())

copyDifferentiable : {a : Type} -> Num a => IsDifferentiable (Copy {a})
copyDifferentiable = MkDiff (\_, da => (da, da))


{-
We'd want a module to turn pointful code into categories.
Then we'd know how to differentiate categories

 -}

fn : (Double, Double) -> Double
fn (x, y) = t + 3
  where t = x * y


