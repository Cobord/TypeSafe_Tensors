module Misc

import Data.Vect
import Data.Fin.Arith
import Data.Vect.Quantifiers


%hide Builtin.infixr.(#)



public export
liftA2 : Applicative f => f a -> f b -> f (a, b)
liftA2 fa fb = ((,) <$> fa) <*> fb

-- Starting with (Fin l -> x) and an extra x, we produce a map (Fin (S l) -> x) 
-- whose first element is the extra x 
public export
addBeginning : x -> (Fin l -> x) -> (Fin (S l) -> x)
addBeginning x _ FZ = x
addBeginning _ c (FS k') = c k'

public export
interface Exp a where
  exp : a -> a

public export
Exp Double where
  exp = Prelude.exp


-- for reshaping a tensor
rr : {n, x, y : Nat}
  -> Fin (S n)
  -> {auto prf : n = x * y}
  -> (Fin (S x), Fin (S y))
rr i = ?rooo
  -- -> Data.Fin.Arith.(*) (Fin (S x)) (Fin (S y))



-- t : {A, B : Type}
--   -> Bool -> Type
-- t False = A
-- t True = B

-- iso : {A, B : Type}
--   -> (A, B) -> (b : Bool) -> t {A=A} {B=B} b
-- iso (a, _) False = a
-- iso (_, b) True = b
-- 
-- tt : {A : Type} -> {B : A -> Type}
--   -> Bool -> Type
-- tt False = A
-- tt True = B ?otetwe_1
-- 
-- iso2 : {A : Type} -> {B : A -> Type}
--   -> (a : A ** B a) -> (b : Bool) -> tt {A=A} {B=B} b
-- iso2 ((a ** _)) False = a
-- iso2 ((a ** b)) True = ?tuu_2


mm : {m, n : Nat} -> Fin (S m) -> Fin (S n) -> Fin (S (m * n))
mm = Data.Fin.Arith.(*)

-- t : Bool -> Type
-- t False = Int
-- t True = (String, String, String)
-- 
-- f : (b : Bool) -> t b
-- f False = 3
-- f True = ?hole2

OutputType : {s, x : Type}
  -> (s, x) -> Type

rnnCell : {s, x : Type}
  -> (s, x) -> OutputType (s, x)



interface Interface1 a where
  constructor MkInterface1
  getInterface1 : a

interface Interface1 t => Interface2 t where
  constructor MkInterface2
  getInterface2 : t

Interface1 Nat where
  getInterface1 = 3

[four] Interface1 Nat where
  getInterface1 = 4

getBoth : (i : Interface2 a) => (a, a)
getBoth = (getInterface1, getInterface2)


t : Type

ll : Num a => List a
ll = ?ll_rhs

ll2 : List (Num a => a)
ll2 = ?ll2_rhs

lk : (a :  Type ** List (Interface1 a => a))
lk = (Nat ** [3, 5])

private prefix 0 #
record ApplF (lprop : Vect m ((Type -> Type) -> Type)) where
  constructor (#)
  F : Type -> Type
  {auto 0 prf : All (\p => p F) lprop}

interface MyInterface f where
  tttt : (a -> b) -> (f a -> f b)


ex0 : List (ApplF [Functor, Applicative])
ex0 = [# Vect 4]

ex1 : List (ApplF [Functor, Applicative])
ex1 = [# List, # Vect 4]

ex2 : List (ApplF [Functor, Applicative])
ex2 = [# Maybe, # List, # Vect 100]

data Repr : Type -> Type where
  MkRepr : (a -> Int) -> Repr a

failing
  shouldNotTypeCheck : List (ApplF [Functor, Applicative])
  shouldNotTypeCheck = [# Repr]

  aIntt : Int
  aIntt = 3



