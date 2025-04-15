module Misc

import Data.Vect
import Data.Fin.Arith
import Data.Vect.Quantifiers



public export
liftA2 : Applicative f => f a -> f b -> f (a, b)
liftA2 fa fb = ((,) <$> fa) <*> fb


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
record FunctorImplicit where
  constructor (#)
  ffff : Type -> Type
  {auto 0 prf : Functor ffff}

ex1 : List FunctorImplicit
ex1 = [# List, # Vect 4]

ex2 : List FunctorImplicit
ex2 = [# Maybe, # List, # Vect 100]

data Repr : Type -> Type where
  MkRepr : (a -> Int) -> Repr a

failing
  shouldNotTypeCheck : List FunctorImplicit
  shouldNotTypeCheck = [# Repr]

  aIntt : Int
  aIntt = 3




