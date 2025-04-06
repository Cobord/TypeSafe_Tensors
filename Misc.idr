module Misc

import Data.Vect
import Data.Fin.Arith

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

t : Bool -> Type
t False = Int
t True = (String, String, String)

f : (b : Bool) -> t b
f False = 3
f True = ?hole2

OutputType : {s, x : Type}
  -> (s, x) -> Type

rnnCell : {s, x : Type}
  -> (s, x) -> OutputType (s, x)



