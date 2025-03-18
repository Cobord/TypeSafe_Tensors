module Misc

t : {A, B : Type}
  -> Bool -> Type
t False = A
t True = B

iso : {A, B : Type}
  -> (A, B) -> (b : Bool) -> t {A=A} {B=B} b
iso (a, _) False = a
iso (_, b) True = b

tt : {A : Type} -> {B : A -> Type}
  -> Bool -> Type
tt False = A
tt True = B ?otetwe_1

iso2 : {A : Type} -> {B : A -> Type}
  -> (a : A ** B a) -> (b : Bool) -> tt {A=A} {B=B} b
iso2 ((a ** _)) False = a
iso2 ((a ** b)) True = ?tuu_2