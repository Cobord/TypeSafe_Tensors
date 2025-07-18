module Misc

import Data.Vect
import Data.Fin.Arith
import Data.Vect.Quantifiers
import Decidable.Equality
import Decidable.Equality.Core
import Data.String
import Data.List
import Data.List1

%hide Builtin.infixr.(#)

||| Definition of liftA2 in terms of (<*>)
public export
liftA2 : Applicative f => f a -> f b -> f (a, b)
liftA2 fa fb = ((,) <$> fa) <*> fb

||| Starting with (Fin l -> x) and an extra x, we produce a map (Fin (S l) -> x) whose first element is the extra x 
public export
addBeginning : x -> (Fin l -> x) -> (Fin (S l) -> x)
addBeginning x _ FZ = x
addBeginning _ c (FS k') = c k'

||| Analogus to take in Data.Vect, but for Fin
public export 
takeFin : (s : Fin (S n)) -> Vect n a -> Vect (finToNat s) a
takeFin FZ _ = []
takeFin (FS s) (x :: xs) = x :: takeFin s xs

public export
interface Exp a where
  exp : a -> a

public export
Exp Double where
  exp = Prelude.exp


||| Pointwise Num structure for Applicative functors
public export
[applicativeNum] Num a => Applicative f => Num (f a) where
  xs + ys = uncurry (+) <$> liftA2 xs ys
  xs * ys = uncurry (*) <$> liftA2 xs ys
  fromInteger = pure . fromInteger

namespace Vect
  public export
  sum : Num a => Vect n a -> a
  sum = foldr (+) (fromInteger 0)
  
  public export
  prod : Num a => Vect n a -> a
  prod = foldr (*) (fromInteger 1)

namespace List
  public export
  sum : Num a => List a -> a
  sum = foldr (+) (fromInteger 0)
  
  public export
  prod : Num a => List a -> a
  prod = foldr (*) (fromInteger 1)

public export
maxInList : Ord a => List a -> Maybe a
maxInList [] = Nothing
maxInList (x :: xs) = do
  mx <- maxInList xs
  pure (Prelude.max x mx)


-- for reshaping a tensor
rr : {n, x, y : Nat}
  -> Fin (S n)
  -> {auto prf : n = x * y}
  -> (Fin (S x), Fin (S y))
rr i = ?rooo
  -- -> Data.Fin.Arith.(*) (Fin (S x)) (Fin (S y))


mm : {m, n : Nat} -> Fin (S m) -> Fin (S n) -> Fin (S (m * n))
mm = Data.Fin.Arith.(*)


||| Splits xs at each occurence of delimeter (general version for lists)
public export
splitList : Eq a =>
  (xs : List a) -> (delimeter : List a) -> (n : Nat ** Vect n (List a))
splitList xs delimeter = 
  if delimeter == []
    then (1 ** [xs]) -- Empty delimiter returns original list
    else case isInfixOfList delimeter xs of
      False => (1 ** [xs]) -- Delimiter not found, return original list
      True => 
        let (before, after) = breakOnList delimeter xs
        in case after of
          [] => (1 ** [before]) -- No more occurrences
          _  => let (restCount ** restVect) = splitList (drop (length delimeter) after) delimeter
                in (S restCount ** before :: restVect)
  where
    -- Check if list starts with delimiter
    isPrefixOfList : List a -> List a -> Bool
    isPrefixOfList [] _ = True
    isPrefixOfList _ [] = False
    isPrefixOfList (d :: ds) (x :: xs) = d == x && isPrefixOfList ds xs
    
    -- Check if delimiter occurs anywhere in the list
    isInfixOfList : List a -> List a -> Bool
    isInfixOfList del [] = del == []
    isInfixOfList del xs@(_ :: xs') = 
      isPrefixOfList del xs || isInfixOfList del xs'
    
    -- Break list at first occurrence of delimiter
    breakOnList : List a -> List a -> (List a, List a)
    breakOnList del xs = breakOnListAcc del xs []
      where
        breakOnListAcc : List a -> List a -> List a -> (List a, List a)
        breakOnListAcc del remaining acc = 
          case isPrefixOfList del remaining of
            True => (reverse acc, remaining)
            False => case remaining of
              [] => (reverse acc, [])
              (c :: cs) => breakOnListAcc del cs (c :: acc)

||| Splits xs at each occurence of delimeter (string version)
public export
splitString : (xs : String) -> (delimeter : String) -> (n : Nat ** Vect n String)
splitString xs delimeter = 
  let (n ** result) = splitList (unpack xs) (unpack delimeter)
  in (n ** pack <$> result)

||| Simple string replacement function
public export
replaceString : String -> String -> String -> String
replaceString old new str = 
  let chars = unpack str
      oldChars = unpack old
      newChars = unpack new
  in pack (replaceInList oldChars newChars chars)
  where
    replaceInList : List Char -> List Char -> List Char -> List Char
    replaceInList [] _ xs = xs
    replaceInList old new [] = []
    replaceInList old new xs@(x :: rest) =
      if isPrefixOf old xs
        then new ++ replaceInList old new (drop (length old) xs)
        else x :: replaceInList old new rest


public export
data IsNo : Dec a -> Type where
  ItIsNo : {prop : Type} -> {contra : Not prop} -> IsNo (No {prop=prop} contra)


public export
[uniqueUninhabited] {a : Type} -> {x : a} -> (de : DecEq a) =>
Uninhabited (IsNo (Equality.decEq x x)) where
  uninhabited y with (decEq x x)
    _ | (Yes _) with (y)
      _ | (ItIsNo _) impossible
    _ | (No contra) = contra Refl


||| Proof of inequality yields IsNo
public export
proofIneqIsNo : {x, y : a} -> DecEq a => ((x = y) -> Void) -> (IsNo (Equality.decEq x y))
proofIneqIsNo f with (decEq x y)
  _ | (Yes prf) = absurd (f prf)
  _ | (No contra) = ItIsNo

||| Proofs about elements existing or not existing in vectors
namespace ElemVector
  ||| A proof that an element is found in a vector at position i
  ||| Position-relevant variant of Elem
  public export
  data ElemIndex : a -> Fin n -> Vect n a -> Type where 
    Here : ElemIndex x FZ (x :: xs)
    There : (later : ElemIndex x i xs) -> ElemIndex x (FS i) (y :: xs)


  ||| A proof that an element is *not* found in vector
  ||| Dual of Elem
  data NotElem : (x : a) -> (xs : Vect n a) -> Type where
    NotElemEmpty : NotElem x []
    NotElemCons : Eq a => {x, y : a} ->
      NotElem x xs ->
      So (x /= y) ->
      NotElem x (y :: xs)



-- t : Bool -> Type
-- t False = Int
-- t True = (String, String, String)
-- 
-- f : (b : Bool) -> t b
-- f False = 3
-- f True = ?hole2

Einsumpe : {s, x : Type}
  -> (s, x) -> Type

rnnCell : {s, x : Type}
  -> (s, x) -> Einsumpe (s, x)



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




{-

interface Comult (f : Type -> Type) a where
  comult : f a -> f (f a)

{shape : Vect n Nat} -> Num a => Comult (TensorA shape) a where
  comult t = ?eir

gg : TensorA [3] Double -> TensorA [3, 3] Double
gg (TS xs) = TS $ map ?fn ?gg_rhs_0

-- [1, 2, 3]
-- can we even do outer product?
-- we wouldn't need reduce, but something like multiply?
outer : {f : Type -> Type} -> {a : Type}
  -> (Num a, Applicative f, Algebra f a)
  => f a -> f a -> f (f a)
outer xs ys = let t = liftA2 xs ys
              in ?outer_rhs 
  
 -}




-- g : String
-- g = assert_total "asdf"