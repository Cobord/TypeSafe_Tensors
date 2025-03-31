module Tensor.Naperian

import Data.Vect

import Tensor.Tensor

-- Needed to define transposition
{-
Lists are not Naperian, because their shape isn't uniform (they can be of different lengths)
Stream is Naperian, and is represented by Nat
Vect n is Naperian, and are represented by Fin n

BinTree in general is not Naperian, but if we restrict to trees of a particular shape, then they are Naperian

Q: Are Naperian functors just containers with constant shape?
This is about non-ragged shapes.
Would ragged shapes imply dependent types?
-}
public export
interface Functor f => Naperian f where
    Log : Type
    lookup : f a -> Log -> a -- this and the line below
    tabulate : (Log -> a) -> f a -- are an isomorphism

public export
positions : Naperian f => f (Log {f=f})
positions = tabulate id

public export
transpose : (Naperian f, Naperian g) => f (g a) -> g (f a)
transpose {f} {g} x = tabulate <$> tabulate (flip (lookup . (lookup x)))
-- 

listLookup : List a -> Nat -> a
listLookup xs 0 = ?listLookup_rhs_0
listLookup xs (S k) = ?listLookup_rhs_1


vectTabulate : {n : Nat} -> (Fin n -> a) -> Vect n a
vectTabulate {n = 0} f = []
vectTabulate {n = (S k)} f = f FZ :: vectTabulate {n=k} (\i => f (FS i))

vectPositions : {n : Nat} -> Vect n (Fin n)
vectPositions {n = 0} = []
vectPositions {n = (S k)} = FZ :: (FS <$> vectPositions)

{n : Nat} -> Naperian (Vect n) where
    Log = Fin n
    lookup = flip index
    tabulate = vectTabulate

pairLookup : Pair a a -> Bool -> a
pairLookup p False = fst p
pairLookup p True = snd p

-- AI generated, not checked if correct
tensorTabulate : {shape : Vect n Nat}
  -> (IndexT shape -> a) -> Tensor shape a
tensorTabulate {shape = []} f = TZ (f Nil)
tensorTabulate {shape = (s :: ss)} f = TS $ vectTabulate (\i => tensorTabulate {shape=ss} (\is => f (i :: is)))

{shape : Vect n Nat} -> Naperian (Tensor shape) where
    Log = IndexT shape
    lookup = flip indexTensor
    tabulate = tensorTabulate

vectPositionsEx : Vect 3 (Fin 3)
vectPositionsEx = positions

tensorPositionsEx : Tensor [3, 3, 3] (IndexT [3, 3, 3])
tensorPositionsEx = positions

  -- not sure how to represent Pair, it's curried?
-- Naperian (Pair) where
--     Log = Bool
--     lookup = pairLookup
--     tabulate f = (f False, f True)
    


{-
           a
         x  y

  a'                a''
x' y'             x'' y''

transposed would be


           a
         a'  a''

  x                  y
x' x''             y' y''

---

If it was ragged we would not be able to transpose it
-}
