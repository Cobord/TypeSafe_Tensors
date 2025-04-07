module Rig

import Data.Fin
import Data.Vect

import Misc

-- We're also interested in natural numbers as an example
public export
interface Rig a where
  zero : a
  one : a
  (~+~) : a -> a -> a
  (~*~) : a -> a -> a
  -- also laws, but we don't care right now

export infixr 6 ~+~
export infixr 7 ~*~

public export
Rig Double where
  zero = 0
  one = 1
  (~+~) = (+)
  (~*~) = (*)

public export
Rig Nat where
  zero = 0
  one = 1
  (~+~) = (+)
  (~*~) = (*)


public export
{n : Nat} -> Rig a => Rig (Vect n a) where
  zero = replicate n zero
  one = replicate n one
  xs ~+~ ys = zipWith (~+~) xs ys
  xs ~*~ ys = zipWith (~*~) xs ys

-- public export
-- (Rig a, Applicative f) => Rig (f a) where
--   zero = pure zero
--   one = pure one
--   xs ~+~ ys = uncurry (~+~) <$> liftA2 xs ys
--   xs ~*~ ys = uncurry (~*~) <$> liftA2 xs ys

public export
sum : Rig a => Vect n a -> a
sum = foldr (~+~) zero

public export
prod : Rig a => Vect n a -> a
prod = foldr (~*~) one