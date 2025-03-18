module Ring

import Data.Fin
import Data.Vect

import Tensor

public export
interface Ring a where
  zero : a
  one : a
  (~+~) : a -> a -> a
  (~*~) : a -> a -> a
  -- also laws, but we don't care right now

export infixr 6 ~+~
export infixr 7 ~*~

public export
Ring Double where
  zero = 0
  one = 1
  (~+~) = (+)
  (~*~) = (*)

-- Pointwise ring structure
public export
{shape : Vect n Nat} -> Ring a => Ring (Tensor shape a) where
  zero = tensorReplicate zero
  one = tensorReplicate one
  xs ~+~ ys = map (uncurry (~+~)) $ liftA2 xs ys
  xs ~*~ ys = map (uncurry (~*~)) $ liftA2 xs ys
