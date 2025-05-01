module Tensor.ContainerTensor.TensorUtils

import Data.Vect 
import Data.Nat -- Add import for Cast

import Tensor.ContainerTensor.Tensor
import Tensor.Naperian
import Data.Rig

public export
zeros : Rig a => {shape : ApplV conts} -> Tensor shape a
zeros = tensorReplicate zero

public export
ones : Rig a => {shape : ApplV conts} -> Tensor shape a
ones = tensorReplicate one

public export
range : {n : Nat} -> Cast Nat a => Tensor' [n] a
range {n} = fromArray' $ cast . finToNat <$> positions {f=Vect n}

-- public export
-- flatten : Tensor shape a -> List a
-- flatten = foldr (::) []


-- public export
-- eye : Rig a => Tensor [n, n] a
-- eye = ?eye_rhs