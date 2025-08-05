module Architectures.Activations

import Misc

public export
relu : Ord a => Num a => a -> a
relu x = max 0 x

public export
sigmoid : Fractional a => Exp a => a -> a
sigmoid x = 1 / (1 + ex) where ex = exp x

