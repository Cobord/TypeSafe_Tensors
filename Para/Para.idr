module Para.Para

import Data.Vect
import Data.Vect.Quantifiers

record Para (a : Type) (n : Nat) (b : Type) where
    constructor MkPara
    Param : Vect n Type
    Impl : a -> (p : HVect Param) -> b



composePara_rhs_1 : (p : Vect n Type) -> (q : Vect m Type)
  -> (a -> All Prelude.id p -> b)
  -> (b -> All Prelude.id q -> c)
  -> (a -> All Prelude.id (p ++ q) -> c)
composePara_rhs_1 [] [] f g a [] = ?composePara_rhs_1_rhs_2
composePara_rhs_1 [] (q :: ws) f g a (pq :: pqs) = ?composePara_rhs_1_rhs_3
composePara_rhs_1 (p :: ps) q f g a pq = ?composePara_rhs_1_rhs_1

composePara : Para a n b -> Para b m c -> Para a (n + m) c
composePara (MkPara p f) (MkPara q g) = MkPara (p ++ q) (composePara_rhs_1 p q f g)


