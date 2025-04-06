module Para.Para

import Data.Vect
import Data.Vect.Quantifiers

public export
record Para (a : Type) (b : Type) where
    constructor MkPara
    Param : a -> Type
    Run : (x : a) -> Param x -> b


public export
composePara : Para a b -> Para b c -> Para a c
composePara (MkPara p f) (MkPara q g) = MkPara (\x => (p' : p x ** q (f x p'))) (\x, (p' ** q') => g (f x p') q')

-- composePara_rhs_1 : (p : Vect n Type) -> (q : Vect m Type)
--   -> (a -> All Prelude.id p -> b)
--   -> (b -> All Prelude.id q -> c)
--   -> (a -> All Prelude.id (p ++ q) -> c)
-- composePara_rhs_1 [] [] f g a [] = ?composePara_rhs_1_rhs_2
-- composePara_rhs_1 [] (q :: ws) f g a (pq :: pqs) = ?composePara_rhs_1_rhs_3
-- composePara_rhs_1 (p :: ps) q f g a pq = ?composePara_rhs_1_rhs_1
-- 
-- composePara : Para a n b -> Para b m c -> Para a (n + m) c
-- composePara (MkPara p f) (MkPara q g) = MkPara (p ++ q) (composePara_rhs_1 p q f g)


