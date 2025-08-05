module Architectures.Residual

import Para.Para

public export
addResidual : Num a => Para a a -> Para a a
addResidual (MkPara param run) = MkPara param
  (\input, p => (run input p) + input)
