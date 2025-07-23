module Training.TrainingLoop

import Data.Vect

import Para.Para
import Misc

Model : (input : Type) -> (output : Type) -> Type
Model input output = Para input output

train : {input, output, l : Type} ->
  (model : Model input output) ->
  (init : (x : input) -> IO (Param model x)) ->
  (dataSampler : IO (input, output)) ->
  (loss : (output, output) -> l) ->
  IO ()
train model init dataSampler loss = do
  (x, yTrue) <- dataSampler
  p <- init x
  let yPred = Run model x p
  let l' = loss (yPred, yTrue)
  pure ?hmm






