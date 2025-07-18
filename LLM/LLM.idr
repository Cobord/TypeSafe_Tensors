module LLM.LLM

import System
import System.Escape
import Data.String

LLM : Type -> Type
LLM = IO

-- For now, hardcode the model - you can change this later
defaultModel : String
defaultModel = "qwen2.5:0.5b"

-- Main LLM query function using the run function
query : String -> LLM String
query prompt = do
  let escapedPrompt = escapeArg prompt
  -- Redirect stderr to /dev/null to avoid progress indicators clearing the screen
  let command = "echo " ++ escapedPrompt ++ " | ollama run " ++ defaultModel ++ " 2>/dev/null"
  
  putStrLn ("Executing: " ++ prompt)  -- Debug output
  (output, exitCode) <- run command
  
  case exitCode of
    0 => pure (trim output)
    _ => pure ("Error: ollama failed with exit code " ++ show exitCode)

-- Test the LLM integration
testLLM : IO ()
testLLM = do
  putStrLn "Testing LLM integration..."
  putStrLn ("Using model: " ++ defaultModel)
  
  response1 <- query "What is 2 + 2?"
  putStrLn ("Model response: " ++ response1)
  
  response2 <- query "Explain what a monad is in one sentence."
  putStrLn ("Model response: " ++ response2)