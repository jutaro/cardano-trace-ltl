module Main where

import           Cardano.Trace.Feed
import           System.Environment

main :: IO ()
main = do
  [!input, !output] <- getArgs
  verify input output
