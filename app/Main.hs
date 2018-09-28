module Main where

import Language.AQL

input = " "

result = runProg input

main :: IO ()
main = do
  putStrLn $ show result
