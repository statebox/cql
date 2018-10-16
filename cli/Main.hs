module Main where

import           Language.AQL
import           System.Environment


main :: IO ()
main = do args <- getArgs
          w <- mapM readFile args
          _ <- mapM (putStrLn . f' . runProg) w
          return ()
 where f' (Left x)        = x
       f' (Right (_,_,c)) = show c

