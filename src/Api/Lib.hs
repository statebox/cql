module Api.Lib where

import           Api.Config.Config (Config (..))

startApp :: Config -> IO ()
startApp _ = putStrLn "hello!"
