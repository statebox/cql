module Api.App where

import           Api.Config.Config      (Config (Config))
import           Api.Config.Environment (Environment (Development))
import           Api.Lib                (startApp)

-- base
import           Data.Maybe             (fromMaybe)
import           System.Environment     (lookupEnv)
import           Text.Read              (readMaybe)

app :: IO ()
app = do
  environment <- lookupEnvVar "AQL_ENV" Development
  apiPort <- lookupEnvVar "PORT" 8080
  startApp $ Config environment apiPort

lookupEnvVar :: (Read a, Show a) => String -> a -> IO a
lookupEnvVar variable default' = do
    maybeValue <- lookupEnv variable
    return $ fromMaybe default' $ maybeValue >>= readMaybe
