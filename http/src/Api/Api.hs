{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Api.Api where

import           Language.AQL (runProg)

-- servant-server
import           Servant      ((:>), Handler, PlainText, Post, ReqBody, Server)

type API = "aql" :> ReqBody '[PlainText] String :> Post '[PlainText] String

aqlApi :: Server API
aqlApi = aqlEndpoint

aqlEndpoint :: String -> Handler String
aqlEndpoint aqlDefinition = do
  let aqlEnvironemnt = runProg aqlDefinition
  pure $ either id (\(_, _, env) -> show env) aqlEnvironemnt
