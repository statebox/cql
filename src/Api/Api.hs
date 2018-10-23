{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Api.Api where

-- servant-server
import           Servant ((:>), Get, Handler, PlainText, ReqBody, Server)

type API = "aql" :> ReqBody '[PlainText] String :> Get '[PlainText] String

aqlApi :: Server API
aqlApi = aqlEndpoint

aqlEndpoint :: String -> Handler String
aqlEndpoint = undefined
