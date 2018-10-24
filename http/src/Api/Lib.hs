module Api.Lib where

import           Api.Api                  (API, aqlApi)
import           Api.Config.Config        (Config (..))
import           Api.Config.Environment   (logger)

-- servant-server
import           Servant                  (Application, Proxy (Proxy), serve)

-- warp
import           Network.Wai.Handler.Warp (defaultSettings, runSettings,
                                           setPort)

startApp :: Config -> IO ()
startApp config = runSettings
  (setPort (apiPort config) defaultSettings)
  (app config)

app :: Config -> Application
app config = logger (environment config) $ serve api aqlApi

api :: Proxy API
api = Proxy
