module Api.Config.Environment where

-- wai
import           Network.Wai                          (Middleware)

-- wai-extra
import           Network.Wai.Middleware.RequestLogger (logStdout, logStdoutDev)

data Environment
    = Development
    | Production
    deriving (Show, Read)

logger :: Environment -> Middleware
logger Development = logStdoutDev
logger Production  = logStdout
