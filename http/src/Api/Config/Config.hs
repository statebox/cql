module Api.Config.Config where

import           Api.Config.Environment (Environment)

data Config = Config
  { environment :: Environment
  , apiPort     :: Int
  }
