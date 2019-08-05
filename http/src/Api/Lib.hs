{-
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/cql`, the categorical query language.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}
module Api.Lib where

import           Api.Api                  (API, cqlApi)
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
app config = logger (environment config) $ serve api cqlApi

api :: Proxy API
api = Proxy
