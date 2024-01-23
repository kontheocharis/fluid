{-# LANGUAGE TemplateHaskell #-}

module Resources.Prelude (preludePath, preludeContents) where

import Control.Monad ((>>=))
import Data.FileEmbed (embedStringFile, makeRelativeToProject, strToExp)
import Data.String (IsString)
import GHC.IO (FilePath)

-- | The contents of the Prelude file.
preludePath :: FilePath
preludePath = $(makeRelativeToProject "src/Resources/prelude.fluid" >>= strToExp)

-- | The contents of the Prelude file.
preludeContents :: (IsString a) => a
preludeContents = $(makeRelativeToProject "src/Resources/prelude.fluid" >>= embedStringFile)
