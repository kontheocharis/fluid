module Refactoring.FillHoles (fillHoles, FillHolesArgs) where

import Lang (Program)
import Refactoring.Utils (FromRefactorArgs (..), Refact)

data FillHolesArgs = FillHolesArgs

instance FromRefactorArgs FillHolesArgs where
  fromRefactorArgs _ = Just FillHolesArgs

fillHoles :: FillHolesArgs -> Program -> Refact Program
fillHoles _ = return -- This already fills in holes as it passes through the typechecker!
