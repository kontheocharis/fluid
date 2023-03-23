module Test (module Test) where

{-
  - Industry Experiences with Large-Scale Refactoring

  1. Evolution of APIs
    - An Empirical Study of Refactoring Challenges and Benefits at Microsoft
    - Lessons Learned from Large-Scale Refactoring
    - Large-Scale Automated Refactoring Using ClangMR
  2. Evolution of design
    - Recommending Refactoring Operations in Large Software Systems
  3. Evolution of architecture
    - An Evolutionary Approach for Multi-objective Software Architecture Refactoring
    - Interactive and Guided Architectural Refactoring with Search-Based Recommendation
    - On The Use of Many Quality Attributes for Software Refactoring
    - Recommending Refactorings to Reverse Software Architecture Erosion
    - Architectural Refactoring for the Cloud
-}

import IMP

{- -- simple(?) API update
  def times(x, y, z, res) {
    if (y == 0) {
      res = z + x
    } else {
      v = y - 1
      w = z + x
      times(x, v, w, res)
    }
  }

  def main() {
    x = 2
    y = 3
    z = x
    res = 0
    times(x, y, z, res)
  }
-}
eg0Bfe :: DExp
eg0Bfe = undefined

{-
  def mul(x, y, r) {
    res = (x * y)
  }

  def main() {
    x = 2
    y = 3
    res = 0
    mul(x, y, res)
  }
-}
eg0Aft :: DExp
eg0Aft = mul main where
  mul = DCons "mul" ["x","y","res"] (Assign "res" (Mul (VarA "x") (VarA "y")))
  main = DMain
       $ Seq (Assign "x" (Num 2))
       $ Seq (Assign "y" (Num 3))
       $ Seq (Assign "res" (Num 0))
       $ Call "mul" ["x","y","z"]

