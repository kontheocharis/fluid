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
    if (y <= 0) {
      res = z
    } else {
      v = y - 1
      w = z + x
      times(x, v, w, res)
    }
  }

  def main() {
    x = 2
    y = 3
    z = 0
    res = 0
    times(x, y, z, res)
  }
-}
eg0Bfe :: DExp
eg0Bfe = times main where
  times = DCons "times" ["x", "y", "z", "res"] body where
    body = If (LTE (VarA "y") (Num 0)) tt ff
    tt = Seq (Assign "randBase" (Num 42))
       $ Assign "res" (VarA "z")
    ff = Seq (Assign "v" (Sub (VarA "y") (Num 1)))  
       $ Seq (Assign "w" (Add (VarA "z") (VarA "x")))
       $ Seq (Assign "rand" (Num 42))
       $ Call "times" ["x", "v", "w", "res"]
  main = DMain
       $ Seq (Assign "x" (Num 2))
       $ Seq (Assign "y" (Num 3))
       $ Seq (Assign "z" (Num 0))
       $ Seq (Assign "res" (Num 0))
       $ Call "times" ["x", "y", "z", "res"]

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
       $ Call "mul" ["x","y","res"]

{-
  In order to demonstrate that eg0Bfe == eg1Aft, we need:
  1. to demonstrate that forall x,y,z . mul(x,y,z) = times(x,y,0,z)
  2. to demonstrate that z can be safely removed

  For 2, this is simple: an assignment followed by no occurrences means it's
  equivalent to no assignment
  > seq (assign x v) k -> k when x \not\in k

  For 1, this is not so simple...

-}

-------------------------------------------------------------------------------

-- To test for correct treatment of a the state following a procedure call
eg1 :: DExp
eg1 = mul main where
  mul = DCons "mul" ["x","y","res"] body where
    body = Seq (Assign "local" (VarA "x"))
         $ Assign "res" (Mul (VarA "x") (VarA "y"))
  main = DMain
       $ Seq (Assign "x" (Num 2))
       $ Seq (Assign "y" (Num 3))
       $ Seq (Assign "res" (Num 0))
       -- {x:2, y:3, res:0}
       $ Seq (Call "mul" ["x", "y", "res"])
       -- {x:2, y:3, res:6}
       $ Seq (Assign "z" (Num 2))
       -- {x:2, y:3, res:6, z:2}
       $ Call "mul" ["res", "z", "res"]
       -- {x:2, y:3, res:12, z:2}
