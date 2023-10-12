module RefacChgParam where

import Utils

import REPL

import Syntax
import Syntax2 
import Eval
import Typecheck
import TypeCheck2 
-- import LambdaPi.Quote
import Parser
import Pretty

import Text.PrettyPrint.HughesPJ hiding (parens)

findDef :: String -> [Stmt TermInf TermChk] -> Stmt TermInf TermChk
findDef name [] = error "Cannot find definition."
findDef name (Let s a : stmts) 
    | name == s = Let s a 
    | otherwise = findDef name stmts
findDef name (s : stmts) = findDef name stmts

typeCheckDef :: ([(Name, Value)], Context) -> Stmt TermInf TermChk -> Result TermInf2 
typeCheckDef env (Let s a) = do
      t <- typeInf02 env a
      return t

-- (Ann (Lam (Lam (Lam (Lam (Inf (((((Free (Global "listElim") :@: Inf (Bound 3)) :@: Lam (Inf (Free (Global "List") :@: Inf (Bound 3)))) :@: Inf (Free (Global "LNil") :@: Inf (Bound 2))) :@: Lam (Lam (Lam (Inf (((Free (Global "LCons") :@: Inf (Bound 5)) :@: Inf (Bound 4 :@: Inf (Bound 2))) :@: Inf (Bound 0)))))) :@: Inf (Bound 0)))))))

countArguments :: Int -> TermChk2 -> Int
countArguments p (LamT x ty) = countArguments (p+1) x 
countArguments p _ = p


-- rewrite vars compensates for a new bound variable added...
-- all references to bound variables at the top level are incremented by 1...
-- only those on the left side of the introduced lambda are increased
rewriteVarsInf :: Int -> TermInf2 -> TermInf2
rewriteVarsInf offset (AnnT t1 t2 ty) = AnnT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsInf offset (StarT ty) = StarT ty
rewriteVarsInf offset (PiT t1 t2 ty) = PiT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsInf offset (SigmaT t1 t2 ty) = SigmaT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsInf offset (BoundT s x ty) 
 | x >= offset = (BoundT s (x+1) ty)
 | otherwise   = BoundT s x ty
rewriteVarsInf offset (FreeT s n ty) = FreeT s n ty
rewriteVarsInf offset (AppRedT ti tc ty) = AppRedT (rewriteVarsInf offset ti) (rewriteVarsChk offset tc) ty
rewriteVarsInf offset (AppT t1 t2 ty) = AppT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsInf offset (PairT t1 t2 t3 t4 ty) = PairT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) ty
rewriteVarsInf offset (NatT ty) = NatT ty
rewriteVarsInf offset (NatElimT t1 t2 t3 t4 ty) = NatElimT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) ty
rewriteVarsInf offset (VecT t1 t2 ty) = VecT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsInf offset (VecElimT t1 t2 t3 t4 t5 t6 ty) = VecElimT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) (rewriteVarsChk offset t6) ty
rewriteVarsInf offset (ListT t1 ty) = ListT (rewriteVarsChk offset t1) ty
rewriteVarsInf offset (ListElimT t1 t2 t3 t4 t5 ty) = ListElimT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) ty
rewriteVarsInf offset (FinT t1 ty) = FinT (rewriteVarsChk offset t1) ty
rewriteVarsInf offset (FinElimT t1 t2 t3 t4 t5 ty) = FinElimT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) ty
rewriteVarsInf offset (EqT t1 t2 t3 ty) = EqT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) ty
rewriteVarsInf offset (EqElimT t1 t2 t3 t4 t5 t6 ty) = EqElimT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) (rewriteVarsChk offset t6) ty
rewriteVarsInf offset (SigElimT t1 t2 t3 t4 t5 ty) = SigElimT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) ty
rewriteVarsInf offset (TMaybeT t1 ty) = TMaybeT (rewriteVarsChk offset t1) ty
rewriteVarsInf offset (LTET t1 t2 ty) = LTET (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsInf offset (LTEElimT t1 t2 t3 t4 t5 t6 ty) = LTEElimT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) (rewriteVarsChk offset t6) ty


{-
data TermChk =         
   Inf TermInf          -- CHK
 | Lam TermChk          -- LAM
 | Zero
 | Succ TermChk 
 | Nil TermChk
 | Cons TermChk TermChk TermChk TermChk
 | LNil TermChk         -- List Nil
 | LCons TermChk TermChk TermChk -- List Cons
 | VecToList TermChk TermChk TermChk
 | FZero TermChk
 | FSucc TermChk TermChk
 | Refl TermChk TermChk
 | TNothing TermChk
 | TJust TermChk TermChk
 | LTEZero TermChk 
 | LTESucc TermChk TermChk TermChk
-}

rewriteVarsChk :: Int -> TermChk2 -> TermChk2
rewriteVarsChk offset (InfT t1 ty) = InfT (rewriteVarsInf offset t1) ty
rewriteVarsChk offset (LamT t1 ty) = LamT (rewriteVarsChk offset t1) ty-- we need to increment the number of binds ...
rewriteVarsChk offset (ZeroT ty) = ZeroT ty
rewriteVarsChk offset (SuccT t1 ty) = SuccT (rewriteVarsChk offset t1) ty
rewriteVarsChk offset (NilT t1 ty) = NilT (rewriteVarsChk offset t1) ty
rewriteVarsChk offset (ConsT t1 t2 t3 t4 ty) = ConsT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) ty
rewriteVarsChk offset (LNilT t1 ty) = LNilT (rewriteVarsChk offset t1) ty
rewriteVarsChk offset (LConsT t1 t2 t3 ty) = LConsT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) ty
rewriteVarsChk offset (VecToListT t1 t2 t3 ty) = VecToListT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) ty
rewriteVarsChk offset (FZeroT t1 ty) = FZeroT (rewriteVarsChk offset t1) ty
rewriteVarsChk offset (FSuccT t1 t2 ty) = FSuccT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsChk offset (ReflT t1 t2 ty) = ReflT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsChk offset (TNothingT t1 ty) = TNothingT (rewriteVarsChk offset t1) ty
rewriteVarsChk offset (TJustT t1 t2 ty) = TJustT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) ty
rewriteVarsChk offset (LTEZeroT t1 ty) = LTEZeroT (rewriteVarsChk offset t1) ty
rewriteVarsChk offset (LTESuccT t1 t2 t3 ty) = LTESuccT (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) ty


refacListArg :: Int -> TermChk2 -> TermChk2
refacListArg pos (InfT (AppRedT (FreeT s1 (Global l) ty0) (InfT (FreeT s2 p ty3) ty1) ty2) ty4) 
  | l == "List" = InfT (AppRedT (AppRedT (FreeT s1 (Global "Vec") VStar) (InfT (FreeT s2 p ty3) ty1) VStar) (InfT (BoundT defaultPos pos VStar) VStar) VStar) VStar
refacListArg pos x = error $ renderChk x

{-
(InfT (AppRedT (FreeT "append.lp" (line 47, column 91) (Global "List") _  )
               (InfT (FreeT "unknown location" (line 0, column 0)(Local 1) _) _) _) _)
-}

refacBodyInf :: Int -> Int -> Int -> TermInf2 -> TermInf2
-- refacBodyInf tot pos lamPos ((((FreeT s1 (Global le) ty0 :@: p1 :@: p2) :@: p3) :@: p4) :@: InfT (BoundT s2 p ty4) ty1)

refacBodyInf tot pos lamPos (AppRedT (AppRedT (AppRedT (AppRedT (AppRedT (FreeT s1 (Global le) _) p1 _) p2 _) p3 _) p4 _) (InfT (BoundT s2 p ty4) ty1) _)
  | le == "listElim" && p == (tot-pos) = {-(((Free s1 (Global "vecElim") 
                                         :@: p1 
                                         :@: (Lam (rewriteVarsChk (countArguments 1 p2) p2))) 
                                         :@: p3) 
                                         :@: (Lam (rewriteVarsChk (countArguments 1 p4) p4))) 
                                         :@: Inf (Bound defaultPos tot) 
                                         :@: Inf (Bound s2 (tot-pos))-}
                                        AppRedT (AppRedT (AppRedT (AppRedT (AppRedT (AppRedT (FreeT s1 (Global "vecElim") VStar) p1 VStar) (LamT (rewriteVarsChk (countArguments 1 p2) p2) VStar) VStar) p3 VStar) (LamT (rewriteVarsChk (countArguments 1 p4) p4) VStar) VStar) (InfT (BoundT defaultPos tot VStar) VStar) VStar) (InfT (BoundT defaultPos (tot-pos) VStar) VStar) VStar

refacBodyInf tot pos lamPos (AppRedT t1 t2 ty) = AppRedT (refacBodyInf tot pos lamPos t1) (refacBodyChk tot pos lamPos t2) ty
refacBodyInf tot pos lamPos t@(BoundT s p ty)
  | p == (tot-lamPos) = AppRedT (AppRedT (AppRedT (FreeT defaultPos (Global "vectToList") VStar) 
                                                  (InfT (BoundT defaultPos tot VStar ) VStar) VStar) 
                                         (InfT (BoundT defaultPos tot VStar) VStar) VStar) 
                                (InfT (BoundT s (tot-pos) VStar) VStar) VStar
-- error (show t)
refacBodyInf tot pos lamPos t = t 

refacBodyChk :: Int -> Int -> Int -> TermChk2 -> TermChk2
refacBodyChk tot pos lamPos (LamT x ty)  
   = LamT (refacBodyChk tot pos (lamPos+1) x) ty
refacBodyChk tot pos lamPos (InfT ti ty) = InfT (refacBodyInf tot pos lamPos ti) ty
refacBodyChk _ _ _ y = y

refacPi :: Int -> Int -> TermChk2 -> TermChk2
refacPi 1 pos2 (InfT (PiT arg bod ty1) ty0) = InfT (PiT (refacListArg (pos2-1) arg) bod ty1) ty0
refacPi pos pos2 (InfT (PiT arg bod ty1) ty0) = InfT (PiT arg (refacPi (pos-1) pos2 bod) ty1) ty0
refacPi _ _ t = t

refacSig :: TermInf2 -> Int -> TermInf2
refacSig (AnnT t pi ty) p = AnnT (LamT (refacBodyChk (countArguments 0 t) p 0 t) VStar) (InfT (PiT (InfT (FreeT defaultPos (Global "Nat") VStar) VStar) (refacPi p p pi) VStar) VStar) ty
refacSig _ _ = error "refactoring eror in refacSig"

refacChgParam :: String -> String -> Int -> IO ()
refacChgParam file name pos = do
    (stmts, (x,y,z)) <- typecheckandParse file
   -- putStrLn $ concatMap showNameValue y
   -- putStrLn $ renderStmts stmts
    let term = findDef name stmts 
    putStrLn $ show term

    case typeCheckDef (lpve,lpte) term of 
      Left s -> error s 
      Right term' -> 
         do putStrLn $ show term
            let term'' = refacSig term' pos 
            putStrLn $ ">>> " ++ (render $ iPrint_ 0 0 (termInf2ToTermInf term'')) ++ " <<<< "
