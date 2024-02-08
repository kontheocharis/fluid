module Refactoring.RemoveMaybe (removeMaybe) where

import Lang
  ( Clause (..),
    DeclItem (..),
    Item (..),
    Pat,
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    appToList,
    genTerm,
    listToPiType,
    piTypeToList,
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupNameArg)

data RemMaybeArgs = RemMaybeArgs
  { -- | The name of the function that has Maybe as return type
    removeMaybeFuncName :: String
  }

instance FromRefactorArgs RemMaybeArgs where
  fromRefactorArgs args =
    RemMaybeArgs
      <$> lookupNameArg "func" args

removeMaybe :: RemMaybeArgs -> Program -> Refact Program
removeMaybe args (Program itemL) =
  let newP =
        ( Program
            ( map
                ( \item ->
                    case item of
                      (Decl decl) ->
                        if (declName decl) == (removeMaybeFuncName args)
                          then Decl (removeMaybe_func decl)
                          else Decl decl
                      (Data dat) -> Data dat
                )
                itemL
            )
        )
   in return (updateUsecase newP)
  where
    -- refactor function
    removeMaybe_func :: DeclItem -> DeclItem
    removeMaybe_func decl =
      let (inpTys, resTy) = piTypeToList (declTy decl)
       in case resTy of -- check return type is a Maybe
            Term (MaybeT ty) termDat ->
              if onlyJust decl
                then DeclItem (declName decl) (removeMaybe_sig (declTy decl)) (removeJust_cls (declClauses decl)) (declLoc decl)
                else decl
            otherTy -> decl
    -- check if the rhs of equations do not have Nothing
    -- TODO: need to rethink if we allow Maybe type elsewhere
    onlyJust :: DeclItem -> Bool
    onlyJust decl =
      all
        ( \cl -> case cl of
            (ImpossibleClause pats _) -> True
            (Clause pats term _) -> onlyJust_term term
        )
        (declClauses decl)
    -- check if term do not have Nothing
    onlyJust_term :: Term -> Bool
    onlyJust_term (Term (App term1 term2) termDat) = (onlyJust_term term1) && (onlyJust_term term2)
    onlyJust_term (Term (Lam var term2) termDat) = (onlyJust_term term2)
    onlyJust_term (Term (Pair term1 term2) termDat) = (onlyJust_term term1) && (onlyJust_term term2)
    onlyJust_term (Term (MJust term) termDat) = (onlyJust_term term)
    onlyJust_term (Term (Case cterm ptList) termDat) =
      if isRecursionCall cterm
        then
          let justClauseNum = isSplittingOnJustNothing ptList
           in if justClauseNum > -1
                then onlyJust_term (snd (ptList !! justClauseNum))
                else all (\pair -> onlyJust_term (snd pair)) ptList -- no, need to ignore the Nothing case...
        else all (\pair -> onlyJust_term (snd pair)) ptList
    onlyJust_term (Term MNothing termDat) = False
    onlyJust_term term = True
    -- check if term is a recursive call
    isRecursionCall :: Term -> Bool
    isRecursionCall (Term (App t1 t2) termDat) =
      case termValue (fst (appToList (Term (App t1 t2) termDat))) of
        Global str -> str == removeMaybeFuncName args
        _ -> False
    isRecursionCall term = False
    -- check if case term splits purely on Just and Nothing
    isSplittingOnJustNothing :: [(Pat, Term)] -> Int
    isSplittingOnJustNothing ptList =
      case termValue (fst (ptList !! 0)) of
        MJust x ->
          if termValue (fst (ptList !! 1)) == MNothing
            then 0
            else -1
        MNothing -> case termValue (fst (ptList !! 1)) of
          MJust x -> 1
          _ -> -1
    -- remove Maybe from the return type
    removeMaybe_sig :: Type -> Type
    removeMaybe_sig ty =
      let (inpTy, resTy) = piTypeToList ty
       in case resTy of
            Term (MaybeT ty) _ -> listToPiType (inpTy, ty)
            ty -> listToPiType (inpTy, resTy)
    -- remove Just in the equations
    removeJust_cls :: [Clause] -> [Clause]
    removeJust_cls cls =
      map
        ( \cl -> case cl of
            (ImpossibleClause pats l) -> ImpossibleClause pats l
            (Clause pats term l) -> Clause pats (removeJust_term term) l
        )
        cls
    -- remove Just in a term
    -- recursions in rhs are left alone
    -- UNLESS recursion is used in case expressions: then we wrap Just around the call
    removeJust_term :: Term -> Term
    removeJust_term (Term (Case cterm ptList) termDat) =
      if isRecursionCall cterm
        then
          let (justPat, justRes) = ptList !! (isSplittingOnJustNothing ptList)
           in case termValue justPat of
                MJust x -> genTerm (Case cterm [(x, removeJust_term justRes)])
                _ -> genTerm (Case cterm (map (\pair -> ((fst pair), removeJust_term (snd pair))) ptList))
        else genTerm (Case cterm (map (\pair -> ((fst pair), removeJust_term (snd pair))) ptList))
    removeJust_term (Term (MJust term) termDat) = term
    removeJust_term term = term
    -- update use sites of f
    updateUsecase :: Program -> Program
    updateUsecase (Program items1) =
      ( Program
          ( map
              ( \item ->
                  case item of
                    (Decl decl) -> Decl (decl {declClauses = map updateUsecase_cl (declClauses decl)})
                    (Data dat) -> Data dat
              )
              items1
          )
      )
    updateUsecase_cl :: Clause -> Clause
    updateUsecase_cl (ImpossibleClause pats l) = ImpossibleClause pats l
    updateUsecase_cl (Clause pats term l) = Clause pats (updateUsecase_term term) l
    -- on rhs of equations, recurse down until we find f, then wrap in Just
    updateUsecase_term :: Term -> Term
    updateUsecase_term (Term (Lam var term2) termDat) =
      genTerm (Lam var (updateUsecase_term term2))
    updateUsecase_term (Term (Pair term1 term2) termDat) =
      genTerm (Pair (updateUsecase_term term1) (updateUsecase_term term2))
    updateUsecase_term (Term (MJust term) termDat) =
      genTerm (MJust (updateUsecase_term term))
    updateUsecase_term (Term (App term1 term2) termDat) =
      let (appHead, appOthers) = appToList (Term (App term1 term2) termDat)
       in case termValue appHead of
            Global str ->
              let recRes = genTerm (App (updateUsecase_term term1) (updateUsecase_term term2))
               in if str == removeMaybeFuncName args
                    then genTerm (MJust recRes) -- todo: in usecase of f where f is applied partially, do (\lambda x -> Just (f (..) x))
                    else recRes
            _ -> genTerm (App (updateUsecase_term term1) (updateUsecase_term term2))
    updateUsecase_term (Term (Case cterm ptList) termDat) =
      genTerm (Case (updateUsecase_term cterm) (map (\pt -> (fst pt, updateUsecase_term (snd pt))) ptList))
    updateUsecase_term term = term

-- stack run -- -r examples/testRemoveMaybe.fluid -n remove-maybe -a 'func=f'
