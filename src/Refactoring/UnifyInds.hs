module Refactoring.UnifyInds (unifyInds) where

import Checking.Typechecking (checkTerm)
import Data.List (partition)
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    GlobalName,
    Item (..),
    Pat,
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    listToPiType,
    piTypeToList,
    termDataAt,
    termLoc,
    genTerm
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupIdxListArg, lookupNameArg)


---------------------------------------------------

-- change nested App term to (reversed) list
appTermToList :: Term -> [Term]
appTermToList (Term (App t1 t2) termDat) = t2 : (appTermToList t1)
appTermToList term = [term]

-- change list to App term
listToAppTerm :: [Term] -> Term
listToAppTerm [term] = term
listToAppTerm (term : terms) =
  let recRes = listToAppTerm terms
   in Term (App recRes term) (termDataAt (termLoc recRes <> termLoc term))

-- TODO: add vars name if wildcards are used - need to work in monad to generate fresh vars - ignore for now
removeWildcards :: [Term] -> [Term]
removeWildcards termList = termList

-- Arguments to the unify indices refactoring.
data UnifyIndsArgs = UnifyIndsArgs
  { -- | The name of the data type of the constructor
    unifyIndsDataName :: String,
    -- | The name of the constructor whose indices are to be unified
    unifyIndsCtorName :: String,
    -- | The positions of the indices to be unified to the index above
    unifyIndsPositions :: [Int]
  }

instance FromRefactorArgs UnifyIndsArgs where
  fromRefactorArgs args =
    UnifyIndsArgs
      <$> lookupNameArg "data" args
      <*> lookupNameArg "ctor" args
      <*> lookupIdxListArg "indsToUnify" args

-- | Specialise a constructor at a given index to a given term.
unifyInds :: UnifyIndsArgs -> Program -> Refact Program
unifyInds args ast =
  let dataRefactored = changeConstr_ast ast -- change data definition
      usecaseUpdated = updateUsecase dataRefactored -- update use case of changed constructor
   in return usecaseUpdated
  where
    -- refactor the program
    -- recurse to the data type declaration
    changeConstr_ast :: Program -> Program
    changeConstr_ast (Program itemL) =
      Program
        ( map
            ( \item ->
                case item of
                  (Decl decl) -> Decl decl
                  (Data dat) ->
                    if dataName dat == (unifyIndsDataName args)
                      then Data (changeConstr_data dat)
                      else Data dat
            )
            itemL
        )
    -- refactor the data
    -- recurse to the constructor
    changeConstr_data :: DataItem -> DataItem
    changeConstr_data (DataItem dname dty dConstrs) =
      DataItem
        dname
        dty
        ( map
            ( \constr ->
                if ctorItemName constr == (unifyIndsCtorName args)
                  then changeConstr_constr constr
                  else constr
            )
            dConstrs
        )
    -- refactor the constructor
    -- recurse to the constructor params and return type
    changeConstr_constr :: CtorItem -> CtorItem
    changeConstr_constr (CtorItem itemName ty dataName) =
      case piTypeToList ty of
        (argList, retTy) ->
          let l = length argList
              indPosnsRev = map (\i -> l - i) (unifyIndsPositions args)
           in if all (\x -> x < l) indPosnsRev -- indices positions valid
                then
                  let refactoredArgList = changeConstr_argsList argList indPosnsRev -- refactor indices
                      refactoredRetType = changeConstr_retTy argList indPosnsRev retTy -- refactor return type
                   in (CtorItem itemName (listToPiType (refactoredArgList, refactoredRetType)) dataName)
                else -- some indices out of bounds
                  (CtorItem itemName ty dataName)
    -- refactor the parameters of constructor
    -- remove redundant params
    changeConstr_argsList :: [(Var, Type)] -> [Int] -> [(Var, Type)]
    changeConstr_argsList argList [] = argList
    changeConstr_argsList argList (i : indPosns) =
      case argList !! i of
        (var, ty) ->
              let oldVars = [fst (argList !! j) | j <- indPosns]
                  reducedArgs = [argList !! j | j <- [0 .. (length argList) - 1], not (elem j indPosns)] -- remove redundant vars
               in map (\vt -> (fst vt, replaceOldVar_type oldVars var (snd vt))) reducedArgs
    -- rename the use of deleted vars in a type
    replaceOldVar_type :: [Var] -> Var -> Type -> Type
    replaceOldVar_type oldVars newVar (Term (App t1 t2) termDat) =
      Term (App (replaceOldVar_type oldVars newVar t1) (replaceOldVar_type oldVars newVar t2)) termDat
    replaceOldVar_type oldVars newVar (Term (V var) termDat) =
      if elem var oldVars
        then Term (V newVar) termDat
        else Term (V var) termDat
    replaceOldVar_type oldVars newVar ty = ty
    -- refactor the return type of the constructor
    -- rename unused var names with the unified one
    changeConstr_retTy :: [(Var, Type)] -> [Int] -> Type -> Type
    changeConstr_retTy argList [] retTy = retTy
    changeConstr_retTy argList (i : indPosns) retTy =
      case argList !! i of
        (var, ty) ->
          let oldVars = [fst (argList !! j) | j <- indPosns]
           in replaceOldVar_type oldVars var retTy
    ----------
    -- update use cases
    updateUsecase :: Program -> Program
    updateUsecase (Program itemL) =
      Program
        ( map
            ( \item ->
                case item of
                  (Decl decl) -> Decl (decl {declClauses = (map (updateUsecase_cl) (declClauses decl))})
                  -- only look at uses of constructors in clauses (if used in declaration, should propagate from update use case in data items)
                  (Data dat) -> item -- TODO: not yet implemented - update use case in other data type
            )
            itemL
        )
    -- update use cases in function equation
    -- update constructor arguments and rename use of deleted variables
    updateUsecase_cl :: Clause -> Clause
    updateUsecase_cl (Clause pats term) =
      let (patRes, varsToRename) = updateUsecase_pats pats
          newClause = Clause (patRes) (updateUsecase_eqnrhs (unifyIndsPositions args) term) -- constructor updated to remove indices
       in renameVars varsToRename newClause -- rename uses of removed vars
    updateUsecase_cl (ImpossibleClause pats) =
      let patRes = updateUsecase_pats pats
       in ImpossibleClause (fst patRes)
    -- refactor use of constructor in lhs of a equation
    updateUsecase_pats :: [Pat] -> ([Pat], [Term])
    updateUsecase_pats [] = ([], [])
    updateUsecase_pats (pat : pats) =
      let (patRes, varsToRename1) = updateUsecase_pat (unifyIndsPositions args) pat
          (patsRec, varsToRename2) = updateUsecase_pats pats
       in (patRes : patsRec, varsToRename1 ++ varsToRename2)
    -- refactor use of constructor in a pattern variable
    -- removes unified parameters
    -- [term] to remmeber what vars were deleted and rename all uses of the these vars in the clause
    -- rename all other vars in term by the name of the first element
    updateUsecase_pat :: [Int] -> Pat -> (Pat, [Term])
    updateUsecase_pat [] (Term (App t1 t2) termDat) = ((Term (App t1 t2) termDat), [])
    updateUsecase_pat (ind : inds) (Term (App t1 t2) termDat) =
      let termList = removeWildcards (appTermToList (Term (App t1 t2) termDat)) -- change wildcards to named vars
       in case last termList of
            Term (Global varName) tD ->
              if varName == (unifyIndsCtorName args)
                then
                  let (toKeep, toRemove) = partition (\j -> not (elem (j + 1) inds)) [0 .. (length termList) - 1]
                   in (listToAppTerm [termList !! j | j <- toKeep], (termList !! (ind - 1)) : [termList !! j | j <- toRemove])
                else (Term (App t1 t2) termDat, [])
    updateUsecase_pat indPosns term = (term, [])
    -- update the use of refactored constructor, when it occurs in the rhs of equations
    -- if constructor in rhs, we remove the I\I1 indices, and make the I1 index a hole
    updateUsecase_eqnrhs :: [Int] -> Term -> Term
    updateUsecase_eqnrhs [] term = term
    updateUsecase_eqnrhs (ind : inds) (Term (Pair t1 t2) termDat) =
      Term (Pair (updateUsecase_eqnrhs (ind : inds) t1) (updateUsecase_eqnrhs (ind : inds) t2)) termDat
    updateUsecase_eqnrhs (ind : inds) (Term (Lam lvar t2) termDat) =
      Term (Lam lvar (updateUsecase_eqnrhs (ind : inds) t2)) termDat
    updateUsecase_eqnrhs (ind : inds) (Term (Case caseTerm ptList) termDat) =
      (Term (Case (updateUsecase_eqnrhs (ind : inds) caseTerm) (map (updateUsecase_patTerm (ind : inds)) ptList)) termDat)
    updateUsecase_eqnrhs (ind : inds) (Term (App t1 t2) termDat) =
      let termList = appTermToList (Term (App t1 t2) termDat)
       in case last termList of
            Term (Global varName) _ ->
              if varName == (unifyIndsCtorName args)
                then
                  let holedConstr = updateUsecase_constrTerm termList (ind : inds)
                   in listToAppTerm [holedConstr !! j | j <- [0 .. (length holedConstr) - 1], not (elem (j + 1) inds)]
                else Term (App t1 t2) termDat
    -- TODO: possible recurse down other constructor type (but since we're removing them, I'm ignoring them for now)
    updateUsecase_eqnrhs indPosns term = term
    -- like in clauses, but for handling case expressions
    updateUsecase_patTerm :: [Int] -> (Pat, Term) -> (Pat, Term)
    updateUsecase_patTerm indPosns (pat, term) =
      let (patRes, varsToRename) = updateUsecase_pats [pat]
          newrhs = updateUsecase_eqnrhs indPosns term -- constructor updated to remove indices
          varsToRenameTV = map (\term -> case term of (Term tv _) -> tv) varsToRename
       in case varsToRename of
            [] -> (patRes !! 0, newrhs)
            (newVar : varsToRename) -> (patRes !! 0, renameVars_term newVar varsToRenameTV newrhs)
    -- update the arguments to constructor
    -- fill with holes
    updateUsecase_constrTerm :: [Term] -> [Int] -> [Term]
    updateUsecase_constrTerm termList indPosns =
      map
        ( \i ->
            if elem (i + 1) indPosns
              then case termList !! i of
                Term (V (Var str int)) td -> Term (Hole (Var (str ++ "_" ++ show i) int)) td -- hole name [oldname]_[position]
                term -> term
              else termList !! i
        )
        [0 .. ((length termList) - 1)]
    -- rename the use of deleted vars in an equation
    -- rename vars in term\term[0] in clause to var name in term[0]
    renameVars :: [Term] -> Clause -> Clause
    renameVars [] clause = clause
    renameVars (newVar : varsToRename) (Clause pats term) =
      let varsToRenameTV = (map (\term -> case term of (Term tv _) -> tv) varsToRename)
       in Clause (renameVars_pats newVar varsToRename pats) (renameVars_term newVar varsToRenameTV term)
    renameVars (newVar : varsToRename) (ImpossibleClause pats) =
      ImpossibleClause (renameVars_pats newVar varsToRename pats)
    -- rename vars in lhs of equations
    renameVars_pats :: Term -> [Term] -> [Pat] -> [Pat]
    renameVars_pats newVar varsToRename = map (renameVars_pat newVar varsToRename)
    -- rename vars in a pattern
    renameVars_pat :: Term -> [Term] -> Pat -> Pat
    renameVars_pat newVar varsToRename pat =
      let varsToRenameTV = (map (\term -> case term of (Term tv _) -> tv) varsToRename)
       in renameVars_term newVar varsToRenameTV pat
    -- rename vars in rhs of equations
    renameVars_term :: Term -> [TermValue] -> Term -> Term
    renameVars_term newVar varsToRename (Term (App term1 term2) termDat) =
      Term (App (renameVars_term newVar varsToRename term1) (renameVars_term newVar varsToRename term2)) termDat
    renameVars_term newVar varsToRename (Term (Pair term1 term2) termDat) =
      Term (Pair (renameVars_term newVar varsToRename term1) (renameVars_term newVar varsToRename term2)) termDat
    renameVars_term newVar varsToRename (Term (Lam lvar term2) termDat) =
      Term (Lam lvar (renameVars_term newVar varsToRename term2)) termDat
    renameVars_term newVar varsToRename (Term (Case cTerm ptList) termDat) =
      Term (Case (renameVars_term newVar varsToRename cTerm) (map (\pt -> (fst pt, (renameVars_term newVar varsToRename (snd pt)))) ptList)) termDat
    renameVars_term newVar varsToRename (Term (V var) termDat) =
      if elem (V var) varsToRename
        then newVar
        else Term (V var) termDat
    renameVars_term _ _ term = term

-- stack run -- -r examples/testUnifyInds.fluid -n unify-inds -a 'data=Data2, ctor=C21, indsToUnify=[4, 3]'
-- stack run -- -r examples/example1filledHoles.fluid -n unify-inds -a 'data=Expr, ctor=Add, indsToUnify=[5,3,1]'