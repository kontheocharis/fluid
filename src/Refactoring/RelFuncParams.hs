module Refactoring.RelFuncParams (RelFuncArgs (..), relFuncParams) where

import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    Item (..),
    Pat (..),
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    appToList,
    genTerm,
    listToApp,
    listToPiType,
    piTypeToList,
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, RefactState, freshVar, lookupExprArg, lookupIdxListArg, lookupNameArg)
import Interface.Pretty (Print (printVal))


-- Arguments to the refactoring.
data RelFuncArgs = RelFuncArgs
  { -- | The name of the function whose params are to be related
    relFuncParamsFuncName :: String,
    -- | The indices of the params to relate
    relFuncParamsIndsPos :: [Int],
    -- | The term to to relate them
    relFuncParamsNewTerm :: Term
  }

instance FromRefactorArgs RelFuncArgs where
  fromRefactorArgs args =
    RelFuncArgs
      <$> lookupNameArg "func" args
      <*> lookupIdxListArg "inds" args
      <*> lookupExprArg "reln" args

-- like piTypeToList, but as a (var,type) list, so it's easier to work with
piTypeToListWithDummy :: Type -> [(Var, Type)]
piTypeToListWithDummy ty =
  let (tys, rTy) = piTypeToList ty
   in tys ++ [(Var "DummyVar" 0, rTy)]

-- like listToPiType, but as a (var,type) list, so it's easier to work with
listWithDummyToPiType :: ([(Var, Type)]) -> Type
listWithDummyToPiType l =
  listToPiType (take ((length l) - 1) l, snd (last l))

-- insert into a list after given index
insertAfter :: [a] -> Int -> a -> [a]
insertAfter varTyList i varTy =
  let (l, r) = splitAt (i + 1) varTyList
   in l ++ (varTy : r)

-- check if App term is given data
isAppData :: String -> Term -> Bool
isAppData dName ty =
  let appList = appToList ty
   in termValue (fst appList) == Global dName

-- check that function has a type (given as string name) as a param
funcHasTyAsParam :: DeclItem -> String -> Bool
funcHasTyAsParam decl dName =
  let (tyList, retTy) = piTypeToList (declTy decl)
   in any (isAppData dName) ((retTy) : (map (\t -> (snd t)) tyList))

removeSpaces :: String -> String
removeSpaces = filter (\c -> (c /= ' ' && c /= '?'))

-- relating params of constructor refactoring
relFuncParams :: RelFuncArgs -> Program -> Refact Program
relFuncParams args (Program items) =
  let indToAddTo = getIndToAddTo (Program items)
      newP = relFuncParams_prog indToAddTo (Program items)
      usecaseUpdate = updateUsecase indToAddTo newP
   in return $ usecaseUpdate
  where
    -- get the ind to add the new param to
    -- TODO: things could be so much easier if I count param from left.....
    getIndToAddTo :: Program -> Int
    getIndToAddTo (Program items0) =
      foldr
        ( \item acc -> case item of
            Decl d ->
              if declName d == relFuncParamsFuncName args
                then
                  let tys = piTypeToListWithDummy (declTy d)
                      inds = map (\i -> (length tys) - i - 1) (relFuncParamsIndsPos args)
                   in maximum inds
                else maximum [0, acc]
            _ -> maximum [0, acc]
        )
        0
        items0
    -- actual refactoring
    relFuncParams_prog :: Int -> Program -> Program
    relFuncParams_prog i (Program items1) =
      Program
        ( map
            ( \item -> case item of
                Decl d ->
                  if declName d == relFuncParamsFuncName args
                    then Decl (relFuncParams_func i d)
                    else Decl d
                _ -> item
            )
            items1
        )
    -- refactor function to add param
    relFuncParams_func :: Int -> DeclItem -> DeclItem
    relFuncParams_func i d =
      let tys = piTypeToListWithDummy (declTy d)
          inds = map (\i -> (length tys) - i - 1) (relFuncParamsIndsPos args)
          varsToRelate = foldr (\x acc -> (fst (tys !! x) : acc)) [] inds
          newVarTy = makeRelationParam varsToRelate
          inserted = insertAfter tys i newVarTy
       in d
            { declTy = listWithDummyToPiType inserted, -- update signature
              declClauses = map (relFuncParams_cl i) (declClauses d) -- update clauses
              -- get var,type for the new relation param
            }

    makeRelationParam :: [Var] -> (Var, Type)
    makeRelationParam vars =
      let termList = map (\v -> genTerm (V v)) vars
       in (Var "relParamV_func" 0, listToApp (relFuncParamsNewTerm args, termList)) -- todo: get fresh var
      -- update clauses to add new pattern variables or holes in recursive calls
    relFuncParams_cl :: Int -> Clause -> Clause
    relFuncParams_cl i (Clause lhsPats rhsTerm l) =
      Clause (insertAfter lhsPats i (genTerm (V (Var "relParam_patV" 0)))) (relFuncParams_clRhs i rhsTerm) l
    relFuncParams_cl i (ImpossibleClause lhsPats l) =
      ImpossibleClause (insertAfter lhsPats i (genTerm (V (Var "relParam_patV" 0)))) l
    -- add holes in all function calls
    relFuncParams_clRhs :: Int -> Term -> Term
    relFuncParams_clRhs i (Term (Case caseTerm patTermList) _) =
      genTerm (Case (relFuncParams_clRhs i caseTerm) (map (\pt -> ((fst pt), relFuncParams_clRhs i (snd pt))) patTermList))
    relFuncParams_clRhs i (Term (App term1 term2) termDat) =
      let (outerTerm, argList) = appToList (Term (App term1 term2) termDat)
       in if termValue outerTerm == Global (relFuncParamsFuncName args)
            then
              let holeInserted = insertAfter argList i (genTerm (Hole (Var ("vrel_" ++ (removeSpaces (printVal (argList!!(i+1)))) ++(show i)) 0))) -- todo: need fresh vars
               in listToApp (outerTerm, holeInserted)
            else Term (App (relFuncParams_clRhs i term1) (relFuncParams_clRhs i term2)) termDat
    -- todo: recurse down other patterns
    relFuncParams_clRhs i term = term
    -- update usecase of f in other places
    updateUsecase :: Int -> Program -> Program
    updateUsecase i (Program items2) =
      Program
        ( map
            ( \item -> case item of
                Decl d ->
                  if declName d == relFuncParamsFuncName args                
                  then item
                  else Decl
                    d
                      { declClauses =
                          map
                            ( \cl -> case cl of
                                ImpossibleClause pat l -> ImpossibleClause pat l
                                Clause pat term l -> Clause pat (relFuncParams_clRhs i term) l
                            )
                            (declClauses d)
                      }
                _ -> item
            )
            items2
        )

-- stack run -- -r examples/testRelFuncParams.fluid -n rel-func-params -a 'func=f, inds=[1,2], reln =`Elem`'
