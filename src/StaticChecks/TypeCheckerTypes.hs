{-# LANGUAGE TupleSections #-}

module StaticChecks.TypeCheckerTypes where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M
import qualified Data.Set as S
import Grammar.AbsLatte
import Control.Monad
import StaticChecks.Errors
import StaticChecks.GrammarUtils

-- build-in functions

builtInFunctionsMap :: M.Map Ident Declaration
builtInFunctionsMap =
  M.fromList
    [ (Ident "printInt", Declaration (Fun BNFC'NoPosition tVoid [tInt]) BNFC'NoPosition),
      (Ident "printString", Declaration (Fun BNFC'NoPosition tVoid [tStr]) BNFC'NoPosition),
      (Ident "error", Declaration (Fun BNFC'NoPosition tVoid []) BNFC'NoPosition),
      (Ident "readInt", Declaration (Fun BNFC'NoPosition tInt []) BNFC'NoPosition),
      (Ident "readString", Declaration (Fun BNFC'NoPosition tStr []) BNFC'NoPosition)
    ]

builtInFunctions :: S.Set Ident
builtInFunctions = M.keysSet builtInFunctionsMap
    
-- environment

data Env = Env
  { variables :: M.Map Ident Declaration,
    variablesInBlock :: [Ident],
    expRetType :: Maybe Type,
    expItemType :: Maybe Type,
    retType :: Maybe Type,
    currClass :: Ident
  }

data Store = Store
  { functions :: M.Map Ident ClassFnDecl,
    fields :: M.Map Ident ClassFieldDecl,
    parents :: M.Map Ident Ident
  } deriving (Eq, Ord, Show, Read)

data Declaration = Declaration {tpe :: Type, position :: BNFC'Position} deriving (Eq, Ord, Show, Read)

type ClassFnDecl = M.Map Ident Declaration
type ClassFieldDecl = M.Map Ident Declaration

emptyEnv :: Env
emptyEnv = Env M.empty [] Nothing Nothing Nothing (Ident "")

emptyStore :: Store
emptyStore = Store (M.singleton (Ident "") builtInFunctionsMap) M.empty M.empty

-- TypeChecker monad

type TypeCheckerM' a = WriterT [SemanticException] (StateT Store (ReaderT Env (ExceptT SemanticError IO))) a

-- environment helpers

newBlockEnv :: TypeCheckerM' Env
newBlockEnv = do
  env <- ask
  pure env {variablesInBlock = []}

updateEnvVariables :: Ident -> Declaration -> Env -> Env
updateEnvVariables ident decl env = env {variables = M.insert ident decl (variables env)}

updateVariablesInBlock :: Ident -> Env -> Env
updateVariablesInBlock ident env = env {variablesInBlock = ident : variablesInBlock env}

addVariableToScope :: BNFC'Position -> Ident -> Type -> Env -> TypeCheckerM' Env
addVariableToScope pos ident t env
  | ident `elem` variablesInBlock env = do
    let Declaration _ firstPos = variables env M.! ident
    throwError $ RedeclarationInScope ident firstPos pos
  | otherwise = do
    _ <- checkExceptType tVoid t (VoidVariable (hasPosition t))
    let updateVariablesEnv = updateVariablesInBlock ident env
    pure $ updateEnvVariables ident (Declaration t pos) updateVariablesEnv

addVariableToLocalScope :: BNFC'Position -> Ident -> Type -> TypeCheckerM' Env
addVariableToLocalScope pos ident t = ask >>= addVariableToScope pos ident t

getVariableType :: Ident -> BNFC'Position -> TypeCheckerM' Type
getVariableType ident pos = do
  maybeType <- reader $ M.lookup ident . variables
  case maybeType of
    Nothing -> throwError $ VariableNotDefined ident pos
    Just (Declaration t _) -> pure t

updateFunctions :: Ident -> Declaration -> TypeCheckerM' ()
updateFunctions fnIdent decl = do
  cIdent <- asks currClass
  fnMap <- gets functions
  let newClassMap = M.insert fnIdent decl (fnMap M.! cIdent)
  modify $ \store -> store {functions = M.insert cIdent newClassMap fnMap}

addFunction :: BNFC'Position -> Ident -> Type -> TypeCheckerM' ()
addFunction pos fnIdent t = do
  cIdent <- asks currClass
  maybeFunc <- gets $ \store -> M.lookup fnIdent ((functions store) M.! cIdent)
  case maybeFunc of
    Nothing -> updateFunctions fnIdent (Declaration t pos)
    Just (Declaration _ BNFC'NoPosition) -> throwError $ BuiltInRedeclaration fnIdent pos
    Just (Declaration _ firstPos) -> throwError $ RedeclarationInScope fnIdent firstPos pos

getFunctionType :: Ident -> Ident -> BNFC'Position -> TypeCheckerM' Type
getFunctionType cIdent fnIdent pos = do
  maybeType <- gets $ \store -> M.lookup fnIdent ((functions store) M.! cIdent)
  case maybeType of
    Nothing -> throwError $ FunctionNotDefined fnIdent pos
    Just (Declaration t _) -> pure t

updateFields :: Ident -> Declaration -> TypeCheckerM' ()
updateFields fieldIdent decl = do
  cIdent <- asks currClass
  fieldsMap <- gets fields
  let newClassMap = M.insert fieldIdent decl (fieldsMap M.! cIdent)
  modify $ \store -> store {fields = M.insert cIdent newClassMap fieldsMap}

addField :: BNFC'Position -> Ident -> Type -> TypeCheckerM' ()
addField pos fieldIdent t = do
  cIdent <- asks currClass
  maybeField <- gets $ \store -> M.lookup fieldIdent ((fields store) M.! cIdent)
  case maybeField of
    Nothing -> updateFields fieldIdent (Declaration t pos)
    Just (Declaration _ firstPos) -> throwError $ RedeclarationInScope fieldIdent firstPos pos

getFieldType :: Ident -> Ident -> BNFC'Position -> TypeCheckerM' Type
getFieldType cIdent fieldIdent pos = do
  maybeType <- gets $ \store -> M.lookup fieldIdent ((fields store) M.! cIdent)
  case maybeType of
    Nothing -> throwError $ PropertyNotExisting fieldIdent pos
    Just (Declaration t _) -> pure t

getParentIdent :: Ident -> TypeCheckerM' (Maybe Ident)
getParentIdent cIdent = gets $ M.lookup cIdent . parents

addExpRetTypeToLocalScope :: Type -> TypeCheckerM' Env
addExpRetTypeToLocalScope t = do
  env <- ask
  pure $ env {expRetType = Just t}

addExpItemTypeToLocalScope :: Type -> TypeCheckerM' Env
addExpItemTypeToLocalScope t = do
  env <- ask
  pure $ env {expItemType = Just t}

addRetTypeToLocalScope :: Type -> TypeCheckerM' Env
addRetTypeToLocalScope t = do
  env <- ask
  pure $ env {retType = Just t}

addCurrClass :: Ident -> TypeCheckerM' Env
addCurrClass ident = do
  modify $ \store -> store {functions = M.insert ident M.empty (functions store)}
  modify $ \store -> store {fields = M.insert ident M.empty (fields store)}
  env <- ask
  pure $ env {currClass = ident}

getCurrClass :: TypeCheckerM' Ident
getCurrClass = asks currClass

prepareClassChecks :: Ident -> TypeCheckerM' Env
prepareClassChecks ident = do
  env <- ask
  classFields <- gets $ \store -> (fields store) M.! ident
  pure $ env {currClass = ident, variables = classFields, variablesInBlock = M.keys classFields}

mergeParentClass :: Ident -> Ident -> TypeCheckerM' ()
mergeParentClass cIdent pIdent = do
  st <- get
  let stFields = fields st
  let stFunctions = functions st
  let fnInter = M.intersection (stFunctions M.! cIdent) (stFunctions M.! pIdent)
  when (M.size fnInter > 0) (throwError $ CustomError "duplication of fun" BNFC'NoPosition ) -- todo: change to proper err
  let newFnMap = M.union (stFunctions M.! cIdent) (stFunctions M.! pIdent)
  let fieldInter = M.intersection (stFields M.! cIdent) (stFields M.! pIdent)
  when (M.size fieldInter > 0) (throwError $  CustomError "duplication of field" BNFC'NoPosition ) -- todo: change to proper err
  let newFieldMap = M.union (stFields M.! cIdent) (stFields M.! pIdent)
  modify $ \store -> store {functions = M.insert cIdent newFnMap (functions store), fields = M.insert cIdent newFieldMap (fields store)}

addClassParent :: Ident -> Maybe Ident -> TypeCheckerM' ()
addClassParent cIdent (Just pIdent) = modify $ \store -> store {parents = M.insert cIdent pIdent (parents store)}
addClassParent _ _ = pure ()

resolveClassesInheritances :: TypeCheckerM' ()
resolveClassesInheritances = do
  storeMap <- gets fields
  let visitMap = M.fromList (map (, 0) (M.keys storeMap))
  foldM_ (flip resolveClassInheritance) visitMap (M.keys storeMap)

-- 0 - undone; 1 - visited, not done; 2 - done
resolveClassInheritance :: Ident -> M.Map Ident Int -> TypeCheckerM' (M.Map Ident Int)
resolveClassInheritance cIdent visitMap = case visitMap M.! cIdent of
  2 -> return visitMap
  1 -> throwError $ InheritanceCycle cIdent BNFC'NoPosition
  0 -> do
    maybeParent <- getParentIdent cIdent
    case maybeParent of
      Nothing -> return (M.insert cIdent 2 visitMap)
      Just pIdent -> do
        newVisitMap <- resolveClassInheritance pIdent (M.insert cIdent 1 visitMap)
        mergeParentClass cIdent pIdent
        return (M.insert cIdent 2 newVisitMap)
  _ -> throwError $  CustomError "strange val in map" BNFC'NoPosition


-- Type helpers

getCompType :: Type -> Type -> SemanticError -> TypeCheckerM' (Maybe Type)
getCompType expType evalType err
  | compareTypes expType evalType = pure $ Just evalType
  | otherwise = do
    case (expType, evalType) of
      (Ref _ t1, t2) -> getCompType t1 t2 err
      (t1, Ref _ t2) -> getCompType t1 t2 err
      (Class _ _, Class _ evalIdent) -> do
        maybeParent <- getParentIdent evalIdent
        case maybeParent of
          Just pIdent -> getCompType expType (Class BNFC'NoPosition pIdent) err
          _ -> throwError err
      _ -> throwError err

checkExceptType :: Type -> Type -> SemanticError -> TypeCheckerM' ()
checkExceptType expType t err = if compareTypes expType t then throwError err else pure ()

printWarning :: SemanticException -> TypeCheckerM' ()
printWarning e = tell [e]
