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

-- TypeChecker monad

type TypeCheckerM' a = WriterT [SemanticException] (StateT Store (ReaderT Env (ExceptT SemanticError IO))) a

-- environment and store

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

-- new environment / store

emptyStore :: Store
emptyStore = Store (M.singleton (Ident "") builtInFunctionsMap) M.empty M.empty

emptyEnv :: Env
emptyEnv = Env M.empty [] Nothing Nothing Nothing (Ident "")

newBlockEnv :: TypeCheckerM' Env
newBlockEnv = do
  env <- ask
  pure env {variablesInBlock = []}

-- functions / methods

addNewFunction :: Ident -> Ident -> Declaration -> TypeCheckerM' ()
addNewFunction cIdent fnIdent decl = do
  fnMap <- gets functions
  let newClassMap = M.insert fnIdent decl (fnMap M.! cIdent)
  modify $ \store -> store {functions = M.insert cIdent newClassMap fnMap}

addFunctionToClass :: Ident -> Type -> BNFC'Position -> Ident -> TypeCheckerM' ()
addFunctionToClass fnIdent t pos cIdent = do
  maybeFunc <- getMethod cIdent fnIdent
  case maybeFunc of
    Nothing -> addNewFunction cIdent fnIdent (Declaration t pos)
    Just (Declaration _ BNFC'NoPosition) -> throwError $ BuiltInRedeclaration fnIdent pos
    Just (Declaration _ firstPos) -> throwError $ RedeclarationInScope fnIdent firstPos pos

addFunction :: Ident -> Type -> BNFC'Position -> TypeCheckerM' ()
addFunction fnIdent t pos = asks currClass >>= addFunctionToClass fnIdent t pos

getMethod :: Ident -> Ident -> TypeCheckerM' (Maybe Declaration)
getMethod cIdent fnIdent = gets $ \store -> M.lookup fnIdent (functions store M.! cIdent)

getFunction :: Ident -> TypeCheckerM' (Maybe Declaration)
getFunction = getMethod (Ident "")

getMethodOrFunction :: Ident -> Ident -> TypeCheckerM' (Maybe Declaration)
getMethodOrFunction cIdent fnIdent = do
  maybeDecl <- getMethod cIdent fnIdent
  case (maybeDecl, cIdent) of
    (Just decl, _) -> pure (Just decl)
    (_, Ident "") -> pure Nothing
    _ -> getFunction fnIdent

getMethodType :: Ident -> Ident -> BNFC'Position -> TypeCheckerM' Type
getMethodType cIdent fnIdent pos = do
  maybeType <- getMethod cIdent fnIdent
  case maybeType of
    Nothing -> throwError $ MethodNotDefined cIdent fnIdent pos
    Just (Declaration t _) -> pure t

getFunctionType :: Ident -> BNFC'Position -> TypeCheckerM' Type
getFunctionType fnIdent pos = do
  cIdent <- asks currClass
  maybeType <- getMethodOrFunction cIdent fnIdent
  case maybeType of
    Nothing -> throwError $ FunctionNotDefined fnIdent pos
    Just (Declaration t _) -> pure t

-- fields

addNewField :: Ident -> Ident -> Declaration -> TypeCheckerM' ()
addNewField cIdent fieldIdent decl = do
  fieldsMap <- gets fields
  let newClassMap = M.insert fieldIdent decl (fieldsMap M.! cIdent)
  modify $ \store -> store {fields = M.insert cIdent newClassMap fieldsMap}

getField :: Ident -> Ident -> TypeCheckerM' (Maybe Declaration)
getField cIdent fIdent = gets $ \store -> M.lookup fIdent (fields store M.! cIdent)

addFieldToClass :: Ident -> Type -> BNFC'Position -> Ident -> TypeCheckerM' ()
addFieldToClass fieldIdent t pos cIdent = do
  maybeField <- getField cIdent fieldIdent
  case maybeField of
    Nothing -> addNewField cIdent fieldIdent (Declaration t pos)
    Just (Declaration _ firstPos) -> throwError $ RedeclarationInScope fieldIdent firstPos pos

addField :: Ident -> Type -> BNFC'Position -> TypeCheckerM' ()
addField fieldIdent t pos = asks currClass >>= addFieldToClass fieldIdent t pos

getFieldType :: Ident -> Ident -> BNFC'Position -> TypeCheckerM' Type
getFieldType cIdent fieldIdent pos = do
  maybeType <- getField cIdent fieldIdent
  case maybeType of
    Nothing -> throwError $ PropertyNotExisting fieldIdent pos
    Just (Declaration t _) -> pure t

-- classes' parents

addClassParent :: Ident -> Maybe Ident -> TypeCheckerM' ()
addClassParent cIdent (Just pIdent) = modify $ \store -> store {parents = M.insert cIdent pIdent (parents store)}
addClassParent _ _ = pure ()

getParentIdent :: Ident -> TypeCheckerM' (Maybe Ident)
getParentIdent cIdent = gets $ M.lookup cIdent . parents

-- variables

addVariableToEnv :: Ident -> Declaration -> Env -> Env
addVariableToEnv ident decl env = env {
    variables = M.insert ident decl (variables env),
    variablesInBlock = ident : variablesInBlock env
  }

addVariableToScope :: Ident -> Type -> BNFC'Position -> Env -> TypeCheckerM' Env
addVariableToScope ident t pos env
  | ident `elem` variablesInBlock env = do
    let Declaration _ firstPos = variables env M.! ident
    throwError $ RedeclarationInScope ident firstPos pos
  | otherwise = do
    when (compareTypes tVoid t) (throwError $ VoidVariable (hasPosition t))
    pure $ addVariableToEnv ident (Declaration t pos) env

addVariableToLocalScope :: Ident -> Type -> BNFC'Position -> TypeCheckerM' Env
addVariableToLocalScope ident t pos = ask >>= addVariableToScope ident t pos

getVariable :: Ident -> TypeCheckerM' (Maybe Declaration)
getVariable ident = reader $ M.lookup ident . variables

getVariableOrField :: Ident -> Ident -> TypeCheckerM' (Maybe Declaration)
getVariableOrField cIdent fieldIdent = do
  maybeDecl <- getVariable fieldIdent
  case (maybeDecl, cIdent) of
    (Just decl, _) -> pure (Just decl)
    (_, Ident "") -> pure Nothing
    _ -> getField cIdent fieldIdent

getVariableType :: Ident -> BNFC'Position -> TypeCheckerM' Type
getVariableType ident pos = do
  cIdent <- asks currClass
  maybeType <- getVariableOrField cIdent ident
  case maybeType of
    Just (Declaration t _) -> pure t
    Nothing -> throwError $ VariableNotDefined ident pos

-- expected / returned type

addExpRetType :: Type -> TypeCheckerM' Env
addExpRetType t = do
  env <- ask
  pure $ env {expRetType = Just t}

addExpItemType :: Type -> TypeCheckerM' Env
addExpItemType t = do
  env <- ask
  pure $ env {expItemType = Just t}

addRetType :: Type -> TypeCheckerM' Env
addRetType t = do
  env <- ask
  pure $ env {retType = Just t}

-- current class

addCurrClass :: Ident -> TypeCheckerM' Env
addCurrClass ident = do
  env <- ask
  pure $ env {currClass = ident}

addNewCurrClass :: Ident -> TypeCheckerM' Env
addNewCurrClass ident = do
  modify $ \store -> store {functions = M.insert ident M.empty (functions store)}
  modify $ \store -> store {fields = M.insert ident M.empty (fields store)}
  addCurrClass ident

getCurrClass :: TypeCheckerM' Ident
getCurrClass = asks currClass

-- resolve classes' inheritances

resolveClassesInheritances :: TypeCheckerM' ()
resolveClassesInheritances = do
  classesList <- gets $ M.keys . fields
  let visitMap = M.fromList (map (, 0) classesList) -- values meaning: 0 - undone; 1 - visited, not done; 2 - done
  foldM_ resolveClassInheritance visitMap classesList

resolveClassInheritance :: M.Map Ident Int -> Ident -> TypeCheckerM' (M.Map Ident Int)
resolveClassInheritance visitMap cIdent = case visitMap M.! cIdent of
  2 -> return visitMap
  1 -> throwError $ InheritanceCycle cIdent BNFC'NoPosition
  0 -> do
    maybeParent <- getParentIdent cIdent
    newVisitMap <- executeClassInheritance visitMap cIdent maybeParent
    return $ M.insert cIdent 2 newVisitMap
  _ -> undefined

executeClassInheritance :: M.Map Ident Int -> Ident -> Maybe Ident -> TypeCheckerM' (M.Map Ident Int)
executeClassInheritance visitMap _ Nothing = return visitMap
executeClassInheritance visitMap cIdent (Just pIdent) = do
  newVisitMap <- resolveClassInheritance (M.insert cIdent 1 visitMap) pIdent
  mergeParentClass cIdent pIdent
  return newVisitMap

mergeParentClass :: Ident -> Ident -> TypeCheckerM' ()
mergeParentClass cIdent pIdent = do
  store <- get
  mapM_ (\(i, Declaration t p) -> addFunctionToClass i t p cIdent) (M.toList (functions store M.! pIdent))
  mapM_ (\(i, Declaration t p) -> addFieldToClass i t p cIdent) (M.toList (fields store M.! pIdent))


-- miscellaneous

-- todo: fix that code :)
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

printWarning :: SemanticException -> TypeCheckerM' ()
printWarning e = tell [e]
