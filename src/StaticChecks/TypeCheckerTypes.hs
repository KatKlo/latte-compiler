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
addField fieldIdent t pos = do
  _ <- checkTypeValidity t pos
  currCl <- getCheckCurrClass pos
  addFieldToClass fieldIdent t pos currCl

getFieldType :: Ident -> Ident -> BNFC'Position -> TypeCheckerM' Type
getFieldType cIdent fieldIdent pos = do
  maybeType <- getField cIdent fieldIdent
  case maybeType of
    Nothing -> throwError $ PropertyNotExisting fieldIdent pos
    Just (Declaration t _) -> pure t

-- classes' parents

addClassParent :: Ident -> Maybe Ident -> BNFC'Position ->TypeCheckerM' ()
addClassParent cIdent (Just pIdent) pos = do
  checkClassValidity pIdent pos
  modify $ \store -> store {parents = M.insert cIdent pIdent (parents store)}
addClassParent _ _ _ = pure ()

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
    _ <- checkTypeValidity t pos
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
  _ <- checkTypeReturnValidity t (hasPosition t)
  env <- ask
  pure $ env {expRetType = Just t}

addExpItemType :: Type -> TypeCheckerM' Env
addExpItemType t = do
  _ <- checkTypeValidity t (hasPosition t) -- unnecessary as it is checked while saving this var
  env <- ask
  pure $ env {expItemType = Just t}

addRetType :: Type -> TypeCheckerM' Env
addRetType t = do
  _ <- checkTypeReturnValidity t (hasPosition t)
  env <- ask
  pure $ env {retType = Just t}

-- current class

setCurrClass :: Ident -> TypeCheckerM' Env
setCurrClass ident = do
  env <- ask
  pure $ env {currClass = ident}

addNewClassDef :: Ident -> TypeCheckerM' ()
addNewClassDef ident = do
  typeExist <- isClassDefined ident
  when typeExist (throwError $ ClassRedefined ident BNFC'NoPosition)
  modify $ \store -> store {functions = M.insert ident M.empty (functions store)}
  modify $ \store -> store {fields = M.insert ident M.empty (fields store)}

getCheckCurrClass :: BNFC'Position -> TypeCheckerM' Ident
getCheckCurrClass pos = do
  ident <- asks currClass
  if ident == Ident "" then throwError $ NotAllowedOutsideClass pos else pure ident 

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

compareCastingEvalType :: Type -> Type -> SemanticError -> TypeCheckerM' (Maybe Type)
compareCastingEvalType expType evalType err = do
  maybeRes <- compareAndGetTypes expType evalType
  case maybeRes of
    Just _ -> pure maybeRes
    _ -> throwError err

compareAndGetTypes :: Type -> Type -> TypeCheckerM' (Maybe Type)
compareAndGetTypes expType (Ref _ (Void _)) =  if isRefType expType then pure $ Just expType else pure Nothing
compareAndGetTypes (Ref _ expType) evalType = compareAndGetTypes expType evalType
compareAndGetTypes expType (Ref _ evalType) = compareAndGetTypes expType evalType
compareAndGetTypes expType evalType = compareTypesWithoutNull expType evalType

compareTypesWithoutNull :: Type -> Type -> TypeCheckerM' (Maybe Type)
compareTypesWithoutNull (Ref _ _) _ = undefined -- should never happen
compareTypesWithoutNull _ (Ref _ _) = undefined -- should never happen
compareTypesWithoutNull expType@(Class _ expIdent) (Class _ evalIdent) = do
  classesMatch <- compareClassTypes expIdent evalIdent
  if classesMatch then pure $ Just expType else pure Nothing
compareTypesWithoutNull expType evalType
  | basicCompareTypes expType evalType = pure $ Just expType
  | otherwise = pure Nothing

compareClassTypes :: Ident -> Ident -> TypeCheckerM' Bool
compareClassTypes expIdent evalIdent
  | expIdent == evalIdent = pure True
  | otherwise = do
    maybeParent <- getParentIdent evalIdent
    case maybeParent of
      Just pIdent -> compareClassTypes expIdent pIdent
      _ -> pure False

compareCastingBothWays :: Type -> Type -> TypeCheckerM' (Maybe Type)
compareCastingBothWays t1 t2 = do
  maybeRes1 <- compareAndGetTypes t1 t2
  case maybeRes1 of
    Just _ -> pure maybeRes1
    _ -> compareAndGetTypes t2 t1

checkTypeReturnValidity :: Type -> BNFC'Position -> TypeCheckerM' ()
checkTypeReturnValidity (Void _) _ = pure ()
checkTypeReturnValidity (Ref _ t) pos = checkTypeReturnValidity t pos
checkTypeReturnValidity t pos = checkTypeValidity t pos

checkTypeValidity :: Type -> BNFC'Position -> TypeCheckerM' ()
checkTypeValidity Int {} _ = pure ()
checkTypeValidity Str {} _ = pure ()
checkTypeValidity Bool {} _ = pure ()
checkTypeValidity (Void _ ) pos = throwError $ VoidNotAllowed pos
checkTypeValidity (Arr _ t) pos = checkTypeValidity t pos
checkTypeValidity (Class _ ident) pos = checkClassValidity ident pos
checkTypeValidity _ _ = undefined -- should never happen

checkClassValidity :: Ident -> BNFC'Position -> TypeCheckerM' ()
checkClassValidity ident pos = do
  typeExist <- isClassDefined ident
  unless typeExist (throwError $ ClassNotDefined ident pos)

isClassDefined :: Ident -> TypeCheckerM' Bool
isClassDefined ident = gets $ M.member ident . functions

printWarning :: SemanticException -> TypeCheckerM' ()
printWarning e = tell [e]
