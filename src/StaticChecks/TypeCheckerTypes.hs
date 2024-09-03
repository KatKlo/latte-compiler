{-# LANGUAGE FlexibleInstances #-}

module StaticChecks.TypeCheckerTypes where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M
import qualified Data.Set as S
import Grammar.AbsLatte
import Control.Monad

-- buildIn functions

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

type ClassFnDecl = M.Map Ident Declaration
type ClassFieldDecl = M.Map Ident Declaration

data Store = Store
  { functions :: M.Map Ident ClassFnDecl,
    fields :: M.Map Ident ClassFieldDecl,
    parents :: M.Map Ident Ident
  } deriving (Eq, Ord, Show, Read)

data Declaration = Declaration {tpe :: Type, position :: BNFC'Position} deriving (Eq, Ord, Show, Read)

emptyEnv :: Env
emptyEnv = Env M.empty [] Nothing Nothing Nothing (Ident "")

emptyStore :: Store
emptyStore = Store (M.singleton (Ident "") builtInFunctionsMap) M.empty M.empty

-- errors

type SemanticError = SemanticError' BNFC'Position

data SemanticError' a
  = WrongMainDeclaration a
  | RedeclarationInScope Ident a a
  | BuiltInRedeclaration Ident a
  | NoReturnStmt Ident a
  | VoidVariable a
  | IntOutOfBound Integer a
  | WrongExpressionType a
  | VariableNotDefined Ident a
  | FunctionNotDefined Ident a
  | WrongNumberOfArgs a
  | WrongVariableType a
  | WrongReturnType a
  | DivisionByZero a
  | WrongMainCall a
  | ExpectedArrType a
  | PropertyNotExisting Ident a
  | InheritanceCycle Ident a
  | UnknownSemanticError a
  | CustomErr String a

instance Show SemanticError where
  show (WrongMainDeclaration pos) =
    "SEMANTIC ERROR: Wrong main declaration" ++ showPos pos
  show (RedeclarationInScope (Ident name) pos1 pos2) =
    "SEMANTIC ERROR: " ++ name ++ " defined" ++ showPos pos1 ++ " and redefined" ++ showPos pos2
  show (BuiltInRedeclaration (Ident name) pos) =
    "SEMANTIC ERROR: Built-in function '" ++ name ++ "' redefined" ++ showPos pos
  show (NoReturnStmt (Ident name) pos) =
    "SEMANTIC ERROR: No return statement in function '" ++ name ++ "' defined" ++ showPos pos
  show (VoidVariable pos) =
    "SEMANTIC ERROR: Void variable not allowed" ++ showPos pos
  show (IntOutOfBound num pos) =
    "SEMANTIC ERROR: Integer " ++ show num ++ " out of bound" ++ showPos pos
  show (WrongExpressionType pos) =
    "SEMANTIC ERROR: Wrong expression type" ++ showPos pos
  show (VariableNotDefined (Ident name) pos) =
    "SEMANTIC ERROR: Variable '" ++ name ++ "' not defined" ++ showPos pos
  show (FunctionNotDefined (Ident name) pos) =
    "SEMANTIC ERROR: Function '" ++ name ++ "' not defined" ++ showPos pos
  show (WrongNumberOfArgs pos) =
    "SEMANTIC ERROR: Wrong number of arguments" ++ showPos pos
  show (WrongVariableType pos) =
    "SEMANTIC ERROR: Wrong variable type" ++ showPos pos
  show (WrongReturnType pos) =
    "SEMANTIC ERROR: Wrong return type" ++ showPos pos
  show (DivisionByZero pos) =
    "SEMANTIC ERROR: Division by zero" ++ showPos pos
  show (WrongMainCall pos) =
    "SEMANTIC ERROR: Wrong main call" ++ showPos pos
  show (ExpectedArrType pos) =
    "SEMANTIC ERROR: Expected array type" ++ showPos pos
  show (PropertyNotExisting (Ident name) pos) =
      "SEMANTIC ERROR: Property '" ++ name ++ "' not existing" ++ showPos pos
  show (InheritanceCycle (Ident name) _) =
      "SEMANTIC ERROR: Classes inheritance cycle with '" ++ name ++ "'"
  show (UnknownSemanticError pos) =
    "SEMANTIC ERROR: Unknown type check exception" ++ showPos pos
  show (CustomErr s _) =
    "SEMANTIC ERROR: Custom exception: " ++ s

type SemanticException = SemanticException' BNFC'Position

data SemanticException' a
  = StmtsNeverReached a
  | InfiniteLoop a
  | UnknownSemanticException a

instance Show SemanticException where
  show (StmtsNeverReached pos) =
    "SEMANTIC EXCEPTION: Statements never reached" ++ showPos pos
  show (UnknownSemanticException pos) =
    "SEMANTIC EXCEPTION: Unknown type check exception" ++ showPos pos
  show (InfiniteLoop pos) =
    "SEMANTIC EXCEPTION: Infinite loop" ++ showPos pos

showPos :: BNFC'Position -> String
showPos (Just (line, column)) = concat [" at line ", show line, ", column ", show column]
showPos _ = ""

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
  let fnInter = M.intersection ((functions st) M.! cIdent) ((functions st) M.! pIdent)
  when ((M.size fnInter) > 0) (throwError $ CustomErr ("duplication of fun") BNFC'NoPosition ) -- todo: change to proper err
  let newFnMap = M.union ((functions st) M.! cIdent) ((functions st) M.! pIdent)
  let fieldInter = M.intersection ((fields st) M.! cIdent) ((fields st) M.! pIdent)
  when ((M.size fieldInter) > 1) (throwError $  CustomErr ("duplication of field") BNFC'NoPosition ) -- todo: change to proper err (1 because of "self" field)
  let newFieldMap = M.union ((fields st) M.! cIdent) ((fields st) M.! pIdent)
  modify $ \store -> store {functions = M.insert cIdent newFnMap (functions store), fields = M.insert cIdent newFieldMap (fields store)}

addClassParent :: Ident -> (Maybe Ident) -> TypeCheckerM' ()
addClassParent cIdent (Just pIdent) = modify $ \store -> store {parents = M.insert cIdent pIdent (parents store)}
addClassParent _ _ = pure ()

resolveClassesInheritances :: TypeCheckerM' ()
resolveClassesInheritances = do
  storeMap <- gets fields
  let visitMap = M.fromList (map (\k -> (k, 0)) (M.keys storeMap))
  foldM_ (\b a -> resolveClassInheritance a b) visitMap (M.keys storeMap)

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
  _ -> throwError $  CustomErr ("strange val in map") BNFC'NoPosition


-- Type helpers

tInt :: Type
tInt = Int BNFC'NoPosition

tStr :: Type
tStr = Str BNFC'NoPosition

tBool :: Type
tBool = Bool BNFC'NoPosition

tVoid :: Type
tVoid = Void BNFC'NoPosition

mapArg :: Arg -> Type
mapArg (FunArg _ t _) = t

ordType :: Type -> Bool
ordType (Int _) = True
ordType (Str _) = True
ordType _ = False

eqType :: Type -> Bool
eqType (Int _) = True
eqType (Str _) = True
eqType (Bool _) = True
eqType t = isRefType t

addType :: Type -> Bool
addType (Int _) = True
addType (Str _) = True
addType _ = False

compareType :: Type -> Type -> Bool
compareType (Int _) (Int _) = True
compareType (Str _) (Str _) = True
compareType (Bool _) (Bool _) = True
compareType (Void _) (Void _) = True
compareType (Arr _ t1) (Arr _ t2) = compareType t1 t2
compareType (Class _ s1) (Class _ s2) = s1 == s2
compareType (Ref _ (Void _)) t2 = isRefType t2
compareType t1 (Ref _ (Void _)) = isRefType t1
compareType (Ref _ t1) (Ref _ t2) = isRefType t1 && isRefType t2
compareType _ _ = False

isRefType :: Type -> Bool
isRefType Class {} = True
isRefType Arr {} = True
isRefType Ref {} = True
isRefType _ = False

getCompType :: Type -> Type -> SemanticError -> TypeCheckerM' (Maybe Type)
getCompType expType evalType err
  | compareType expType evalType = pure $ Just evalType
  | otherwise = do
    case (expType, evalType) of
      (Class _ _, Class _ evalIdent) -> do
        maybeParent <- getParentIdent evalIdent
        case maybeParent of
          Just pIdent -> getCompType expType (Class BNFC'NoPosition pIdent) err
          _ -> throwError err
      _ -> throwError err

checkExceptType :: Type -> Type -> SemanticError -> TypeCheckerM' ()
checkExceptType expType t err = if compareType expType t then throwError err else pure ()

printWarning :: SemanticException -> TypeCheckerM' ()
printWarning e = tell [e]
