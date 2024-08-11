{-# LANGUAGE FlexibleInstances #-}

module StaticChecks.TypeCheckerTypes where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M
import qualified Data.Set as S
import Grammar.AbsLatte

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
    retType :: Maybe Type
  }

newtype Store = Store {functions :: M.Map Ident Declaration}

data Declaration = Declaration {tpe :: Type, position :: BNFC'Position}

emptyEnv :: Env
emptyEnv = Env M.empty [] Nothing Nothing Nothing

emptyStore :: Store
emptyStore = Store builtInFunctionsMap

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
  | UnknownSemanticError a

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
  show (UnknownSemanticError pos) =
    "SEMANTIC ERROR: Unknown type check exception" ++ showPos pos

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

-- TypeChecker monad and classes
type TypeCheckerM' a = WriterT [SemanticException] (StateT Store (ReaderT Env (ExceptT SemanticError IO))) a

class DefsAdder a where
  addDefs :: a -> TypeCheckerM' ()

class Checker a where
  check :: a -> TypeCheckerM' ()

class EnvGetter a where
  getEnv :: a -> TypeCheckerM' Env

class TypeGetterChecker a where
  getCheckType :: a -> TypeCheckerM' (Maybe Type)

class TypeGetter a where
  getType :: a -> TypeCheckerM' Type

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
updateFunctions ident decl = modify $ \store -> store {functions = M.insert ident decl (functions store)}

addFunction :: BNFC'Position -> Ident -> Type -> TypeCheckerM' ()
addFunction pos ident t
  | ident `elem` builtInFunctions = throwError $ BuiltInRedeclaration ident pos
  | otherwise = do
    maybeFunc <- gets $ M.lookup ident . functions
    case maybeFunc of
      Nothing -> updateFunctions ident (Declaration t pos)
      Just (Declaration _ firstPos) -> throwError $ RedeclarationInScope ident firstPos pos

getFunctionType :: Ident -> BNFC'Position -> TypeCheckerM' Type
getFunctionType ident pos = do
  maybeType <- gets $ M.lookup ident . functions
  case maybeType of
    Nothing -> throwError $ FunctionNotDefined ident pos
    Just (Declaration t _) -> pure t

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
mapArg (FnArg _ t _) = t

ordType :: Type -> Bool
ordType (Int _) = True
ordType (Str _) = True
ordType _ = False

eqType :: Type -> Bool
eqType (Int _) = True
eqType (Str _) = True
eqType (Bool _) = True
eqType _ = False

addType :: Type -> Bool
addType (Int _) = True
addType (Str _) = True
addType _ = False

compareType :: Type -> Type -> Bool
compareType (Int _) (Int _) = True
compareType (Str _) (Str _) = True
compareType (Bool _) (Bool _) = True
compareType (Void _) (Void _) = True
compareType _ _ = False

getCompType :: Type -> Type -> SemanticError -> TypeCheckerM' (Maybe Type)
getCompType expType t err = if compareType expType t then pure $ Just t else throwError err

checkExceptType :: Type -> Type -> SemanticError -> TypeCheckerM' ()
checkExceptType expType t err = if compareType expType t then throwError err else pure ()

printWarning :: SemanticException -> TypeCheckerM' ()
printWarning e = tell [e]
