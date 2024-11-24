{-# LANGUAGE TupleSections #-}

module StaticChecks.TypeCheckerTypes where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M
import qualified Data.Set as S
import Grammar.AbsLatte
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
    retType :: Maybe Type
  }
newtype Store = Store { functions :: M.Map Ident Declaration }

data Declaration = Declaration {tpe :: Type, position :: BNFC'Position} deriving (Eq, Ord, Show, Read)

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
emptyStore = Store builtInFunctionsMap

emptyEnv :: Env
emptyEnv = Env M.empty [] Nothing Nothing Nothing

newBlockEnv :: TypeCheckerM' Env
newBlockEnv = do
  env <- ask
  pure env {variablesInBlock = []}

-- functions / methods

addNewFunction :: Ident -> Declaration -> TypeCheckerM' ()
addNewFunction fnIdent decl = do
  modify $ \store -> store {functions = M.insert fnIdent decl (functions store)}

addFunction :: Ident -> Type -> BNFC'Position -> TypeCheckerM' ()
addFunction fnIdent t pos = do
  maybeFunc <- getFunction fnIdent
  case maybeFunc of
    Nothing -> addNewFunction fnIdent (Declaration t pos)
    Just (Declaration _ BNFC'NoPosition) -> throwError $ BuiltInRedeclaration fnIdent pos
    Just (Declaration _ firstPos) -> throwError $ RedeclarationInScope fnIdent firstPos pos

getFunction :: Ident -> TypeCheckerM' (Maybe Declaration)
getFunction fnIdent = gets $ \store -> M.lookup fnIdent (functions store)

getFunctionType :: Ident -> BNFC'Position -> TypeCheckerM' Type
getFunctionType fnIdent pos = do
  maybeType <- getFunction fnIdent
  case maybeType of
    Nothing -> throwError $ FunctionNotDefined fnIdent pos
    Just (Declaration t _) -> pure t

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

getVariableType :: Ident -> BNFC'Position -> TypeCheckerM' Type
getVariableType ident pos = do
  maybeType <- getVariable ident
  case maybeType of
    Just (Declaration t _) -> pure t
    Nothing -> throwError $ VariableNotDefined ident pos

-- expected / returned type

addExpRetType :: Type -> TypeCheckerM' Env
addExpRetType t = do
  _ <- checkReturnTypeValidity t (hasPosition t)
  env <- ask
  pure $ env {expRetType = Just t}
  
getExpRetType :: TypeCheckerM' Type
getExpRetType = do
  maybeType <- asks expRetType
  case maybeType of
    Just t -> pure t
    _ -> undefined -- should never happen

addExpItemType :: Type -> TypeCheckerM' Env
addExpItemType t = do
  _ <- checkTypeValidity t (hasPosition t) -- unnecessary as it is checked while saving this var
  env <- ask
  pure $ env {expItemType = Just t}

addRetType :: Type -> TypeCheckerM' Env
addRetType t = do
  _ <- checkReturnTypeValidity t (hasPosition t)
  env <- ask
  pure $ env {retType = Just t}

-- comparing types

compareTypes :: Type -> Type -> SemanticError -> TypeCheckerM' (Maybe Type)
compareTypes expType evalType err = do
  maybeRes <- compareAndGetTypes expType evalType
  case maybeRes of
    Just _ -> pure maybeRes
    _ -> throwError err

compareAndGetTypes :: Type -> Type -> TypeCheckerM' (Maybe Type)
compareAndGetTypes (Ref _ (Void _)) evalType=  if isRefType evalType then pure $ Just evalType else pure Nothing
compareAndGetTypes expType (Ref _ (Void _)) =  if isRefType expType then pure $ Just expType else pure Nothing
compareAndGetTypes (Ref _ expType) evalType = compareAndGetTypes expType evalType
compareAndGetTypes expType (Ref _ evalType) = compareAndGetTypes expType evalType
compareAndGetTypes expType evalType = compareTypesWithoutNull expType evalType

compareTypesWithoutNull :: Type -> Type -> TypeCheckerM' (Maybe Type)
compareTypesWithoutNull (Ref _ _) _ = undefined -- should never happen
compareTypesWithoutNull _ (Ref _ _) = undefined -- should never happen
compareTypesWithoutNull expType evalType
  | basicCompareTypes expType evalType = pure $ Just expType
  | otherwise = pure Nothing

-- miscellaneous

checkReturnTypeValidity :: Type -> BNFC'Position -> TypeCheckerM' ()
checkReturnTypeValidity (Void _) _ = pure ()
checkReturnTypeValidity (Ref _ t) pos = checkReturnTypeValidity t pos
checkReturnTypeValidity t pos = checkTypeValidity t pos

checkTypeValidity :: Type -> BNFC'Position -> TypeCheckerM' ()
checkTypeValidity Int {} _ = pure ()
checkTypeValidity Str {} _ = pure ()
checkTypeValidity Bool {} _ = pure ()
checkTypeValidity (Void _ ) pos = throwError $ VoidNotAllowed pos
checkTypeValidity (Arr _ t) pos = checkTypeValidity t pos
checkTypeValidity _ _ = undefined -- should never happen

printWarning :: SemanticException -> TypeCheckerM' ()
printWarning e = tell [e]
