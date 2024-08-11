{-# LANGUAGE FlexibleInstances #-}

module StaticChecks.TypeChecker (typeCheck) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad
import Data.Functor
import Data.Maybe
import Grammar.AbsLatte
import StaticChecks.TypeCheckerTypes
import Data.Ix (inRange)
import Data.Int (Int32)

-- main function

typeCheck :: Program -> IO (Either SemanticError [SemanticException])
typeCheck prog = runExceptT (runReaderT (evalStateT (execWriterT (checkProgram prog)) emptyStore) emptyEnv)

-- 'Program' level checks

checkProgram :: Program -> TypeCheckerM' ()
checkProgram (Prog _ topDefs) = do
  mapM_ saveFnDefinition topDefs
  checkMainDeclaration
  mapM_ checkTopDef topDefs

checkMainDeclaration :: TypeCheckerM' ()
checkMainDeclaration = do
  mainType <- getFunctionType (Ident "main") BNFC'NoPosition
  case mainType of
    Fun _ (Int _) [] -> pure ()
    Fun pos _ _ -> throwError $ WrongMainDeclaration pos
    _ -> throwError $ UnknownSemanticError BNFC'NoPosition

-- 'TopDef' level checks

saveFnDefinition :: TopDef -> TypeCheckerM' ()
saveFnDefinition (FnDef pos t ident args _) = do
  let mappedArgs = map mapArg args
  addFunction pos ident (Fun pos t mappedArgs)

checkTopDef :: TopDef -> TypeCheckerM' ()
checkTopDef (FnDef pos t ident args (SBlock _ stmts)) = do
  newEnv <- addExpRetTypeToLocalScope t
  blockEnv <- resolveDefArgs args newEnv
  evaluated <- local (const blockEnv) (checkStmtsListType stmts)
  case evaluated of
    Just _ -> pure ()
    Nothing -> getCompType tVoid t (NoReturnStmt ident pos) >> pure ()

-- 'Block' level checks

checkBlockType :: Block -> TypeCheckerM' (Maybe Type)
checkBlockType (SBlock _ stmts) = do
  cleanedEnv <- newBlockEnv
  local (const cleanedEnv) (checkStmtsListType stmts)

checkStmtsListType :: [Stmt] -> TypeCheckerM' (Maybe Type)

checkStmtsListType [] = asks retType

checkStmtsListType ((Decl _ t items) : xs) = do
  localEnv <- addExpItemTypeToLocalScope t
  updatedEnv <- foldM (\env item -> local (const env) (addDeclItemToEnv item)) localEnv items
  local (const updatedEnv) (checkStmtsListType xs)
  
checkStmtsListType (x : xs) = do
  evaluated <- checkStmtType x
  alreadyEvaluated <- asks retType
  env <- case (alreadyEvaluated, evaluated) of
    (Just _, _) -> printWarning (StmtsNeverReached (hasPosition x)) >> ask
    (Nothing, Just t) -> addRetTypeToLocalScope t
    (_, _) -> ask
  local (const env) (checkStmtsListType xs)

-- 'Item' level checks

addDeclItemToEnv :: Item -> TypeCheckerM' Env

addDeclItemToEnv (NoInit pos ident) = do
  (Just t) <- asks expItemType
  addVariableToLocalScope pos ident t
  
addDeclItemToEnv (Init pos ident expr) = do
  (Just t) <- asks expItemType
  _ <- getCheckExprType expr t
  addVariableToLocalScope pos ident t

-- 'Stmt' level checks

checkStmtType :: Stmt -> TypeCheckerM' (Maybe Type)

checkStmtType (Empty _) = pure Nothing

checkStmtType (BStmt _ block) = checkBlockType block

checkStmtType Decl {} = pure Nothing -- checked in block

checkStmtType (Ass pos ident expr) = do
  expected <- getVariableType ident pos
  _ <- getCheckExprType expr expected
  pure Nothing

checkStmtType (Incr pos ident) = do
  t <- getVariableType ident pos
  _ <- getCompType tInt t (WrongVariableType pos)
  pure Nothing
checkStmtType (Decr pos ident) = do
  t <- getVariableType ident pos
  _ <- getCompType tInt t (WrongVariableType pos)
  pure Nothing

checkStmtType (Ret _ expr) = do
  Just t <- asks expRetType
  getCheckExprType expr t
checkStmtType (VRet pos) = do
  Just t <- asks expRetType
  getCompType tVoid t (WrongReturnType pos)

checkStmtType (Cond pos expr s1) = checkStmtType (CondElse pos expr s1 (Empty pos))
checkStmtType (CondElse _ expr s1 s2) = do
  _ <- getCheckExprType expr tBool
  ret1 <- checkBlockType (SBlock (hasPosition s1) [s1])
  ret2 <- checkBlockType (SBlock (hasPosition s2) [s2])
  let instantRes = instantBoolExpValue expr
  case (instantRes, ret1, ret2) of
    (Just True, _, _) -> pure ret1
    (Just False, _, _) -> pure ret2
    (Nothing, Just _, Just _) -> asks expRetType
    (_, _, _) -> pure Nothing

checkStmtType (While pos expr stmt) = do
  _ <- getCheckExprType expr tBool
  ret <- checkBlockType (SBlock (hasPosition stmt) [stmt])
  let instantRes = instantBoolExpValue expr
  case (instantRes, ret) of
    (Just True, Nothing) -> printWarning (InfiniteLoop pos) >> pure Nothing
    (Just True, Just _) -> pure ret
    (_, _) -> pure Nothing

checkStmtType (SExp _ expr) = getExprType expr >> pure Nothing

-- 'Expr' level checks

getExprType :: Expr -> TypeCheckerM' Type

getExprType (EVar pos ident) = getVariableType ident pos

getExprType (ELitInt pos num) = if isInt num then pure tInt else throwError $ IntOutOfBound num pos
getExprType (ELitTrue _) = pure tBool
getExprType (ELitFalse _) = pure tBool
getExprType (EString _ _) = pure tStr

getExprType (Neg pos (ELitInt _ num)) = getExprType (ELitInt pos (- num))
getExprType (Neg _ expr) = getCheckExprType expr tInt <&> fromJust
getExprType (Not _ expr) = getCheckExprType expr tBool <&> fromJust

getExprType (EAnd _ e1 e2) = getCheckExprType e1 tBool >> getCheckExprType e2 tBool <&> fromJust
getExprType (EOr _ e1 e2) = getCheckExprType e1 tBool >> getCheckExprType e2 tBool <&> fromJust

getExprType (EMul _ e1 op e2) = do
  _ <- getCheckExprType e1 tInt
  _ <- getCheckExprType e2 tInt
  case (e2, op) of
    (ELitInt _ 0, Div _) -> throwError $ DivisionByZero (hasPosition e2)
    (ELitInt _ 0, Mod _) -> throwError $ DivisionByZero (hasPosition e2)
    _ -> pure tInt

getExprType (EAdd _ e1 (Minus _) e2) = getCheckExprType e1 tInt >> getCheckExprType e2 tInt <&> fromJust
getExprType (EAdd _ e1 _ e2) = do
  t1 <- getExprType e1
  if addType t1
    then getCheckExprType e2 t1 <&> fromJust
    else throwError $ WrongExpressionType (hasPosition e1)

getExprType (ERel _ e1 op e2) = do
  t1 <- getExprType e1
  if relType op t1
    then getCheckExprType e2 t1 >> pure tBool
    else throwError $ WrongExpressionType (hasPosition e1)
  where
    relType :: RelOp -> Type -> Bool
    relType (EQU _) = eqType
    relType (NE _) = eqType
    relType _ = ordType

getExprType (EApp pos ident exprs) = do
  when (ident == Ident "main") (throwError $ WrongMainCall pos)
  Fun _ t args <- getFunctionType ident pos
  resolveAppArgs pos args exprs
  pure t

-- typeChecker utils

resolveAppArgs :: BNFC'Position -> [Type] -> [Expr] -> TypeCheckerM' ()
resolveAppArgs _ [] [] = pure ()
resolveAppArgs pos (t : xs) (expr : ys) = getCheckExprType expr t >> resolveAppArgs pos xs ys
resolveAppArgs pos _ _ = throwError $ WrongNumberOfArgs pos

resolveDefArgs :: [Arg] -> Env -> TypeCheckerM' Env
resolveDefArgs [] env = pure env
resolveDefArgs (x : xs) env = resolveDefArg x env >>= resolveDefArgs xs

resolveDefArg :: Arg -> Env -> TypeCheckerM' Env
resolveDefArg (FnArg pos t ident) env = do
  addVariableToScope pos ident t env

getCheckExprType :: Expr -> Type -> TypeCheckerM' (Maybe Type)
getCheckExprType expr (Void _) = throwError $ WrongExpressionType (hasPosition expr)
getCheckExprType expr expected = do
  evaluated <- getExprType expr
  getCompType expected evaluated (WrongExpressionType (hasPosition expr))

instantBoolExpValue :: Expr -> Maybe Bool
instantBoolExpValue (ELitTrue _) = Just True
instantBoolExpValue (ELitFalse _) = Just False
instantBoolExpValue (Not _ expr) = not <$> instantBoolExpValue expr
instantBoolExpValue (EAnd _ e1 e2) = (&&) <$> instantBoolExpValue e1 <*> instantBoolExpValue e2
instantBoolExpValue (EOr _ e1 e2) = (||) <$> instantBoolExpValue e1 <*> instantBoolExpValue e2
instantBoolExpValue _ = Nothing

-- helpers

isInt :: Integer -> Bool
isInt = inRange (toInteger (minBound :: Int32), toInteger (maxBound :: Int32))
