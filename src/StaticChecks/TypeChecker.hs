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
import StaticChecks.Errors
import StaticChecks.GrammarUtils
import Data.Ix (inRange)
import Data.Int (Int32)

-- main function

typeCheck :: Program -> IO (Either SemanticError [SemanticException])
typeCheck prog = runExceptT (runReaderT (evalStateT (execWriterT (checkProgram prog)) emptyStore) emptyEnv)

-- 'Program' level checks

checkProgram :: Program -> TypeCheckerM' ()
checkProgram (Prog _ topDefs) = do
  mapM_ saveTopDef topDefs
  checkMainDeclaration
  mapM_ checkTopDef topDefs

checkMainDeclaration :: TypeCheckerM' ()
checkMainDeclaration = do
  mainType <- getFunctionType (Ident "main") BNFC'NoPosition
  case mainType of
    Fun _ (Int _) [] -> pure ()
    Fun pos _ _ -> throwError $ WrongMainDeclaration pos
    _ -> undefined  -- should never happen

-- 'TopDef' level checks

saveTopDef :: TopDef -> TypeCheckerM' ()
saveTopDef (FnDef pos t ident args _) = do
  let mappedArgs = map argType args
  addFunction ident (Fun pos t mappedArgs) pos

checkTopDef :: TopDef -> TypeCheckerM' ()
checkTopDef (FnDef pos t ident args (SBlock _ stmts)) = do
  newEnv <- addExpRetType t
  blockEnv <- foldM resolveFnArg newEnv args
  evaluated <- local (const blockEnv) (checkStmtsListType stmts)
  case evaluated of
    Just _ -> pure ()
    Nothing -> compareTypes tVoid t (MissingReturnStmt ident pos) >> pure ()

-- 'Block' level checks

checkBlockType :: Block -> TypeCheckerM' (Maybe Type)
checkBlockType (SBlock _ stmts) = do
  cleanedEnv <- newBlockEnv
  local (const cleanedEnv) (checkStmtsListType stmts)

checkStmtsListType :: [Stmt] -> TypeCheckerM' (Maybe Type)

checkStmtsListType [] = asks retType

checkStmtsListType ((Decl _ t items) : xs) = do
  localEnv <- addExpItemType t
  updatedEnv <- foldM (\env item -> local (const env) (addDeclItemToEnv item)) localEnv items
  local (const updatedEnv) (checkStmtsListType xs)
  
checkStmtsListType (x : xs) = do
  alreadyEvaluated <- asks retType
  evaluated <- checkStmtType x
  env <- case (alreadyEvaluated, evaluated) of
    (Just _, _) -> printWarning (StmtsNeverReached (hasPosition x)) >> ask
    (Nothing, Just t) -> addRetType t
    (_, _) -> ask
  local (const env) (checkStmtsListType xs)

-- 'Item' level checks

addDeclItemToEnv :: Item -> TypeCheckerM' Env

addDeclItemToEnv (NoInit pos ident) = do
  (Just t) <- asks expItemType
  addVariableToLocalScope ident t pos
  
addDeclItemToEnv (Init pos ident expr) = do
  (Just t) <- asks expItemType
  _ <- getCheckExprType expr t
  addVariableToLocalScope ident t pos

-- 'Stmt' level checks

checkStmtType :: Stmt -> TypeCheckerM' (Maybe Type)

checkStmtType (Empty _) = pure Nothing

checkStmtType (BStmt _ block) = checkBlockType block

checkStmtType Decl {} = pure Nothing -- checked in block

checkStmtType (Ass pos itemExpr expr) = do
  expected <- getExprType itemExpr
  _ <- getCheckExprType expr expected
  _ <- checkExprMutability itemExpr pos
  pure Nothing

checkStmtType (Incr pos itemExpr) = do
  _ <- getCheckExprType itemExpr tInt
  _ <- checkExprMutability itemExpr pos
  pure Nothing
checkStmtType (Decr pos itemExpr) = do
  _ <- getCheckExprType itemExpr tInt
  _ <- checkExprMutability itemExpr pos
  pure Nothing

checkStmtType (Ret pos expr) = do
  t <- getExpRetType
  case t of
    (Void _) -> throwError $ ExpectedVRet pos
    _ -> getCheckExprType expr t
checkStmtType (VRet pos) = do
  t <- getExpRetType
  compareTypes tVoid t (ReturnValueExpected pos)

checkStmtType (Cond pos expr s1) = checkStmtType (CondElse pos expr s1 (Empty pos))
checkStmtType (CondElse _ expr s1 s2) = do
  _ <- getCheckExprType expr tBool
  ret1 <- checkBlockType (SBlock (hasPosition s1) [s1])
  ret2 <- checkBlockType (SBlock (hasPosition s2) [s2])
  let instantRes = instantBoolExprValue expr
  case (instantRes, ret1, ret2) of
    (Just True, _, _) -> pure ret1
    (Just False, _, _) -> pure ret2
    (Nothing, Just _, Just _) -> asks expRetType
    (_, _, _) -> pure Nothing

checkStmtType (While pos expr stmt) = do
  _ <- getCheckExprType expr tBool
  ret <- checkBlockType (SBlock (hasPosition stmt) [stmt])
  let instantRes = instantBoolExprValue expr
  case (instantRes, ret) of
    (Just True, Nothing) -> printWarning (InfiniteLoop pos) >> pure Nothing
    (Just True, Just _) -> pure ret
    (_, _) -> pure Nothing

checkStmtType (ForEach pos t elIdent arrExpr stmt) = do
  evaluatedArrExpr <- getExprType arrExpr
  _ <- case evaluatedArrExpr of
    Arr _ elType -> compareTypes t elType (WrongVariableType (hasPosition t))
    _ -> throwError $ ExpectedArrType (hasPosition arrExpr)
  let elStmt = Decl pos t [NoInit pos elIdent]
  _ <- case stmt of
    BStmt _ (SBlock bPos stmts) -> checkBlockType (SBlock bPos (elStmt : stmts))
    _ -> checkBlockType (SBlock (hasPosition stmt) [elStmt, stmt])
  pure Nothing

checkStmtType (SExp _ (EApp _ (Ident "error") _)) = asks expRetType
checkStmtType (SExp _ expr) = getExprType expr >> pure Nothing

-- 'Expr' level checks

getExprType :: Expr -> TypeCheckerM' Type

getExprType (EVar pos ident) = getVariableType ident pos

getExprType (ELitInt pos num) = if isInt num then pure tInt else throwError $ IntOutOfBound num pos
getExprType (ELitTrue _) = pure tBool
getExprType (ELitFalse _) = pure tBool
getExprType (EString _ _) = pure tStr
getExprType (EArrNull pos t) = checkTypeValidity t pos >> pure (Ref pos t)
getExprType (ENull pos) = pure $ Ref pos tVoid

getExprType (ENewArr pos t expr) = do
  _ <- checkTypeValidity t pos
  _ <- getCheckExprType expr tInt
  pure $ Arr pos t

getExprType (EArrGet pos arrExpr idExpr) = do
  _ <- getCheckExprType idExpr tInt
  arrType <- getExprType arrExpr
  case arrType of
    (Arr _ t) -> pure t
    _ -> throwError $ ExpectedArrType pos
getExprType (EArrLen pos arrExpr) = do
  arrType <- getExprType arrExpr
  case arrType of
    Arr _ _ -> pure tInt
    _ -> throwError $ ExpectedArrType pos

getExprType (Neg pos (ELitInt _ num)) = getExprType (ELitInt pos (- num))
getExprType (Neg _ expr) = getCheckExprType expr tInt <&> fromJust
getExprType (Not _ expr) = getCheckExprType expr tBool <&> fromJust

getExprType (EAnd _ e1 e2) = getCheckExprType e1 tBool >> getCheckExprType e2 tBool <&> fromJust
getExprType (EOr _ e1 e2) = getCheckExprType e1 tBool >> getCheckExprType e2 tBool <&> fromJust

getExprType (EMul _ e1 op e2) = do
  _ <- getCheckExprType e1 tInt
  _ <- getCheckExprType e2 tInt
  case (e2, op) of
    (ELitInt _ 0, Div _) -> printWarning $ DivisionByZero (hasPosition e2)
    (ELitInt _ 0, Mod _) -> printWarning $ DivisionByZero (hasPosition e2)
    _ -> pure ()
  pure tInt

getExprType (EAdd _ e1 (Minus _) e2) = getCheckExprType e1 tInt >> getCheckExprType e2 tInt <&> fromJust
getExprType (EAdd pos e1 _ e2) = do
  t1 <- getExprType e1
  if isAddType t1
    then getCheckExprType e2 t1 <&> fromJust
    else throwError $ CannotMakeOpOnType "add" t1 pos

getExprType (ERel pos e1 op e2) = do
  t1 <- getExprType e1
  t2 <- getExprType e2
  maybeFinalType <- compareAndGetTypes t1 t2
  case maybeFinalType of
    Just t -> if relType op t then pure tBool else throwError $ CannotMakeOpOnType "comparison" t pos
    Nothing -> throwError $ DiffOperandTypes t1 t2 pos
  where
    relType :: RelOp -> Type -> Bool
    relType (EQU _) = isEqType
    relType (NE _) = isEqType
    relType _ = isOrdType

getExprType (EApp pos (Ident "main") _) = throwError $ MainCallNotAllowed pos
getExprType (EApp pos ident exprs) = do
  Fun _ t args <- getFunctionType ident pos
  resolveAppArgs pos args exprs
  pure t

-- typeChecker utils

resolveAppArgs :: BNFC'Position -> [Type] -> [Expr] -> TypeCheckerM' ()
resolveAppArgs _ [] [] = pure ()
resolveAppArgs pos (t : xs) (expr : ys) = getCheckExprType expr t >> resolveAppArgs pos xs ys
resolveAppArgs pos _ _ = throwError $ WrongNumberOfArgs pos

resolveFnArg :: Env -> Arg -> TypeCheckerM' Env
resolveFnArg env (FnArg pos t ident) = addVariableToScope ident t pos env

getCheckExprType :: Expr -> Type -> TypeCheckerM' (Maybe Type)
getCheckExprType expr expected = do
  evaluated <- getExprType expr
  compareTypes expected evaluated (WrongExpressionType expected evaluated (hasPosition expr))

checkExprMutability :: Expr -> BNFC'Position -> TypeCheckerM' ()
checkExprMutability EVar {} _ = pure ()
checkExprMutability EArrGet {} _ = pure ()
checkExprMutability _ pos = throwError $ OperationImpossible pos

-- helpers

isInt :: Integer -> Bool
isInt = inRange (toInteger (minBound :: Int32), toInteger (maxBound :: Int32))
