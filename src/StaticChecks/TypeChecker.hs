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
  resolveClassesInheritances
  checkMainDeclaration
  mapM_ checkTopDef topDefs

checkMainDeclaration :: TypeCheckerM' ()
checkMainDeclaration = do
  mainType <- getFunctionType (Ident "") (Ident "main") BNFC'NoPosition
  case mainType of
    Fun _ (Int _) [] -> pure ()
    Fun pos _ _ -> throwError $ WrongMainDeclaration pos
    _ -> throwError $ UnknownSemanticError BNFC'NoPosition

-- 'TopDef' level checks

saveTopDef :: TopDef -> TypeCheckerM' ()
saveTopDef (FnTopDef _ fnDef) = saveFnDef fnDef
saveTopDef (ClassTopDef _ classDef) = saveClassDef classDef

saveFnDef :: FnDef -> TypeCheckerM' ()
saveFnDef (FunDef pos t ident args _) = do
  let mappedArgs = map argType args
  addFunction pos ident (Fun pos t mappedArgs)

saveClassDef :: ClassDef -> TypeCheckerM' ()
saveClassDef cls = do
  let cIdent = className cls
  _ <- addClassParent cIdent (classParent cls)
  newEnv <- addCurrClass cIdent
  local (const newEnv) (mapM_ saveCStmt (classBody cls))

saveCStmt :: CStmt -> TypeCheckerM' ()
saveCStmt (MethodDef _ fnDef) = saveFnDef fnDef
saveCStmt (FieldDef pos fieldType fieldIdent) = addField pos fieldIdent fieldType

checkTopDef :: TopDef -> TypeCheckerM' ()
checkTopDef (FnTopDef _ fnDef) = checkFnDef fnDef
checkTopDef (ClassTopDef _ classDef) = checkClassDef classDef

checkFnDef :: FnDef -> TypeCheckerM' ()
checkFnDef (FunDef pos t ident args (SBlock _ stmts)) = do
  newEnv <- addExpRetTypeToLocalScope t
  blockEnv <- resolveDefArgs args newEnv
  evaluated <- local (const blockEnv) (checkStmtsListType stmts)
  case evaluated of
    Just _ -> pure ()
    Nothing -> getCompType tVoid t (NoReturnStmt ident pos) >> pure ()

checkClassDef :: ClassDef -> TypeCheckerM' ()
checkClassDef cls = do
  newEnv <- prepareClassChecks (className cls)
  local (const newEnv) (mapM_ checkCStmt (classBody cls))

checkCStmt :: CStmt -> TypeCheckerM' ()
checkCStmt (MethodDef _ fnDef) = checkFnDef fnDef
checkCStmt _ = pure ()

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

checkStmtType (Ass _ itemExpr expr) = do
  expected <- getExprType itemExpr
  _ <- getCheckExprType expr expected
  pure Nothing

checkStmtType (Incr _ itemExpr) = do
  _ <- getCheckExprType itemExpr tInt
  pure Nothing
checkStmtType (Decr _ itemExpr) = do
  _ <- getCheckExprType itemExpr tInt
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

-- what if arr.length = 0 ???
checkStmtType (ForEach pos t elIdent arrExpr stmt) = do
  (Arr _ arrType) <-getExprType arrExpr
  _ <- getCompType arrType t ( WrongVariableType (hasPosition t))
  checkBlockType (SBlock (hasPosition stmt) [(Decl pos t [NoInit pos elIdent]), stmt])

checkStmtType (SExp _ expr) = getExprType expr >> pure Nothing

-- 'Expr' level checks

getExprType :: Expr -> TypeCheckerM' Type

getExprType (EVar pos ident) = getVariableType ident pos
getExprType (ESelf pos) = do
  cIdent <- getCurrClass
  pure $ Class pos cIdent -- todo: what if not in class?

getExprType (ELitInt pos num) = if isInt num then pure tInt else throwError $ IntOutOfBound num pos
getExprType (ELitTrue _) = pure tBool
getExprType (ELitFalse _) = pure tBool
getExprType (EString _ _) = pure tStr
getExprType (EClassNull pos ident) = pure $ Ref pos (Class pos ident)
getExprType (EArrNull pos t) = pure $ Ref pos t
getExprType (ENull pos) = pure $ Ref pos tVoid

-- maybe check if expr > 0 ???
getExprType (ENewArr pos t expr) = do
  _ <- getCheckExprType expr tInt
  pure $ Arr pos t
getExprType (ENewObj _ t) = pure t

getExprType (EArrGet pos arrExpr idExpr) = do
  _ <- getCheckExprType idExpr tInt
  arrType <- getExprType arrExpr
  case arrType of
    (Arr _ t) -> pure t
    _ -> throwError $ ExpectedArrType pos
getExprType (EFieldGet pos itemExpr ident) = do
  itemType <- getExprType itemExpr
  case (itemType, ident) of
    (Arr _ _, Ident "length") -> pure tInt
    (Class _ cIdent, _) -> getFieldType cIdent ident pos
    _ -> throwError $ UnknownSemanticError pos

getExprType (EMethod pos itemExpr methodIdent exprs) = do
  (Class _ classIdent) <- getExprType itemExpr
  Fun _ t args <- getFunctionType classIdent methodIdent pos
  resolveAppArgs pos args exprs
  pure t

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
  if isAddType t1
    then getCheckExprType e2 t1 <&> fromJust
    else throwError $ WrongExpressionType (hasPosition e1)

getExprType (ERel _ e1 op e2) = do
  t1 <- getExprType e1
  if relType op t1
    then getCheckExprType e2 t1 >> pure tBool
    else throwError $ WrongExpressionType (hasPosition e1)
  where
    relType :: RelOp -> Type -> Bool
    relType (EQU _) = isEqType
    relType (NE _) = isEqType
    relType _ = isOrdType

getExprType (EApp pos ident exprs) = do
  when (ident == Ident "main") (throwError $ WrongMainCall pos)
  Fun _ t args <- getFunctionType (Ident "") ident pos
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
resolveDefArg (FunArg pos t ident) env = do
  addVariableToScope pos ident t env

getCheckExprType :: Expr -> Type -> TypeCheckerM' (Maybe Type)
getCheckExprType expr (Void _) = throwError $ WrongExpressionType (hasPosition expr)
getCheckExprType expr expected = do
  evaluated <- getExprType expr
  getCompType expected evaluated (WrongExpressionType (hasPosition expr))

-- helpers

isInt :: Integer -> Bool
isInt = inRange (toInteger (minBound :: Int32), toInteger (maxBound :: Int32))
