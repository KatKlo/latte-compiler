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

typeCheck :: Program -> IO (Either SemanticError [SemanticException])
typeCheck prog = runExceptT (runReaderT (evalStateT (execWriterT (checkProgram prog)) emptyStore) emptyEnv)

checkProgram :: Program -> TypeCheckerM' ()
checkProgram prog = do
  addDefs prog
  check prog

instance DefsAdder Program where
  addDefs (Prog _ defs) = addDefs defs

instance DefsAdder [TopDef] where
  addDefs [] = do
    mainType <- getFunctionType (Ident "main") BNFC'NoPosition
    case mainType of
      Fun _ (Int _) [] -> pure ()
      Fun pos _ _ -> throwError $ WrongMainDeclaration pos
      _ -> throwError $ UnknownSemanticError BNFC'NoPosition
  addDefs (x : xs) = addDefs x >> addDefs xs

instance DefsAdder TopDef where
  addDefs (FnDef pos t ident args _) = do
    let mappedArgs = map mapArg args
    addFunction pos ident (Fun pos t mappedArgs)

instance Checker Program where
  check (Prog _ topDefs) = mapM_ check topDefs

instance Checker TopDef where
  check (FnDef pos t ident args (SBlock _ stmts)) = do
    newEnv <- addExpRetTypeToLocalScope t
    blockEnv <- resolveDefArgs args newEnv
    evaluated <- local (const blockEnv) (getCheckType stmts)
    case evaluated of
      Just _ -> pure ()
      Nothing -> getCompType tVoid t (NoReturnStmt ident pos) >> pure ()

instance TypeGetterChecker Block where
  getCheckType (SBlock _ stmts) = do
    cleanedEnv <- newBlockEnv
    local (const cleanedEnv) (getCheckType stmts)

instance TypeGetterChecker [Stmt] where
  getCheckType [] = asks retType
  getCheckType ((Decl _ t items) : xs) = do
    localEnv <- addExpItemTypeToLocalScope t
    updatedEnv <- foldM (\env item -> local (const env) (getEnv item)) localEnv items
    local (const updatedEnv) (getCheckType xs)
  getCheckType (x : xs) = do
    evaluated <- getCheckType x
    alreadyEvaluated <- asks retType
    env <- case (alreadyEvaluated, evaluated) of
      (Just _, _) -> printWarning (StmtsNeverReached (hasPosition x)) >> ask
      (Nothing, Just t) -> addRetTypeToLocalScope t
      (_, _) -> ask
    local (const env) (getCheckType xs)

instance EnvGetter Item where
  getEnv (NoInit pos ident) = do
    (Just t) <- asks expItemType
    addVariableToLocalScope pos ident t
  getEnv (Init pos ident expr) = do
    (Just t) <- asks expItemType
    _ <- getCheckExprType expr t
    addVariableToLocalScope pos ident t

instance TypeGetterChecker Stmt where
  getCheckType (Empty _) = pure Nothing
  getCheckType (BStmt _ block) = getCheckType block
  
  getCheckType Decl {} = pure Nothing -- checked in block
  getCheckType (Ass pos ident expr) = do
    expected <- getVariableType ident pos
    _ <- getCheckExprType expr expected
    pure Nothing
    
  getCheckType (Incr pos ident) = do
    t <- getVariableType ident pos
    _ <- getCompType tInt t (WrongVariableType pos)
    pure Nothing
  getCheckType (Decr pos ident) = do
    t <- getVariableType ident pos
    _ <- getCompType tInt t (WrongVariableType pos)
    pure Nothing
    
  getCheckType (Ret _ expr) = do
    Just t <- asks expRetType
    getCheckExprType expr t
  getCheckType (VRet pos) = do
    Just t <- asks expRetType
    getCompType tVoid t (WrongReturnType pos)
    
  getCheckType (Cond pos expr s1) = getCheckType (CondElse pos expr s1 (Empty pos))
  getCheckType (CondElse _ expr s1 s2) = do
    _ <- getCheckExprType expr tBool
    ret1 <- getCheckType (SBlock (hasPosition s1) [s1])
    ret2 <- getCheckType (SBlock (hasPosition s2) [s2])
    let instantRes = instantBoolExpValue expr
    case (instantRes, ret1, ret2) of
      (Just True, _, _) -> pure ret1
      (Just False, _, _) -> pure ret2
      (Nothing, Just _, Just _) -> asks expRetType
      (_, _, _) -> pure Nothing
 
  getCheckType (While pos expr stmt) = do
    _ <- getCheckExprType expr tBool
    ret <- getCheckType (SBlock (hasPosition stmt) [stmt])
    let instantRes = instantBoolExpValue expr
    case (instantRes, ret) of
      (Just True, Nothing) -> printWarning (InfiniteLoop pos) >> pure Nothing
      (Just True, Just _) -> pure ret
      (_, _) -> pure Nothing

  getCheckType (SExp _ expr) = getType expr >> pure Nothing

instance TypeGetter Expr where
  getType (EVar pos ident) = getVariableType ident pos
  
  getType (ELitInt pos num) = if isInt num then pure tInt else throwError $ IntOutOfBound num pos
  getType (ELitTrue _) = pure tBool
  getType (ELitFalse _) = pure tBool
  getType (EString _ _) = pure tStr
  
  getType (Neg pos (ELitInt _ num)) = getType (ELitInt pos (- num))
  getType (Neg _ expr) = getCheckExprType expr tInt <&> fromJust
  getType (Not _ expr) = getCheckExprType expr tBool <&> fromJust
  
  getType (EAnd _ e1 e2) = getCheckExprType e1 tBool >> getCheckExprType e2 tBool <&> fromJust
  getType (EOr _ e1 e2) = getCheckExprType e1 tBool >> getCheckExprType e2 tBool <&> fromJust
  
  getType (EMul _ e1 op e2) = do
    _ <- getCheckExprType e1 tInt
    _ <- getCheckExprType e2 tInt
    case (e2, op) of
      (ELitInt _ 0, Div _) -> throwError $ DivisionByZero (hasPosition e2)
      (ELitInt _ 0, Mod _) -> throwError $ DivisionByZero (hasPosition e2)
      _ -> pure tInt
      
  getType (EAdd _ e1 (Minus _) e2) = getCheckExprType e1 tInt >> getCheckExprType e2 tInt <&> fromJust
  getType (EAdd _ e1 _ e2) = do
    t1 <- getType e1
    if addType t1
      then getCheckExprType e2 t1 <&> fromJust
      else throwError $ WrongExpressionType (hasPosition e1)
      
  getType (ERel _ e1 op e2) = do
    t1 <- getType e1
    if relType op t1
      then getCheckExprType e2 t1 >> pure tBool
      else throwError $ WrongExpressionType (hasPosition e1)
    where
      relType :: RelOp -> Type -> Bool
      relType (EQU _) = eqType
      relType (NE _) = eqType
      relType _ = ordType
  
  getType (EApp pos ident exprs) = do
    when (ident == Ident "main") (throwError $ WrongMainCall pos)
    Fun _ t args <- getFunctionType ident pos
    resolveAppArgs pos args exprs
    pure t

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
  evaluated <- getType expr
  getCompType expected evaluated (WrongExpressionType (hasPosition expr))

instantBoolExpValue :: Expr -> Maybe Bool
instantBoolExpValue (ELitTrue _) = Just True
instantBoolExpValue (ELitFalse _) = Just False
instantBoolExpValue (Not _ expr) = not <$> instantBoolExpValue expr
instantBoolExpValue (EAnd _ e1 e2) = (&&) <$> instantBoolExpValue e1 <*> instantBoolExpValue e2
instantBoolExpValue (EOr _ e1 e2) = (||) <$> instantBoolExpValue e1 <*> instantBoolExpValue e2
instantBoolExpValue _ = Nothing

isInt :: Integer -> Bool
isInt = inRange (toInteger (minBound :: Int32), toInteger (maxBound :: Int32))
