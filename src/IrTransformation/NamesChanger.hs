module IrTransformation.NamesChanger where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad
import qualified Data.Map as M
import Data.Maybe
import Grammar.AbsLatte

type Env = M.Map Ident Ident

type Store = M.Map Ident Integer

emptyEnv :: Env
emptyEnv = M.empty

emptyStore :: Store
emptyStore = M.empty

addToEnv :: Ident -> Env -> RenamerM' Env
addToEnv ident@(Ident name) env = do
  maybeIdentCounter <- gets $ M.lookup ident
  let identCounter = fromMaybe 0 maybeIdentCounter
  modify $ M.insert ident (identCounter + 1)
  return $ M.insert ident (Ident $ name ++ "#" ++ show identCounter) env

type RenamerM' a = StateT Store (ReaderT Env Identity) a

rename :: Program -> Program
rename prog = runRenamerM (renameProgram prog) emptyEnv emptyStore

runRenamerM :: RenamerM' a -> Env -> Store -> a
runRenamerM m env store = runIdentity $ runReaderT (evalStateT m store) env

renameProgram :: Program -> RenamerM' Program
renameProgram (Prog pos defs) = Prog pos <$> mapM renameTopDef defs

renameTopDef :: TopDef -> RenamerM' TopDef
renameTopDef (FnTopDef pos fnDef) = FnTopDef pos <$> renameFnDef fnDef
renameTopDef (ClassTopDef pos classDef) = ClassTopDef pos <$> renameClassDef classDef

renameFnDef :: FnDef -> RenamerM' FnDef
renameFnDef (FunDef pos t ident args block) = do
  (newArgs, blockEnv) <- argsToEnv args
  newBlock <- local (const blockEnv) (renameBlock block)
  pure $ FunDef pos t ident newArgs newBlock

renameClassDef :: ClassDef -> RenamerM' ClassDef
renameClassDef = pure -- todo

renameBlock :: Block -> RenamerM' Block
renameBlock (SBlock pos stmts) = SBlock pos <$> renameStmts stmts

renameStmts :: [Stmt] -> RenamerM' [Stmt]
renameStmts [] = pure []
renameStmts ((Decl pos t items) : stmts) = do
  (newItems, newEnv) <- renameItems items
  newStmts <- local (const newEnv) (renameStmts stmts)
  pure $ Decl pos t newItems : newStmts
renameStmts (stmt : stmts) = do
  newStmt <- renameStmt stmt
  newStmts <- renameStmts stmts
  pure $ newStmt : newStmts

-- renameItem

renameStmt :: Stmt -> RenamerM' Stmt
renameStmt stmt@(Empty _) = pure stmt
renameStmt (BStmt pos block) = BStmt pos <$> renameBlock block
--renameStmt stmt@(Decl pos _ _) = renameStmt $ BStmt pos (SBlock pos [stmt]) -- is it needed?
renameStmt stmt@ForEach {} = pure stmt -- todo
renameStmt (Ass pos itemExpr expr) = do
  newItemExpr <- renameExpr itemExpr
  newExpr <- renameExpr expr
  pure $ Ass pos newItemExpr newExpr
renameStmt (Incr pos itemExpr) = Incr pos <$> renameExpr itemExpr
renameStmt (Decr pos itemExpr) = Decr pos <$> renameExpr itemExpr
renameStmt (Ret pos expr) = Ret pos <$> renameExpr expr
renameStmt stmt@(VRet _) = pure stmt
renameStmt (Cond pos expr stmt) = do
  newExpr <- renameExpr expr
  newStmt <- renameStmt stmt
  pure $ Cond pos newExpr newStmt
renameStmt (CondElse pos expr stmt1 stmt2) = do
  newExpr <- renameExpr expr
  newStmt1 <- renameStmt stmt1
  newStmt2 <- renameStmt stmt2
  pure $ CondElse pos newExpr newStmt1 newStmt2
renameStmt (While pos expr stmt) = do
  newExpr <- renameExpr expr
  newStmt <- renameStmt stmt
  pure $ While pos newExpr newStmt
renameStmt (SExp pos expr) = SExp pos <$> renameExpr expr

argsToEnv :: [Arg] -> RenamerM' ([Arg], Env)
argsToEnv args = do
  (finalArgs, finalEnv) <- foldM foldFun ([], emptyEnv) args
  pure (reverse finalArgs, finalEnv)
  where
    foldFun (newArgs, newEnv) item = do
      (newArg, newerEnv) <- local (const newEnv) (renameArg item)
      pure (newArg : newArgs, newerEnv)

renameArg :: Arg -> RenamerM' (Arg, Env)
renameArg (FunArg pos t ident) = do
  env <- ask
  newEnv <- addToEnv ident env
  let newIdent = fromMaybe undefined (M.lookup ident newEnv)
  pure (FunArg pos t newIdent, newEnv)

renameItems :: [Item] -> RenamerM' ([Item], Env)
renameItems items = do
  env <- ask
  (finalItems, finalEnv) <- foldM foldFun ([], env) items
  pure (reverse finalItems, finalEnv)
  where
    foldFun (newItems, newEnv) item = do
      (newItem, newerEnv) <- local (const newEnv) (renameItem item)
      pure (newItem : newItems, newerEnv)

renameItem :: Item -> RenamerM' (Item, Env)
renameItem (NoInit pos ident) = do
  env <- ask
  newEnv <- addToEnv ident env
  let newIdent = fromMaybe undefined (M.lookup ident newEnv)
  pure (NoInit pos newIdent, newEnv)
renameItem (Init pos ident expr) = do
  env <- ask
  newExpr <- renameExpr expr
  newEnv <- addToEnv ident env
  let newIdent = fromMaybe undefined (M.lookup ident newEnv)
  pure (Init pos newIdent newExpr, newEnv)

resolveIdent :: Ident -> RenamerM' Ident
resolveIdent ident = do
  maybeNewIdent <- asks (M.lookup ident)
  maybe undefined return maybeNewIdent

renameExpr :: Expr -> RenamerM' Expr
renameExpr (EVar pos ident) = EVar pos <$> resolveIdent ident
renameExpr expr@EArrGet {} = pure expr -- todo
renameExpr expr@EFieldGet {} = pure expr -- todo
renameExpr expr@EMethod {} = pure expr -- todo
renameExpr (EApp pos ident exprs) = do
  newExprs <- mapM renameExpr exprs
  return $ EApp pos ident newExprs
renameExpr expr@(EString _ _) = return expr
renameExpr (Neg pos expr) = Neg pos <$> renameExpr expr
renameExpr (Not pos expr) = Not pos <$> renameExpr expr
renameExpr (EMul pos expr1 mulOp expr2) = do
  newExpr1 <- renameExpr expr1
  newExpr2 <- renameExpr expr2
  return $ EMul pos newExpr1 mulOp newExpr2
renameExpr (EAdd pos expr1 addOp expr2) = do
  newExpr1 <- renameExpr expr1
  newExpr2 <- renameExpr expr2
  return $ EAdd pos newExpr1 addOp newExpr2
renameExpr (ERel pos expr1 relOp expr2) = do
  newExpr1 <- renameExpr expr1
  newExpr2 <- renameExpr expr2
  return $ ERel pos newExpr1 relOp newExpr2
renameExpr (EAnd pos expr1 expr2) = do
  newExpr1 <- renameExpr expr1
  newExpr2 <- renameExpr expr2
  return $ EAnd pos newExpr1 newExpr2
renameExpr (EOr pos expr1 expr2) = do
  newExpr1 <- renameExpr expr1
  newExpr2 <- renameExpr expr2
  return $ EOr pos newExpr1 newExpr2
renameExpr expr = return expr -- todo: check if all of the rest doesn't need change
