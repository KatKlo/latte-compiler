{-# LANGUAGE FlexibleInstances #-}

module StaticChecks.Errors where

import Grammar.AbsLatte

type SemanticError = SemanticError' BNFC'Position

data SemanticError' a
  = WrongMainDeclaration a
  | RedeclarationInScope Ident a a
  | BuiltInRedeclaration Ident a
  | NoReturnStmt Ident a
  | VoidNotAllowed a
  | ClassNotDefined Ident a
  | ClassRedefined Ident a
  | IntOutOfBound Integer a
  | WrongExpressionType a
  | VariableNotDefined Ident a
  | FunctionNotDefined Ident a
  | MethodNotDefined Ident Ident a
  | WrongNumberOfArgs a
  | WrongVariableType a
  | WrongReturnType a
  | WrongMainCall a
  | ExpectedArrType a
  | PropertyNotExisting Ident a
  | InheritanceCycle Ident a
  | OperationImpossible a
  | CustomError String a
  | UnknownSemanticError a

instance Show SemanticError where
  show (WrongMainDeclaration pos) =
    "SEMANTIC ERROR: Wrong main declaration" ++ showPos pos
  show (RedeclarationInScope (Ident name) pos1 pos2) =
    "SEMANTIC ERROR: " ++ name ++ " defined" ++ showPos (min pos1 pos2) ++ " and redefined" ++ showPos (max pos1 pos2)
  show (BuiltInRedeclaration (Ident name) pos) =
    "SEMANTIC ERROR: Built-in function '" ++ name ++ "' redefined" ++ showPos pos
  show (NoReturnStmt (Ident name) pos) =
    "SEMANTIC ERROR: No return statement in function '" ++ name ++ "' defined" ++ showPos pos
  show (VoidNotAllowed pos) =
    "SEMANTIC ERROR: Void usage not allowed" ++ showPos pos
  show (ClassNotDefined (Ident ident) pos) =
    "SEMANTIC ERROR: Class '" ++ ident ++ "' not defined" ++ showPos pos
  show (ClassRedefined (Ident ident) _) =
    "SEMANTIC ERROR: Class '" ++ ident ++ "' defined multiple times"
  show (IntOutOfBound num pos) =
    "SEMANTIC ERROR: Integer " ++ show num ++ " out of bound" ++ showPos pos
  show (WrongExpressionType pos) =
    "SEMANTIC ERROR: Wrong expression type" ++ showPos pos
  show (VariableNotDefined (Ident name) pos) =
    "SEMANTIC ERROR: Variable '" ++ name ++ "' not defined" ++ showPos pos
  show (FunctionNotDefined (Ident name) pos) =
    "SEMANTIC ERROR: Function '" ++ name ++ "' not defined" ++ showPos pos
  show (MethodNotDefined (Ident cName) (Ident fnName) pos) =
    "SEMANTIC ERROR: Method '" ++ fnName ++ "' in class '" ++ cName ++ "' not defined" ++ showPos pos
  show (WrongNumberOfArgs pos) =
    "SEMANTIC ERROR: Wrong number of arguments" ++ showPos pos
  show (WrongVariableType pos) =
    "SEMANTIC ERROR: Wrong variable type" ++ showPos pos
  show (WrongReturnType pos) =
    "SEMANTIC ERROR: Wrong return type" ++ showPos pos
  show (WrongMainCall pos) =
    "SEMANTIC ERROR: Wrong main call" ++ showPos pos
  show (ExpectedArrType pos) =
    "SEMANTIC ERROR: Expected array type" ++ showPos pos
  show (PropertyNotExisting (Ident name) pos) =
      "SEMANTIC ERROR: Property '" ++ name ++ "' not existing" ++ showPos pos
  show (InheritanceCycle (Ident name) _) =
      "SEMANTIC ERROR: Classes inheritance cycle with '" ++ name ++ "'"
  show (OperationImpossible pos) =
    "SEMANTIC ERROR: Cannot execute operation" ++ showPos pos
  show (CustomError s _) =
    "SEMANTIC ERROR: Custom error: " ++ s
  show (UnknownSemanticError pos) =
    "SEMANTIC ERROR: Unknown type check error" ++ showPos pos


type SemanticException = SemanticException' BNFC'Position

data SemanticException' a
  = StmtsNeverReached a
  | InfiniteLoop a
  | DivisionByZero a
  | UnknownSemanticException a

instance Show SemanticException where
  show (StmtsNeverReached pos) =
    "SEMANTIC EXCEPTION: Statements never reached" ++ showPos pos
  show (InfiniteLoop pos) =
    "SEMANTIC EXCEPTION: Infinite loop" ++ showPos pos
  show (DivisionByZero pos) =
    "SEMANTIC EXCEPTION: Division by zero" ++ showPos pos
  show (UnknownSemanticException pos) =
    "SEMANTIC EXCEPTION: Unknown type check exception" ++ showPos pos

-- helpers

showPos :: BNFC'Position -> String
showPos (Just (line, column)) = concat [" at line ", show line, ", column ", show column]
showPos _ = ""
