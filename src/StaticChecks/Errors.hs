{-# LANGUAGE FlexibleInstances #-}

module StaticChecks.Errors where

import Grammar.AbsLatte
import Data.List (intercalate)
import StaticChecks.GrammarUtils

type SemanticError = SemanticError' BNFC'Position

data SemanticError' a
  = WrongMainDeclaration a
  | RedeclarationInScope Ident a a
  | BuiltInRedeclaration Ident a
  | MissingReturnStmt Ident a
  | VoidNotAllowed a
  | IntOutOfBound Integer a
  | WrongExpressionType Type Type a
  | VariableNotDefined Ident a
  | FunctionNotDefined Ident a
  | WrongNumberOfArgs a
  | WrongVariableType a
  | ReturnValueExpected a
  | ExpectedVRet a
  | MainCallNotAllowed a
  | ExpectedArrType a
  | OperationImpossible a
  | DiffOperandTypes Type Type a
  | CannotMakeOpOnType String Type a
  | UnknownSemanticError a

instance Show SemanticError where
  show (WrongMainDeclaration pos) =
    "SEMANTIC ERROR: Wrong main declaration" ++ showPos pos ++ " expected type: " ++ showType tMainFn
  show (RedeclarationInScope (Ident name) pos1 pos2) =
    "SEMANTIC ERROR: " ++ name ++ " defined" ++ showPos (min pos1 pos2) ++ " and redefined" ++ showPos (max pos1 pos2)
  show (BuiltInRedeclaration (Ident name) pos) =
    "SEMANTIC ERROR: Built-in function '" ++ name ++ "' redefined" ++ showPos pos
  show (MissingReturnStmt (Ident name) pos) =
    "SEMANTIC ERROR: No return statement in function '" ++ name ++ "' defined" ++ showPos pos
  show (VoidNotAllowed pos) =
    "SEMANTIC ERROR" ++ showPos pos ++ ": Void usage not allowed"
  show (IntOutOfBound num pos) =
    "SEMANTIC ERROR" ++ showPos pos ++ ": Integer " ++ show num ++ " out of bound"
  show (WrongExpressionType ex ev pos) =
    "SEMANTIC ERROR: Wrong expression type (expected: " ++ showType ex ++ "; got: " ++ showType ev ++ ")" ++ showPos pos
  show (VariableNotDefined (Ident name) pos) =
    "SEMANTIC ERROR" ++ showPos pos ++ ": Variable '" ++ name ++ "' not defined"
  show (FunctionNotDefined (Ident name) pos) =
    "SEMANTIC ERROR" ++ showPos pos ++ ": Function '" ++ name ++ "' not defined"
  show (WrongNumberOfArgs pos) =
    "SEMANTIC ERROR: Wrong number of arguments" ++ showPos pos
  show (WrongVariableType pos) =
    "SEMANTIC ERROR: Wrong variable type" ++ showPos pos
  show (ReturnValueExpected pos) =
    "SEMANTIC ERROR: Expected value to return" ++ showPos pos
  show (ExpectedVRet pos) =
    "SEMANTIC ERROR: No value is expected to be returned" ++ showPos pos
  show (MainCallNotAllowed pos) =
    "SEMANTIC ERROR" ++ showPos pos ++ ": Explicit main call is not allowed"
  show (ExpectedArrType pos) =
    "SEMANTIC ERROR" ++ showPos pos ++ ": Expected array type (cannot be null)"
  show (OperationImpossible pos) =
    "SEMANTIC ERROR: Cannot execute operation" ++ showPos pos
  show (DiffOperandTypes t1 t2 pos) =
    "SEMANTIC ERROR: Different types of operands (" ++ showType t1 ++ ", " ++ showType t2 ++ ")" ++ showPos pos
  show (CannotMakeOpOnType op t pos) =
    "SEMANTIC ERROR" ++ showPos pos ++ ": Cannot make " ++ op ++ " operation on " ++ showType t
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

showType :: Type -> String
showType Int {} = "integer"
showType Str {} = "string"
showType Bool {} = "boolean"
showType Void {} = "void"
showType (Arr _ t) = showType t ++ "[]"
showType (Fun _ t args) = "fn (" ++ (intercalate ", " (map showType args)) ++ ") -> " ++ showType t
showType (Ref _ (Void _)) = "null"
showType (Ref _  t) = "(" ++ showType t ++ ")null"
