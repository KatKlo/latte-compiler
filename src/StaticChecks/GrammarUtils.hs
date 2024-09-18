module StaticChecks.GrammarUtils where

import Grammar.AbsLatte

-- pre-defined types

tInt :: Type
tInt = Int BNFC'NoPosition

tStr :: Type
tStr = Str BNFC'NoPosition

tBool :: Type
tBool = Bool BNFC'NoPosition

tVoid :: Type
tVoid = Void BNFC'NoPosition

-- types mappers

argType :: Arg -> Type
argType (FunArg _ t _) = t

className :: ClassDef -> Ident
className (ClassFinDef _ ident _) = ident
className (ClassExtDef _ ident _ _) = ident

classParent :: ClassDef -> Maybe Ident
classParent (ClassExtDef _ _ pIdent _) = Just pIdent
classParent _ = Nothing

classBody :: ClassDef -> [CStmt]
classBody (ClassFinDef _ _ body) = body
classBody (ClassExtDef _ _ _ body) = body

-- types checks

isOrdType :: Type -> Bool
isOrdType (Int _) = True
isOrdType (Str _) = True
isOrdType _ = False

isEqType :: Type -> Bool
isEqType (Int _) = True
isEqType (Str _) = True
isEqType (Bool _) = True
isEqType t = isRefType t

isAddType :: Type -> Bool
isAddType (Int _) = True
isAddType (Str _) = True
isAddType _ = False

isRefType :: Type -> Bool
isRefType Class {} = True
isRefType Arr {} = True
isRefType Ref {} = True
isRefType _ = False

-- todo: fix asigning to arr.length
isAssignExpr :: Expr -> Bool
isAssignExpr EVar {} = True
isAssignExpr EArrGet {} = True
isAssignExpr EFieldGet {} = True
isAssignExpr _ = False

-- miscellaneous

basicCompareTypes :: Type -> Type -> Bool
basicCompareTypes (Int _) (Int _) = True
basicCompareTypes (Str _) (Str _) = True
basicCompareTypes (Bool _) (Bool _) = True
basicCompareTypes (Void _) (Void _) = True
basicCompareTypes (Arr _ t1) (Arr _ t2) = basicCompareTypes t1 t2
basicCompareTypes (Class _ s1) (Class _ s2) = s1 == s2
basicCompareTypes _ _ = False

instantBoolExprValue :: Expr -> Maybe Bool
instantBoolExprValue (ELitTrue _) = Just True
instantBoolExprValue (ELitFalse _) = Just False
instantBoolExprValue (Not _ expr) = not <$> instantBoolExprValue expr
instantBoolExprValue (EAnd _ e1 e2) = (&&) <$> instantBoolExprValue e1 <*> instantBoolExprValue e2
instantBoolExprValue (EOr _ e1 e2) = (||) <$> instantBoolExprValue e1 <*> instantBoolExprValue e2
instantBoolExprValue _ = Nothing
