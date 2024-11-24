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

tMainFn :: Type
tMainFn = Fun BNFC'NoPosition tInt []

-- types mappers

argType :: Arg -> Type
argType (FnArg _ t _) = t

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
isRefType Arr {} = True
isRefType Ref {} = True
isRefType _ = False

-- miscellaneous

basicCompareTypes :: Type -> Type -> Bool
basicCompareTypes (Int _) (Int _) = True
basicCompareTypes (Str _) (Str _) = True
basicCompareTypes (Bool _) (Bool _) = True
basicCompareTypes (Void _) (Void _) = True
basicCompareTypes (Arr _ t1) (Arr _ t2) = basicCompareTypes t1 t2
basicCompareTypes _ _ = False

instantBoolExprValue :: Expr -> Maybe Bool
instantBoolExprValue (ELitTrue _) = Just True
instantBoolExprValue (ELitFalse _) = Just False
instantBoolExprValue (Not _ expr) = not <$> instantBoolExprValue expr
instantBoolExprValue (EAnd _ e1 e2) = (&&) <$> instantBoolExprValue e1 <*> instantBoolExprValue e2
instantBoolExprValue (EOr _ e1 e2) = (||) <$> instantBoolExprValue e1 <*> instantBoolExprValue e2
instantBoolExprValue _ = Nothing
