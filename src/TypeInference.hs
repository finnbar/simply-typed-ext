{--------------------------------------------------------------------------------------------------
                                Interactive Simply-Typed \-Calculus                                
                                       Michael Benjamin Gale                                       
--------------------------------------------------------------------------------------------------}

-- In this module we implement the type inference algorithm for the simply-typed lambda-calculus.

module TypeInference (
    TyEnv,
    infer
) where

{----------------------------------------------------------------------}
{-- Module Imports                                                    -}
{----------------------------------------------------------------------}

import Text.Printf (printf)
import Types
import AST

{----------------------------------------------------------------------}
{-- Error Messages                                                    -}
{----------------------------------------------------------------------}

errFunTy :: String
errFunTy = "\n\tExpected function of type (%s -> t),\n\tbut found object of type %s instead.\n" 

errObjTy :: String
errObjTy = "\n\tExpected object of type %s,\n\tbut found object of type %s instead.\n"

errFixTy :: String
errFixTy = "\n\tExpected function of type (t -> t) as the argument of fix,\n\tbut found object of type %s instead.\n" 

errUndef :: String
errUndef = "\n\tUnable to infer the type of `%s' because it is undefined.\n"
    
{----------------------------------------------------------------------}
{-- Type Inference                                                    -}
{----------------------------------------------------------------------}
    
-- A type environment associates variables with types.

type TyEnv = [(Variable, Type)]

-- Tests if the domain of a function type matches the type of an argument.

unify :: Type -> Type -> Either String Type
unify (FunTy pt rt) at | pt == at = Right rt
unify t             at            = Left $ printf errFunTy (show at) (show t)

ensure :: Type -> Type -> Either String Type
ensure x y | x == y    = Right x
           | otherwise = Left $ printf errObjTy (show y) (show x)

isFixFunction :: Type -> Either String Type
isFixFunction (FunTy pt rt) | pt == rt = Right pt
isFixFunction t                        = Left $ printf errFixTy (show t)

typeLookup :: Variable -> TyEnv -> Either String Type
typeLookup x env = case lookup x env of
    (Just t) -> Right t
    Nothing  -> Left $ printf errUndef x

-- Given an expression and a type environment, this function attempts to
-- infer the type of the expression. This is fairly standard for PCF.
-- For cost inference, we make some arbitrary decisions for testing purposes.
-- The interpreter performs substitution, so var lookup technically costs
-- nothing. However, in its place, application takes much longer (size of
-- subtree steps) since it has to check every element for a capture-avoiding
-- substitution, as well as performing the cost of the actual application.

infer :: Expr -> TyEnv -> Either String Type
-- Value lookup costs zero time.
infer (Val _)      _   = do return natType
-- This is a challenge, since it depends on the cost of the variable - it could
-- be a substitution from an earlier App (in which case, it is that cost), or a
-- definition lookup (in which case, it is the cost of lookup + cost of that
-- actual code). This will need a CostEnv.
infer (Var x)      env = do typeLookup x env
-- Abstractions cost the time of their internal code.
-- However, an abstraction with no application should cost zero time - so maybe
-- the best solution is to make abstractions cost zero time, but App costs the
-- inside of an abstraction as extra time.
infer (Abs x t e)  env = do t' <- infer e ((x,t) : env)
                            return (FunTy t t')
-- Succ, Pred, IsZero cost one time.
infer (Succ e)     env = do t <- infer e env
                            ensure t natType
infer (Pred e)     env = do t <- infer e env
                            ensure t natType
infer (IsZero e)   env = do t <- infer e env
                            ensure t natType
-- Uhhhhhhhhhhhhh I don't really know what to do here. Maybe there's a paper on
-- recursion and cost estimation? Especially as this is possibly unbounded.
infer (Fix f)      env = do t <- infer f env
                            isFixFunction t
-- Has the cost of f plus |f| to apply the capture-avoiding substitution.
-- Cost of x is added to a cost environment.
infer (App f x)    env = do ft <- infer f env
                            xt <- infer x env
                            unify ft xt
-- Time is time(c) + max(time(t), time(f)).
infer (Cond c t f) env = do ct <- infer c env
                            ensure ct natType
                            tt <- infer t env
                            ft <- infer f env
                            ensure tt ft

{--------------------------------------------------------------------------------------------------
                                            End of File                                            
--------------------------------------------------------------------------------------------------}  
