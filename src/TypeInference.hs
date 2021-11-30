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
import Types hiding (Succ)
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

unify :: Ty -> Ty -> Either String Ty
unify (FunTy pt rt) at | pt == at = Right rt
unify t             at            = Left $ printf errFunTy (show at) (show t)

ensure :: Ty -> Ty -> Either String Ty
ensure x y | x == y    = Right x
           | otherwise = Left $ printf errObjTy (show y) (show x)

isFixFunction :: Ty -> Either String Ty
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

-- IDEAS FOR NEXT STEPS: Lists, tuples, primitive map etc.
-- Let would be helpful to add, but seems to already be used (unless we add
-- let... in instead? replace let with def maybe?)

-- TODO: fix the wrong ones, then fix all calls of infer

infer :: Expr -> TyEnv -> Either String Type
-- Value lookup costs zero time.
infer (Val _)      _   = do return $ Type natType (Cost 0)
-- This is a challenge, since it depends on the cost of the variable - it could
-- be a substitution from an earlier App (in which case, it is that cost), or a
-- definition lookup (in which case, it is the cost of lookup + cost of that
-- actual code). This will need a CostEnv. (TODO)
infer (Var x)      env = do typeLookup x env
-- Abstractions cost the time of their internal code.
-- However, an abstraction with no application should cost zero time - so maybe
-- the best solution is to make abstractions cost zero time, but App costs the
-- inside of an abstraction as extra time.
infer (Abs x t e)  env = do Type t' c' <- infer e ((x,Type t (Cost 0)) : env)
                            return $ Type (FunTy t t') c' -- TODO: THIS IS WRONG
-- Succ, Pred, IsZero cost one time.
infer (Succ e)     env = do Type t c <- infer e env
                            ensure t natType
                            return $ Type t (costadd c (Cost 1))
infer (Pred e)     env = do Type t c <- infer e env
                            ensure t natType
                            return $ Type t (costadd c (Cost 1))
infer (IsZero e)   env = do Type t c <- infer e env
                            ensure t natType
                            return $ Type t (costadd c (Cost 1))
-- Uhhhhhhhhhhhhh I don't really know what to do here. Maybe there's a paper on
-- recursion and cost estimation? Especially as this is possibly unbounded.
infer (Fix f)      env = do Type t c <- infer f env
                            isFixFunction t
                            return $ Type t c
-- Has the cost of f plus |f| to apply the capture-avoiding substitution.
-- Cost of x is added to a cost environment.
infer (App f x)    env = do Type ft fc <- infer f env
                            Type xt xc <- infer x env
                            ty <- unify ft xt
                            return $ Type ty (fc `costadd` casCost f)
-- Time is time(c) + max(time(t), time(f)).
infer (Cond c t f) env = do Type ct cc <- infer c env
                            ensure ct natType
                            Type tt tc <- infer t env
                            Type ft fc <- infer f env
                            ensure tt ft
                            return $ Type tt $ cc `costadd` costmax tc fc

casCost :: Expr -> Cost
casCost (Val _) = Cost 1
casCost (Var _) = Cost 1
casCost (Abs x t e) = Cost 1 `costadd` casCost e
casCost (Succ e) = casCost e
casCost (Pred e) = casCost e
casCost (IsZero e) = casCost e
casCost (Fix f) = casCost f
casCost (App f x) = casCost f `costadd` casCost x
casCost (Cond c t f) = casCost c `costadd` casCost t `costadd` casCost f

{--------------------------------------------------------------------------------------------------
                                            End of File                                            
--------------------------------------------------------------------------------------------------}  
