{--------------------------------------------------------------------------------------------------
                                Interactive Simply-Typed \-Calculus                                
                                       Michael Benjamin Gale                                       
--------------------------------------------------------------------------------------------------}

-- In this module we define the type system of the simply-typed lambda-calculus.

module Types where

{----------------------------------------------------------------------}
{-- Type System                                                       -}
{----------------------------------------------------------------------}
    
-- A type name is just a string of characters.
    
type TyName = String

data Nat = Zero
         | Succ Nat

natType :: Ty
natType = ConTy "Nat"

funType :: Ty
funType = FunTy natType natType

-- Types can either be concrete types such as "Nat" or they can be function
-- types with a domain and codomain.

data Ty = ConTy TyName
          | FunTy Ty Ty
          deriving Eq

-- We create an instance of the Show type-class for the Type data type so
-- that we can show the types of expressions.

instance Show Ty where
    show (ConTy n)   = n
    show (FunTy d c) = "(" ++ show d ++ " -> " ++ show c ++ ")"

-- Costs are numbers, functions of input size or Infinity.
-- NOTE: May need negative values for memory use etc., if we get that far.

data Cost = Cost Int | Inf
    deriving (Show, Eq)

instance Ord Cost where
    Inf    <= Inf    = True
    Inf    <= c      = False
    c      <= Inf    = True
    Cost x <= Cost y = x <= y

costadd :: Cost -> Cost -> Cost
costadd Inf c = Inf
costadd c Inf = Inf
costadd (Cost x) (Cost y) = Cost $ x + y

costmax :: Cost -> Cost -> Cost
costmax x y | x > y     = x
            | otherwise = y

data Type = Type Ty Cost
    deriving (Show, Eq)

{--------------------------------------------------------------------------------------------------
                                            End of File                                            
--------------------------------------------------------------------------------------------------}  