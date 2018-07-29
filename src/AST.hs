module AST ( Expr (..), Type (..), LocalVar (..), OpEntry, eval, (!?), getOp, mkFuncTy ) where

import Data.Word

data Expr
  = Nat Word64
  | Bool Bool
  | Op String Expr Expr
  | App Expr Expr
  | Id LocalVar
  | Let String Expr Expr
  | If Expr Expr Expr
  | Func LocalVar [LocalVar] Expr
  deriving Eq

data LocalVar = (:::)
  { nameof :: String,
    typeof :: Type }
  deriving Eq

data Type
  = TVar Word64
  | TNat
  | TBool
  | TFunc Type Type
  deriving Eq

instance Show Expr where
  show (Nat n) = show n
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Op op a b) = "(" ++ show a ++ " " ++ op ++ " " ++ show b ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Id name) = show name
  show (Let name val expr) = "(let " ++ name ++ " = " ++ show val ++ " in " ++ show expr ++ ")"
  show (If i t e) = "(if " ++ show i ++ " then " ++ show t ++ " else " ++ show e ++ ")"
  show (Func x xs expr) = "(\\" ++ unwords (map show (x:xs)) ++ " -> " ++ show expr ++ ")"

instance Show LocalVar where
  show (x ::: _) = x

  -- FOR DEBUGGING
  -- show (x ::: (TVar _)) = x
  -- show (x ::: t) = "(" ++ x ++ " : " ++ show t ++ ")"

instance Show Type where
  show (TVar n) = "<" ++ show n ++ ">"
  show TNat = "Nat"
  show TBool = "Bool"
  show (TFunc a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"

eval :: [[(String, Expr)]] -> Expr -> Either String Expr
eval l (Op op a b) = do
  a <- eval l a
  (_, _, f) <- getOp op
  b <- eval l b
  f a b
eval l (App a b) = do
  a <- eval l a
  b <- eval l b
  case (a, b) of
    (Func x [] expr, param) -> do
      param <- eval l param
      eval ([(nameof x, param)]:l) expr
    (Func x (y:xs) expr, param) -> do
      param <- eval l param
      expr <- eval ([(nameof x, param)]:l) expr
      Right (Func y xs expr)
    (a, b) -> Left ("cannot apply `" ++ show b ++ "` to `" ++ show a ++ "`")
eval l (Id (name ::: _)) =
  case l !? name of
    Just x -> Right x
    Nothing -> Left ("cannot find value: `" ++ name ++ "`")
eval l (Let name val expr) = do
  val <- eval l val
  eval ([(name, val)]:l) expr
eval l (If i t e) = do
  i <- eval l i
  case i of
    Bool True -> eval l t
    Bool False -> eval l e
-- TODO: capture function values
eval _ x = Right x

(!?) :: Eq k => [[(k, v)]] -> k -> Maybe v
(!?) [] _ = Nothing
(!?) (list:rest) key =
  case find key list of
    Just v -> Just v
    Nothing -> rest !? key
  where
    find _ [] = Nothing
    find key ((k, v):rest)
      | k == key = Just v
      | otherwise = find key rest

type OpEntry = (Type, Type, Expr -> Expr -> Either String Expr)

opList :: [(String, OpEntry)]
opList =
  [ n "+" (+),
    n "-" (-),
    n "*" (*),
    n "/" quot,
    n "%" rem,
    n "^" (^),
    c "<" (<),
    c ">" (>),
    c "<=" (<=),
    c ">=" (>=),
    c "==" (==),
    c "!=" (/=),
    b "||" (||),
    b "&&" (&&) ]
  where
    n s op = (s, (TNat, TNat, f))
      where
        f (Nat a) (Nat b) = Right (Nat (op a b))
        f _ _ = Left ("invalid inputs for numeric operator `" ++ s ++ "`, expected two `Nat` arguments")
    c s op = (s, (TNat, TBool, f))
      where
        f (Nat a) (Nat b) = Right (Bool (op a b))
        f _ _ = Left ("invalid inputs for comparison operator `" ++ s ++ "`, expected two `Nat` arguments")
    b s op = (s, (TBool, TBool, f))
      where
        f (Bool a) (Bool b) = Right (Bool (op a b))
        f _ _ = Left ("invalid inputs for boolean operator `" ++ s ++ "`, expected two `Bool` arguments")

getOp :: String -> Either String OpEntry
getOp s =
  case lookup s opList of
    Just entry -> Right entry
    Nothing -> Left ("cannot find operator `" ++ s ++ "`")

mkFuncTy :: [Type] -> Type -> Type
mkFuncTy [] r = r
mkFuncTy (x:xs) r = TFunc x (mkFuncTy xs r)
