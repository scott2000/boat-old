module AST
  ( Expr (..),
    Type (..),
    Typed (..),
    Literal (..),
    Value (..),
    Decl (..),
    Name (..),
    Env,
    OpEntry,
    declFromList,
    declToList,
    deps,
    eval,
    getOp,
    mkFuncTy,
    tNat,
    tBool )
  where

import Data.Word
import Data.List
import Control.Monad.State
import qualified Data.Set as Set

data Expr
  = Lit Literal                                 -- literals
  | Id Name                                     -- identifiers
  | Op String (Typed Expr) (Typed Expr)         -- primitive operations
  | App (Typed Expr) (Typed Expr)               -- (a b)
  | If (Typed Expr) (Typed Expr) (Typed Expr)   -- (if a then b else c)
  | Let (Typed Name) (Typed Expr) (Typed Expr)  -- (let a = b in c)
  | Func [Typed Name] (Typed Expr)              -- (\a -> b)
  deriving Eq

data Type
  = TAnon Word64
  | TId String
  | TVar String
  | TFunc Type Type
  deriving Eq

data Typed a = (:::)
  { valof :: a,
    typeof :: Type }
  deriving Eq

data Literal
  = Nat Word64
  | Bool Bool
  deriving Eq

data Value
  = VLit Literal
  | Closure (Env Value) [Name] (Typed Expr)
  deriving Eq

data Decl
  = Decl Name (Typed Expr)
  deriving Eq

newtype Name
  = Name String
  deriving (Eq, Ord)

type Env a = [(Name, a)]

instance Show Expr where
  show (Lit l) = show l
  show (Id name) = show name
  show (Op op a b) = "(" ++ show a ++ " " ++ op ++ " " ++ show b ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (If i t e) = "(if " ++ show i ++ " then " ++ show t ++ " else " ++ show e ++ ")"
  show (Let name val expr) = "(let " ++ show name ++ " = " ++ show val ++ " in " ++ show expr ++ ")"
  show (Func xs expr) = "(\\" ++ unwords (map show xs) ++ " -> " ++ show expr ++ ")"

instance Show Type where
  show (TAnon n) = "{" ++ show n ++ "}"
  show (TId s) = s
  show (TVar s) = s
  show (TFunc a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"

instance Show a => Show (Typed a) where
  show (x ::: _) = show x

instance Show Literal where
  show (Nat n) = show n
  show (Bool True) = "true"
  show (Bool False) = "false"

instance Show Value where
  show (VLit l) = show l
  show (Closure [] _ _) = "<function>"
  show (Closure _ _ _) = "<closure>"

instance Show Decl where
  show (Decl name (val ::: ty)) = "val " ++ show name ++ " : " ++ show ty ++ " = " ++ show val

instance Show Name where
  show (Name s) = s

declFromList :: Env (Typed Expr) -> [Decl]
declFromList = map (uncurry Decl)

declToList :: [Decl] -> Env (Typed Expr)
declToList = map (\(Decl n e) -> (n, e))

deps :: [Name] -> Typed Expr -> State (Set.Set Name) ()
deps env (expr ::: ty) =
  case expr of
    Id name ->
      if name `elem` env then
        return ()
      else
        modify (Set.insert name)
    Op _ a b -> deps env a >> deps env b
    App a b -> deps env a >> deps env b
    If i t e -> deps env i >> deps env t >> deps env e
    Let name val expr -> deps env val >> deps (valof name : env) expr
    Func params expr -> deps (map valof params ++ env) expr
    _ -> return ()

eval :: Env Value -> Typed Expr -> Either String Value
eval env (expr ::: ty) =
  case expr of
    Lit l -> Right (VLit l)
    Id name ->
      case lookup name env of
        Just x -> Right x
        Nothing -> Left ("cannot find value: `" ++ show name ++ "`")
    Op op a b -> do
      a <- eval env a
      (_, _, f) <- getOp op
      b <- eval env b
      f a b
    App a b -> do
      a <- eval env a
      b <- eval env b
      applyValue a b
    If i t e -> do
      i <- eval env i
      case i of
        VLit (Bool True) -> eval env t
        VLit (Bool False) -> eval env e
    Let (name ::: _) val expr -> do
      val <- eval env val
      eval ((name, val):env) expr
    Func xs expr ->
      Right (Closure env (map valof xs) expr)

applyValue :: Value -> Value -> Either String Value
applyValue (Closure env (x:xs) expr) param =
  let new_env = (x, param):env in
  if null xs then
    eval new_env expr
  else
    Right (Closure new_env xs expr)

type OpEntry = (Type, Type, Value -> Value -> Either String Value)

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
    n s op = (s, (tNat, tNat, f))
      where
        f (VLit (Nat a)) (VLit (Nat b)) = Right (VLit (Nat (op a b)))
        f _ _ = Left ("invalid inputs for numeric operator `" ++ s ++ "`, expected two `Nat` arguments")
    c s op = (s, (tNat, tBool, f))
      where
        f (VLit (Nat a)) (VLit (Nat b)) = Right (VLit (Bool (op a b)))
        f _ _ = Left ("invalid inputs for comparison operator `" ++ s ++ "`, expected two `Nat` arguments")
    b s op = (s, (tBool, tBool, f))
      where
        f (VLit (Bool a)) (VLit (Bool b)) = Right (VLit (Bool (op a b)))
        f _ _ = Left ("invalid inputs for boolean operator `" ++ s ++ "`, expected two `Bool` arguments")

getOp :: String -> Either String OpEntry
getOp s =
  case lookup s opList of
    Just entry -> Right entry
    Nothing -> Left ("cannot find operator `" ++ s ++ "`")

mkFuncTy :: [Type] -> Type -> Type
mkFuncTy [] r = r
mkFuncTy (x:xs) r = TFunc x (mkFuncTy xs r)

tyString :: String -> Type
tyString [] = error "type name cannot be empty"
tyString s =
  if head s `elem` ['A'..'Z'] then
    TId s
  else
    TVar s

tNat :: Type
tNat = TId "Nat"

tBool :: Type
tBool = TId "Bool"
