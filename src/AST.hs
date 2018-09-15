module AST
  ( Expr (..),
    Type (..),
    Typed (..),
    Value (..),
    Decl (..),
    Name (..),
    Env,
    OpEntry,
    declFromList,
    declToList,
    deps,
    countLocals,
    substitute,
    checkFunc,
    zipEnv,
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
  = Val Value                                   -- values
  | Id Name                                     -- identifiers
  | Op String (Typed Expr) (Typed Expr)         -- primitive operations
  | App (Typed Expr) (Typed Expr)               -- (a b)
  | If (Typed Expr) (Typed Expr) (Typed Expr)   -- (if a then b else c)
  | Let (Typed Name) (Typed Expr) (Typed Expr)  -- (let a = b in c)
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

data Value
  = Nat Word64
  | Bool Bool
  | Func [Typed Name] (Typed Expr)
  deriving Eq

data Decl
  = Decl Name (Typed Expr)
  deriving Eq

newtype Name
  = Name String
  deriving (Eq, Ord)

type Env a = [(Name, a)]

instance Show Expr where
  show (Val v) = show v
  show (Id name) = show name
  show (Op op a b) = "(" ++ show a ++ " " ++ op ++ " " ++ show b ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (If i t e) = "(if " ++ show i ++ " then " ++ show t ++ " else " ++ show e ++ ")"
  show (Let name val expr) = "(let " ++ show name ++ " = " ++ show val ++ " in " ++ show expr ++ ")"

instance Show Type where
  show (TAnon n) = "{" ++ show n ++ "}"
  show (TId s) = s
  show (TVar s) = s
  show (TFunc a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"

instance Show a => Show (Typed a) where
  show (x ::: _) = show x

instance Show Value where
  show (Nat n) = show n
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Func xs expr) = "(\\" ++ unwords (map show xs) ++ " -> " ++ show expr ++ ")"

instance Show Decl where
  show (Decl name (val ::: ty)) = "val " ++ show name ++ " : " ++ show ty ++ " = " ++ show val

instance Show Name where
  show (Name s) = s

declFromList :: Env (Typed Expr) -> [Decl]
declFromList = map (uncurry Decl)

declToList :: [Decl] -> Env (Typed Expr)
declToList = map (\(Decl n e) -> (n, e))

deps :: Bool -> [Name] -> Typed Expr -> State (Set.Set Name) ()
deps lam env (expr ::: ty) =
  case expr of
    Id name ->
      if name `elem` env then
        return ()
      else
        modify (Set.insert name)
    Op _ a b -> deps lam env a >> deps lam env b
    App a b -> deps lam env a >> deps lam env b
    If i t e -> deps lam env i >> deps lam env t >> deps lam env e
    Let name val expr -> deps lam env val >> deps lam (valof name : env) expr
    Val (Func params expr) ->
      if lam then
        deps lam (map valof params ++ env) expr
      else
        return ()
    _ -> return ()

countLocals :: [Name] -> Typed Expr -> Env Int -> Env Int
countLocals globals (expr ::: _) env =
  case expr of
    Val (Func xs expr) ->
      let
        params = map (\(x ::: _) -> (x, 0)) xs
        env' = params ++ env
      in
        drop (length xs) (countLocals globals expr env')
    Id name
      | name `elem` globals -> env
      | otherwise -> addName name env
    Op _ a b ->
      countLocals globals b (countLocals globals a env)
    App a b ->
      countLocals globals b (countLocals globals a env)
    If i t e ->
      let
        env' = countLocals globals i env
        te = countLocals globals t env'
        ee = countLocals globals e env'
      in
        zipEnv max te ee
    Let (name ::: _) val expr ->
      tail $ countLocals globals expr ((name, 0) : countLocals globals val env)
    _ -> env
  where
    addName name ((e@(n, x)):xs) =
      if n == name then
        (n, x+1):xs
      else
        e : addName name xs

substitute :: Name -> Value -> Typed Expr -> Typed Expr
substitute name value (expr ::: ty) =
  (::: ty) $ case expr of
    Val (Func xs expr) ->
      Val (Func xs (checkFunc xs name value expr))
    Val other -> Val other
    Id n
      | n == name -> Val value
      | otherwise -> Id n
    Op op a b ->
      Op op (substitute name value a) (substitute name value b)
    App a b ->
      App (substitute name value a) (substitute name value b)
    If i t e ->
      If (substitute name value i) (substitute name value t) (substitute name value e)
    Let (t@(n ::: _)) v expr
      | n == name -> Let t (substitute name value v) expr
      | otherwise -> Let t (substitute name value v) (substitute name value expr)

checkFunc :: [Typed Name] -> Name -> Value -> Typed Expr -> Typed Expr
checkFunc [] name value expr = substitute name value expr
checkFunc ((n ::: _):ns) name value expr
  | n == name = expr
  | otherwise = checkFunc ns name value expr

zipEnv :: (a -> b -> c) -> Env a -> Env b -> Env c
zipEnv _ [] [] = []
zipEnv f ((n, a):as) ((m, b):bs)
  | n == m = (n, f a b) : zipEnv f as bs

type OpEntry = (Type, Type, Value -> Value -> Either String Value)

opList :: [(String, OpEntry)]
opList =
  [ n "+" (+),
    n "-" (-),
    n "*" (*),
    n "/" quot,
    n "%" rem,
    -- n "^" (^),
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
        f (Nat a) (Nat b) = Right (Nat (op a b))
        f _ _ = Left ("invalid inputs for numeric operator `" ++ s ++ "`, expected two `Nat` arguments")
    c s op = (s, (tNat, tBool, f))
      where
        f (Nat a) (Nat b) = Right (Bool (op a b))
        f _ _ = Left ("invalid inputs for comparison operator `" ++ s ++ "`, expected two `Nat` arguments")
    b s op = (s, (tBool, tBool, f))
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
