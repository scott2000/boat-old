{-# LANGUAGE RecordWildCards #-}

module AST
  ( Expr (..),
    Type (..),
    Typed (..),
    Value (..),
    Decls (..),
    Name (..),
    Env,
    OpEntry,
    emptyDecls,
    addValDecl,
    showValDecl,
    deps,
    countLocals,
    substitute,
    checkFunc,
    zipEnv,
    getOp,
    mkFuncTy,
    tIdVar,
    tUnit,
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
  deriving (Eq, Ord)

data Typed a = (:::)
  { valof :: a,
    typeof :: Type }
  deriving Eq

data Value
  = Unit
  | Nat Word64
  | Bool Bool
  | Func [Typed Name] (Typed Expr)
  deriving Eq

data Decls = Decls
  { valDecls :: Env (Typed Expr) }
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
  show Unit = "unit"
  show (Nat n) = show n
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Func xs expr) = "(\\" ++ unwords (map show xs) ++ " -> " ++ show expr ++ ")"

instance Show Name where
  show (Name s) = s

emptyDecls :: Decls
emptyDecls = Decls
  { valDecls = [] }

addValDecl :: (Name, Typed Expr) -> Decls -> Decls
addValDecl val Decls {..} = Decls { valDecls = val : valDecls, .. }

showValDecl :: (Name, Typed Expr) -> String
showValDecl (name, val ::: TAnon _) =
  "val " ++ show name ++ " = " ++ show val
showValDecl (name, val ::: ty) =
  "val " ++ show name ++ " : " ++ show ty ++ " = " ++ show val

deps :: Bool -> [Name] -> Typed Expr -> State (Set.Set Name) ()
deps lam env (expr ::: ty) =
  case expr of
    Val (Func params expr) ->
      if lam then
        deps lam (map valof params ++ env) expr
      else
        return ()
    Val _ -> return ()
    Id name ->
      if name `elem` env then
        return ()
      else
        modify (Set.insert name)
    Op _ a b -> deps lam env a >> deps lam env b
    App a b -> deps lam env a >> deps lam env b
    If i t e -> deps lam env i >> deps lam env t >> deps lam env e
    Let name val expr -> deps lam env val >> deps lam (valof name : env) expr

countLocals :: Typed Expr -> Env Int -> Env Int
countLocals (expr ::: _) env =
  case expr of
    Val (Func xs expr) ->
      let
        remove (x, _) = (x, 0)
        emptyEnv = map remove env
        toEnv (x ::: _) = (x, 0)
        env' = map toEnv xs ++ emptyEnv
        fix (x, 0) = (x, 0)
        fix (x, _) = (x, 1)
      in
        zipEnv (+) env $ map fix $ drop (length xs) $ countLocals expr env'
    Val _ -> env
    Id name ->
      addName name env
    Op _ a b ->
      countLocals b $ countLocals a env
    App a b ->
      countLocals b $ countLocals a env
    If i t e ->
      let
        env' = countLocals i env
        te = countLocals t env'
        ee = countLocals e env'
      in
        zipEnv max te ee
    Let (name ::: _) val expr ->
      let
        valLocals = countLocals val env
        env' = (name, 0) : valLocals
      in
        tail $ countLocals expr env'
  where
    addName name [] = []
    addName name ((e@(n, x)) : xs)
      | n == name = (n, x+1) : xs
      | otherwise = e : addName name xs

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
    b "&&" (&&)]
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

tIdVar :: String -> Type
tIdVar [] = error "type name cannot be empty"
tIdVar s =
  if head s `elem` ['A'..'Z'] then
    TId s
  else
    TVar s

tUnit :: Type
tUnit = TId "Unit"

tNat :: Type
tNat = TId "Nat"

tBool :: Type
tBool = TId "Bool"
