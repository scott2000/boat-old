module Infer (infer) where

import AST

import Data.Word
import Data.Maybe
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

type InferMap = Map.Map Word64 Type
type LocalSet = Set.Set String

type InferState = StateT (InferMap, LocalSet) (Either String)
type QuantifyState = State (InferMap, Int)

infer :: Typed Expr -> Either String (Typed Expr)
infer expr = do
  (m, s) <- execStateT (ty [] expr) (Map.empty, Set.empty)
  let simple_expr = mapTypes (simplify m) expr
  let (q, _) = execState (quantify (typeof simple_expr)) (Map.empty, 0)
  let final_expr = mapTypes (simplify q) simple_expr
  verifyTypes final_expr
  Right final_expr

letters :: String
letters = "abcdefghijklmnopqrstuvwxyz"

generic_name :: Int -> String
generic_name = helper 26 1
  where
    helper m s c =
      if c >= m then
        helper (m*26) (s+1) (c-m)
      else
        builder [] s c
    builder a 0 _ = a
    builder a s c =
      builder ((letters !! (rem c 26)) : a) (s-1) (div c 26)

quantify :: Type -> QuantifyState ()
quantify (TAnon a) = do
  (m, n) <- get
  case Map.lookup a m of
    Just x -> return ()
    Nothing -> do
      let name = generic_name n
      let var = TVar name
      put (Map.insert a var m, n+1)
quantify (TFunc a b) = quantify a >> quantify b
quantify _ = return ()

class TypeMap a where
  mapTypes :: (Type -> Type) -> a -> a
  verifyTypes :: a -> Either String ()

instance (Show a, TypeMap a) => TypeMap (Typed a) where
  mapTypes f (x ::: t) = (mapTypes f x ::: f t)

  verifyTypes (x ::: (TAnon _)) = do
    verifyTypes x
    Left ("cannot infer a concrete type for `" ++ show x ++ "`")
  verifyTypes (x ::: _) = verifyTypes x

instance TypeMap Name where
  mapTypes _ = id
  verifyTypes _ = Right ()

instance TypeMap Expr where
  mapTypes f (Op op a b) = Op op (mapTypes f a) (mapTypes f b)
  mapTypes f (App a b) = App (mapTypes f a) (mapTypes f b)
  mapTypes f (If i t e) = If (mapTypes f i) (mapTypes f t) (mapTypes f e)
  mapTypes f (Let name val expr) = Let (mapTypes f name) (mapTypes f val) (mapTypes f expr)
  mapTypes f (Func xs expr) = Func (map (mapTypes f) xs) (mapTypes f expr)
  mapTypes _ other = other

  verifyTypes (Op _ a b) = verifyTypes a >> verifyTypes b
  verifyTypes (App a b) = verifyTypes a >> verifyTypes b
  verifyTypes (If i t e) = verifyTypes i >> verifyTypes t >> verifyTypes e
  verifyTypes (Let name val expr) = verifyTypes name >> verifyTypes val >> verifyTypes expr
  verifyTypes (Func xs expr) = do
    sequence $ map verifyTypes xs
    verifyTypes expr
  verifyTypes _ = Right ()

ty :: [(Name, Type)] -> Typed Expr -> InferState Type
ty env (x ::: fin) = do
  case x of
    Lit (Nat _) -> unify fin tNat
    Lit (Bool _) -> unify fin tBool
    Id name ->
      case lookup name env of
        Just x -> unify fin x
        Nothing -> lift $ Left ("cannot find value: `" ++ show name ++ "`")
    Op op a b -> do
      a <- ty env a
      (t, r, _) <- lift $ getOp op
      b <- ty env b
      unify a t
      unify b t
      unify fin r
    App a b -> do
      a <- ty env a
      b <- ty env b
      unify a $ TFunc b fin
    If i t e -> do
      i <- ty env i
      unify i tBool
      t <- ty env t
      e <- ty env e
      unify t e
      unify fin t
    Let (name ::: ex) val expr -> do
      v <- ty env val
      unify v ex
      e <- ty ((name, v):env) expr
      unify fin e
    Func xs expr -> do
      let types = map (\(n ::: t) -> (n, t)) xs
      res <- ty (reverse types ++ env) expr
      unify fin $ mkFuncTy (map typeof xs) res
  return fin

simplify :: InferMap -> Type -> Type
simplify m (TAnon a) =
  case Map.lookup a m of
    Just n -> simplify m n
    Nothing -> TAnon a
simplify m (TFunc a b) = TFunc (simplify m a) (simplify m b)
simplify _ other = other

unify :: Type -> Type -> InferState ()
unify a b = do
  (m, _) <- get
  u (simplify m a) (simplify m b)
  where
    u (TAnon a) (TAnon b) =
      if a == b then
        return ()
      else
        inserTAnon a (TAnon b)
    u (TAnon a) other = inserTAnon a other
    u other (TAnon a) = inserTAnon a other
    u (TId a) (TId b) =
      if a == b then
        return ()
      else
        lift $ Left ("cannot unify named types `" ++ show a ++ "` and `" ++ show b ++ "`")
    u (TVar a) (TVar b) =
      if a == b then do
        (m, s) <- get
        put (m, Set.insert a s)
      else
        lift $ Left ("cannot unify type variables `" ++ show a ++ "` and `" ++ show b ++ "`")
    u (TFunc a0 b0) (TFunc a1 b1) = do
      unify a0 a1
      unify b0 b1
    u a b = lift $ Left ("cannot unify types `" ++ show a ++ "` and `" ++ show b ++ "`")

inserTAnon :: Word64 -> Type -> InferState ()
inserTAnon k v =
  if typeContains k v then
    lift $ Left ("infinitely recursive type constraint: " ++ show (TAnon k) ++ " = " ++ show v)
  else do
    (m, s) <- get
    put (Map.insert k v m, s)

typeContains :: Word64 -> Type -> Bool
typeContains v (TAnon a) = a == v
typeContains v (TFunc a b) = typeContains v a || typeContains v b
typeContains _ _ = False
