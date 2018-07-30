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

infer :: Expr -> Either String (Expr, Type)
infer expr = do
  (ty, (m, s)) <- runStateT (ty [] expr) (Map.empty, Set.empty)
  let simple_expr = mapLocals (mapType $ simplify m) expr
  let simple_ty = simplify m ty
  let (final_ty, (q, _)) = runState (quantify simple_ty) (Map.empty, 0)
  let final_expr = mapLocals (mapType $ simplify q) simple_expr
  verify final_expr
  Right (final_expr, final_ty)

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

quantify :: Type -> QuantifyState Type
quantify (TAnon a) = do
  (m, n) <- get
  case Map.lookup a m of
    Just x -> return x
    Nothing -> do
      let name = generic_name n
      let var = TVar name
      put (Map.insert a var m, n+1)
      return var
quantify (TFunc a b) = do
  a <- quantify a
  b <- quantify b
  return (TFunc a b)
quantify other = return other

verify :: Expr -> Either String ()
verify (Op _ a b) = verify a >> verify b
verify (App a b) = verify a >> verify b
verify (Id a) = verifyLocal a
verify (Let _ a b) = verify a >> verify b
verify (If a b c) = verify a >> verify b >> verify c
verify (Func x xs expr) = do
  verifyLocal x
  sequence $ map verifyLocal xs
  verify expr
verify _ = return ()

verifyLocal :: LocalVar -> Either String ()
verifyLocal (n ::: (TAnon a)) =
  Left ("cannot infer a concrete type for `" ++ n ++ "`")
verifyLocal _ = Right ()

mapLocals :: (LocalVar -> LocalVar) -> Expr -> Expr
mapLocals f (Op op a b) = Op op (mapLocals f a) (mapLocals f b)
mapLocals f (App a b) = App (mapLocals f a) (mapLocals f b)
mapLocals f (Id a) = Id (f a)
mapLocals f (Let name val expr) = Let name (mapLocals f val) (mapLocals f expr)
mapLocals f (If i t e) = If (mapLocals f i) (mapLocals f t) (mapLocals f e)
mapLocals f (Func x xs expr) = Func (f x) (map f xs) (mapLocals f expr)
mapLocals _ other = other

mapType :: (Type -> Type) -> LocalVar -> LocalVar
mapType f (n ::: t) = (n ::: f t)

ty :: [[(String, Type)]] -> Expr -> InferState Type
ty _ (Nat _) = return tNat
ty _ (Bool _) = return tBool
ty l (Op op a b) = do
  a <- ty l a
  (t, r, _) <- lift $ getOp op
  b <- ty l b
  unify a t
  unify b t
  return r
ty l (App a b) = do
  a <- ty l a
  b <- ty l b
  (m, _) <- get
  case simplify m a of
    TFunc t r -> do
      unify b t
      return r
    other -> lift $ Left ("cannot apply to non-function type `" ++ show other ++ "`")
ty l (Id (name ::: t)) =
  case l !? name of
    Just x -> do
      unify t x
      return x
    Nothing -> lift $ Left ("cannot find value: `" ++ name ++ "`")
ty l (Let name val expr) = do
  v <- ty l val
  ty ([(name, v)]:l) expr
ty l (If i t e) = do
  i <- ty l i
  unify i tBool
  t <- ty l t
  e <- ty l e
  unify t e
  return t
ty l (Func x xs expr) = do
  let types = map (\(n ::: t) -> (n, t)) (x:xs)
  res <- ty (types:l) expr
  return $ mkFuncTy (map typeof (x:xs)) res

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
inserTAnon k v = do
  (m, s) <- get
  put (Map.insert k v m, s)
