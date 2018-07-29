module Infer (infer) where

import AST

import Data.Word
import Data.Maybe
import Control.Monad.State
import qualified Data.Map as Map

type InferState = StateT (Map.Map Word64 Type) (Either String)

infer :: Expr -> Either String (Expr, Type)
infer expr = evalStateT i Map.empty
  where
    i = do
      ty <- ty [] expr
      expr <- doInfer expr
      ty <- simplify ty
      return (expr, ty)

doInfer :: Expr -> InferState Expr
doInfer (Op op a b) = do
  a <- doInfer a
  b <- doInfer b
  return (Op op a b)
doInfer (App a b) = do
  a <- doInfer a
  b <- doInfer b
  return (App a b)
doInfer (Id (name ::: ty)) = do
  ty <- simplify ty
  return (Id (name ::: ty))
doInfer (Let name val expr) = do
  val <- doInfer val
  expr <- doInfer expr
  return (Let name val expr)
doInfer (If i t e) = do
  i <- doInfer i
  t <- doInfer t
  e <- doInfer e
  return (If i t e)
doInfer (Func x xs expr) = do
  x <- idInfer x
  xs <- sequence $ map idInfer xs
  expr <- doInfer expr
  return (Func x xs expr)
  where
    idInfer (name ::: ty) = do
      ty <- simplify ty
      return (name ::: ty)
doInfer other = return other

ty :: [[(String, Type)]] -> Expr -> InferState Type
ty _ (Nat _) = return TNat
ty _ (Bool _) = return TBool
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
  s <- simplify a
  case s of
    TFunc t r -> do
      unify b t
      return r
    other -> lift $ Left ("cannot apply to non-function type `" ++ show s ++ "`")
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
  unify i TBool
  t <- ty l t
  e <- ty l e
  unify t e
  return t
ty l (Func x xs expr) = do
  let types = map (\(n ::: t) -> (n, t)) (x:xs)
  res <- ty (types:l) expr
  return $ mkFuncTy (map typeof (x:xs)) res

simplify :: Type -> InferState Type
simplify (TVar a) = do
  m <- get
  case Map.lookup a m of
    Just n -> simplify n
    Nothing -> return (TVar a)
simplify (TFunc a b) = do
  a <- simplify a
  b <- simplify b
  return (TFunc a b)
simplify other = return other

unify :: Type -> Type -> InferState ()
unify a b = do
  a <- simplify a
  b <- simplify b
  u a b
  where
    u (TVar a) (TVar b) =
      if a == b then
        return ()
      else
        insertVar a (TVar b)
    u (TVar a) other = insertVar a other
    u other (TVar a) = insertVar a other
    u TNat TNat = return ()
    u TBool TBool = return ()
    u (TFunc a0 b0) (TFunc a1 b1) = do
      unify a0 a1
      unify b0 b1
    u a b = lift $ Left ("cannot unify types `" ++ show a ++ "` and `" ++ show b ++ "`")

insertVar :: Word64 -> Type -> InferState ()
insertVar k v = do
  m <- get
  put $ Map.insert k v m
