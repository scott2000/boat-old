module Run (getInstanceOfValue, evaluateAll, evaluate, embed) where

import AST
import Infer (TypeMap (mapTypes))

import Data.Word
import Data.Maybe
import Data.List
import Data.Graph
import Control.Applicative
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

data PossibleValue
  = Unevaluated (Typed Expr)
  | Evaluated (Typed Value)
  | InProgress

getInstanceOfValue :: Type -> Typed Value -> Typed Value
getInstanceOfValue targetTy val =
  mapTypes subs val
  where
    subsMap = matchTypes Map.empty targetTy (typeof val)
    subs (TVar v) = fromJust (Map.lookup v subsMap)
    subs (TFunc a b) = TFunc (subs a) (subs b)
    subs other = other
    matchTypes m target (TVar v)
      | Map.member v m = m
      | otherwise    = Map.insert v target m
    matchTypes m (TFunc a0 b0) (TFunc a1 b1) =
      matchTypes (matchTypes m a0 a1) b0 b1
    matchTypes m _ _ = m

type RunState = StateT (Map.Map Name PossibleValue) (Either String)

evaluateAll :: Env (Typed Expr) -> Either String (Env (Typed Value))
evaluateAll env = evalStateT (helper (reverse env)) (initialize env Map.empty)
  where
    initialize [] m = m
    initialize ((name, expr):xs) m =
      initialize xs (Map.insert name (Unevaluated expr) m)

    helper [] = return []
    helper ((name, expr):xs) = do
      m <- get
      v <- case Map.lookup name m of
        Just (Evaluated v) -> return v
        _ -> run expr
      rest <- helper xs
      return ((name, v) : rest)

evaluate :: Env (Typed Value) -> Typed Expr -> Either String (Typed Value)
evaluate = error "unimplemented"

getValue :: Name -> RunState (Typed Value)
getValue name = do
  m <- get
  case Map.lookup name m of
    Nothing -> lift $ Left ("cannot find top-level value with name `" ++ show name ++ "`")
    Just (Unevaluated expr) -> do
      res <- run expr
      put (Map.insert name (Evaluated res) m)
      return res
    Just (Evaluated val) -> return val
    Just InProgress -> lift $ Left ("cannot evaluate recursive top-level value `" ++ show name ++ "`")

run :: Typed Expr -> RunState (Typed Value)
run (expr ::: ty) =
  case expr of
    Val v -> return (v ::: ty)
    Id name -> (getInstanceOfValue ty) <$> getValue name
    Op op a b -> do
      (_, r, f) <- lift $ getOp op
      (a ::: _) <- run a
      (b ::: _) <- run b
      (::: r) <$> lift (f a b)
    App a b -> do
      f <- run a
      x <- run b
      funApp f x
    If i t e -> do
      (cond ::: _) <- run i
      case cond of
        Bool False -> run e
        _ -> run t
    Let (name ::: _) val expr -> do
      (v ::: _) <- run val
      run $ substitute name v expr

funApp :: Typed Value -> Typed Value -> RunState (Typed Value)
funApp (f ::: fty) (x ::: _) =
  case f of
    Func [(name ::: _)] expr ->
      run $ substitute name x expr
    Func ((name ::: _):xs) expr ->
      case fty of
        TFunc _ r ->
          return (Func xs (checkFunc xs name x expr) ::: r)

embed :: Typed Value -> Typed Expr
embed (v ::: t) = Val v ::: t