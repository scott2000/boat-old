{-# LANGUAGE RecordWildCards #-}

module Run (getInstanceOfValue, evaluateAll, evaluate, embed) where

import AST
import Infer (TypeMap (mapTypes))

import Data.Maybe
import Data.List
import Control.Monad.State
import qualified Data.Map as Map

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
    subs (TApp a b) = TApp (subs a) (subs b)
    subs other = other
    matchTypes m target (TVar v)
      | Map.member v m = m
      | otherwise    = Map.insert v target m
    matchTypes m (TApp a0 b0) (TApp a1 b1) =
      matchTypes (matchTypes m a0 a1) b0 b1
    matchTypes m _ _ = m

type RunState = StateT (Map.Map Name PossibleValue) (Either String)

evaluateAll :: Env (Typed Expr) -> Env DataDecl -> Either String (Env (Typed Value))
evaluateAll valDecls dataDecls =
  evalStateT (helper $ reverse valDecls)
  $ initialize valDecls
  $ Map.map Evaluated
  $ Map.fromList
  $ concat
  $ map constructorsForData dataDecls
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
    Val v -> return $ v ::: ty
    Id name -> getInstanceOfValue ty <$> getValue name
    Op op a b -> do
      (_, r, f) <- lift $ getOp op
      (a ::: _) <- run a
      (b ::: _) <- run b
      (::: r) <$> lift (f a b)
    App a b -> do
      x <- run b
      f <- run a
      funApp f x
    If i t e -> do
      (cond ::: _) <- run i
      case cond of
        Bool True -> run t
        Bool False -> run e
    Let (name ::: _) val expr -> do
      (v ::: _) <- run val
      run $ substitute name (Val v) expr
    Match exprs cases ->
      sequence (map run exprs) >>= runCases cases
    Panic [] -> lift $ Left "attempted to evaluate `panic`"
    Panic msg -> lift $ Left msg
    ICons name variant list -> do
      val <- sequence $ map run list
      return $ Cons name variant val ::: ty

funApp :: Typed Value -> Typed Value -> RunState (Typed Value)
funApp (f ::: fty) (x ::: _) =
  case f of
    Func [(name ::: _)] expr ->
      run $ substitute name (Val x) expr
    Func ((name ::: _):xs) expr ->
      case fty of
        TFunc _ r ->
          return (Func xs (checkFunc xs name (Val x) expr) ::: r)
        _ ->
          lift $ Left ("application to non-function type: " ++ show fty)

runCases :: [MatchCase] -> [Typed Value] -> RunState (Typed Value)
runCases [] vs = lift $ Left ("no pattern matches for values: " ++ intercalate " " (map show vs))
runCases ((ps, expr):cs) vs =
  case tryAllPatterns ps vs expr of
    Just expr -> run expr
    Nothing -> runCases cs vs

tryAllPatterns :: [Typed Pattern] -> [Typed Value] -> Typed Expr -> Maybe (Typed Expr)
tryAllPatterns [] [] expr = Just expr
tryAllPatterns (p:ps) (v:vs) expr =
  tryPattern p v expr >>= tryAllPatterns ps vs
tryAllPatterns _ _ _ = Nothing

tryPattern :: Typed Pattern -> Typed Value -> Typed Expr -> Maybe (Typed Expr)
tryPattern p v expr =
  case (valof p, valof v) of
    (PAny Nothing, _) ->
      Just expr
    (PAny (Just name), v) ->
      Just $ substitute name (Val v) expr
    (PNat n0, Nat n1)
      | n0 == n1 -> Just expr
      | otherwise -> Nothing
    (PBool b0, Bool b1)
      | b0 == b1 -> Just expr
      | otherwise -> Nothing
    (PCons n0 l0, Cons _ n1 l1)
      | n0 == n1 -> tryAllPatterns l0 l1 expr
      | otherwise -> Nothing
    _ -> error ("impossible pattern and value: " ++ show p ++ " = " ++ show v)

embed :: Typed Value -> Typed Expr
embed (v ::: t) = Val v ::: t
