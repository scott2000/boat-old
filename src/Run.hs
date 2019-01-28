{-# LANGUAGE RecordWildCards #-}

module Run where

import AST
import Infer (TypeMap (mapTypes))

import Data.Maybe
import Control.Monad.State
import qualified Data.Map as Map

data PossibleValue = PossibleValue
  { valueExpr :: Typed Expr,
    valueInstances :: Map.Map Type (Typed Value) }

toPossibleValue :: Typed Expr -> PossibleValue
toPossibleValue expr = PossibleValue
  { valueExpr = expr,
    valueInstances = Map.empty }

getInstanceOfValue :: (Show a, TypeMap a) => Type -> Typed a -> Typed a
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

type RunMap = Map.Map Name PossibleValue
type RunState = StateT RunMap (Either String)

evaluateEntry :: Typed Name -> Env (Typed Expr) -> Either String (Typed Value, RunMap)
evaluateEntry name valDecls =
  evaluate name $ initialize valDecls Map.empty
  where
    initialize [] m = m
    initialize ((name, expr):xs) m =
      initialize xs (Map.insert name (toPossibleValue expr) m)

evaluate :: Typed Name -> RunMap -> Either String (Typed Value, RunMap)
evaluate name = runStateT $ getValue name

getValue :: Typed Name -> RunState (Typed Value)
getValue (name ::: ty) = do
  m <- get
  case Map.lookup name m of
    Nothing -> lift $ Left ("cannot find value with name `" ++ show name ++ "`")
    Just (PossibleValue {..}) ->
      case Map.lookup ty valueInstances of
        Nothing -> do
          val <- run $ getInstanceOfValue ty valueExpr
          modify $ \m ->
            let
              (PossibleValue {..}) = fromJust $ Map.lookup name m
              new = PossibleValue { valueInstances = Map.insert ty val valueInstances, .. }
            in
              Map.insert name new m
          return val
        Just val ->
          return val

run :: Typed Expr -> RunState (Typed Value)
run (expr ::: ty) =
  case expr of
    Val v -> return $ v ::: ty
    Id name -> getValue (name ::: ty)
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
    Panic [] -> lift $ Left emptyPanic
    Panic msg -> lift $ Left msg
    ICons name variant list -> do
      val <- sequence $ map run list
      return $ Cons name variant val ::: ty

runOrRec :: Typed Expr -> RunState (Either [Typed Value] (Typed Value))
runOrRec typedExpr@(expr ::: ty) =
  case expr of
    If i t e -> do
      (cond ::: _) <- run i
      case cond of
        Bool True -> runOrRec t
        Bool False -> runOrRec e
    Let (name ::: _) val expr -> do
      (v ::: _) <- run val
      runOrRec $ substitute name (Val v) expr
    Rec args -> Left <$> (sequence $ map run args)
    _ -> Right <$> run typedExpr

emptyPanic :: String
emptyPanic = "attempted to evaluate `panic`"

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
runCases allCases = go allCases
  where
    go [] ((v ::: ty):_) = lift $ Left ("invalid value for type " ++ show ty ++ ": " ++ show v)
    go ((ps, expr):cs) vs =
      case tryAllPatterns ps vs expr of
        Just expr -> do
          res <- runOrRec expr
          case res of
            Left args -> go allCases args
            Right expr -> return expr
        Nothing -> go cs vs

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
    (PCons n0 l0, Cons n n1 l1)
      | n0 == n.|.n1 -> tryAllPatterns l0 l1 expr
      | otherwise -> Nothing
    _ -> Nothing

embed :: Typed Value -> Typed Expr
embed (v ::: t) = Val v ::: t
