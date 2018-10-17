module Infer (inferAll, simplify, TypeMap (mapTypes)) where

import AST

import Data.Word
import Data.Maybe
import Data.List
import Data.Graph
import Control.Applicative
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

type InferMap = Map.Map Word64 Type

data InferData = Inf
  { getAnonMap :: InferMap,
    getVarCount :: Word64 }
  deriving Show

newInferData :: Word64 -> InferData
newInferData c = Inf Map.empty c

insertAnon :: Word64 -> Type -> InferData -> InferData
insertAnon n t (Inf m c) = Inf (Map.insert n t m) c

getNewVar :: InferState Word64
getNewVar = do
  Inf m c <- get
  put $ Inf m (c+1)
  return c

data Globals = Globals
  { globalVariables :: Map.Map Name Type,
    inferenceVariables :: Map.Map Name Type }
  deriving Show

type InferState = StateT InferData (Either String)
type QuantifyState = State (InferMap, Int)

type DepEntry = (Name, Set.Set Name)
type MultiDepEntry = (Set.Set Name, Set.Set Name)

inferAll :: Word64 -> Env (Typed Expr) -> Either String (Env (Typed Expr))
inferAll _ [] = Right []
inferAll count globals = do
  let allDeps = depList True globals
  let grouped = groupCycles allDeps
  let red = removeRedundancies grouped
  let sorted = tsort red
  let values = map (flip getAllValues globals) sorted
  (count, inferred) <- inferEach count values Map.empty []
  quantified <- sequence $ map (quantifyVerify 0) inferred
  let funcDeps = depList False quantified
  checkRecursiveDeps funcDeps
  return quantified
  where
    inferEach :: Word64
              -> [Env (Typed Expr)]
              -> Map.Map Name Type
              -> Env (Typed Expr)
              -> Either String (Word64, Env (Typed Expr))
    inferEach count [] _ l = Right (count, l)
    inferEach count (env:xs) m l = do
      (count, env) <- infer m env count
      inferEach count xs (Map.union m $ Map.fromList $ map typeNameList env) (env++l)
    quantifyVerify :: Int -> (Name, Typed Expr) -> Either String (Name, Typed Expr)
    quantifyVerify count (name, expr) =
      let
        locals = execState (getLocals expr) Set.empty
        (m, count') = execState (quantify locals (typeof expr)) (Map.empty, count)
        simplified = mapTypes (simplify m) expr
      in do
        verifyTypes simplified
        return (name, simplified)

infer :: Map.Map Name Type -> Env (Typed Expr) -> Word64 -> Either String (Word64, Env (Typed Expr))
infer m env count = do
  (s, d) <- runStateT helper (newInferData count)
  return (getVarCount d, s)
  where
    convertTypes :: (Name, Typed a) -> (Name, Type)
    convertTypes (name, typed) = (name, typeof typed)
    globals :: Globals
    globals = Globals m (Map.fromList (map typeNameList env))
    checkTypes :: (Name, Typed Expr) -> InferState Type
    checkTypes (name, expr) = ty globals [] expr
    simplifyTypes :: (Name, Typed Expr) -> InferState (Name, Typed Expr)
    simplifyTypes (name, expr) = do
      m <- gets getAnonMap
      return (name, mapTypes (simplify m) expr)
    helper :: InferState (Env (Typed Expr))
    helper = do
      sequence_ $ map checkTypes env
      sequence $ map simplifyTypes env

typeNameList :: (a, Typed b) -> (a, Type)
typeNameList (a, b) = (a, typeof b)

groupCycles :: [DepEntry] -> [MultiDepEntry]
groupCycles = map from . stronglyConnCompR . into
  where
    into :: [DepEntry] -> [((), Name, [Name])]
    into [] = []
    into ((name, deps):xs) = ((), name, Set.toList deps) : into xs
    from :: SCC ((), Name, [Name]) -> MultiDepEntry
    from (AcyclicSCC ((), name, deps)) = (Set.singleton name, Set.fromList deps)
    from (CyclicSCC list) = fromCyc (Set.empty, Set.empty) list
    fromCyc :: MultiDepEntry -> [((), Name, [Name])] -> MultiDepEntry
    fromCyc entry [] = entry
    fromCyc entry (((), name, deps):xs) =
      let (names, set) = fromCyc entry xs in
      (Set.insert name names, Set.union set $ Set.fromList deps)

removeRedundancies :: [MultiDepEntry] -> [MultiDepEntry]
removeRedundancies = map helper
  where
    helper (names, deps) = (names, Set.difference deps names)

tsort :: [MultiDepEntry] -> [Set.Set Name]
tsort [] = []
tsort deps = helper [] deps
  where
    helper acc deps
      | null a = next
      | null b = next ++ map fst a      -- This case is called when there is an invalid value
      | otherwise = helper next newDeps -- which breaks the topological sorting algorithm
      where                             --   TODO: Add a check earlier in the process for invalid
        (a, b) = roots deps             --         identifier names
        next = acc ++ b
        newDeps = foldr removeName a $ concat $ map Set.toList b
    roots [] = ([], [])
    roots ((e@(n, s)):xs)
      | Set.null s = (a, n:b)
      | otherwise = (e:a, b)
      where
        (a, b) = roots xs

getAllValues :: Set.Set Name -> Env a -> Env a
getAllValues _ [] = []
getAllValues s ((e@(n, _)):xs)
  | Set.member n s = e : rest
  | otherwise = rest
  where
    rest = getAllValues s xs

removeName :: Name -> [MultiDepEntry] -> [MultiDepEntry]
removeName _ [] = []
removeName n ((x, s):xs) = (x, Set.delete n s) : removeName n xs

depList :: Bool -> Env (Typed Expr) -> [DepEntry]
depList lam = map helper
  where
    helper (name, expr) = (name, execState (deps lam [] expr) Set.empty)

type DepState = StateT [DepEntry] (Either String)

checkRecursiveDeps :: [DepEntry] -> Either String ()
checkRecursiveDeps allDeps = sequence_ (map helper allDeps)
  where
    helper (name, deps) = check [] (Set.toList deps)
    check parents [] = Right ()
    check parents (x:xs) =
      case untilElem [x] x parents of
        [] -> do
          check parents xs
          check (x:parents) (Set.toList (fromJust (lookup x allDeps)))
        list -> Left ("infinite loop in top level values: " ++ intercalate " => " (map show list))
    untilElem list target [] = []
    untilElem list target (x:xs)
      | x == target = list'
      | otherwise = untilElem list' target xs
      where
        list' = x:list

showName :: Name -> String
showName name = '`' : show name ++ "`"

type AliasMode = Type -> State (Word64, Map.Map Word64 Type, Map.Map String Type) Type

alias :: AliasMode -> Type -> InferState Type
alias trans ty = do
  m <- get
  let (ty', (count', _, _)) = runState (trans ty) (getVarCount m, Map.empty, Map.empty)
  put $ m { getVarCount = count' }
  return ty'

globalAlias :: AliasMode
globalAlias (TAnon a) = do
  (c, ma, mv) <- get
  case Map.lookup a ma of
    Just ty -> return ty
    Nothing -> do
      let ty = TAnon c
      put (c+1, Map.insert a ty ma, mv)
      return ty
globalAlias (TVar v) = do
  (c, ma, mv) <- get
  case Map.lookup v mv of
    Just ty -> return ty
    Nothing -> do
      let ty = TAnon c
      put (c+1, ma, Map.insert v ty mv)
      return ty
globalAlias (TFunc a b) = TFunc <$> globalAlias a <*> globalAlias b
globalAlias other = return other

inferAlias :: AliasMode
inferAlias (TVar v) = do
  (c, ma, mv) <- get
  case Map.lookup v mv of
    Just ty -> return ty
    Nothing -> do
      let ty = TAnon c
      put (c+1, ma, Map.insert v ty mv)
      return ty
inferAlias (TFunc a b) = TFunc <$> inferAlias a <*> inferAlias b
inferAlias other = return other

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

unique_name :: Set.Set String -> Int -> (Int, String)
unique_name deny n
  | Set.member name deny = unique_name deny (n+1)
  | otherwise = (n+1, name)
  where
    name = generic_name n

quantify :: Set.Set String -> Type -> QuantifyState ()
quantify deny (TAnon a) = do
  (m, n) <- get
  case Map.lookup a m of
    Just x -> return ()
    Nothing -> do
      let (n', name) = unique_name deny n
      let var = TVar name
      put (Map.insert a var m, n')
quantify deny (TFunc a b) = quantify deny a >> quantify deny b
quantify deny _ = return ()

getLocals :: Typed Expr -> State (Set.Set String) ()
getLocals (x ::: t) = do
  case t of
    TVar name -> modify (Set.insert name)
    _ -> return ()
  case x of
    Val (Func xs expr) -> sequence (map locName xs) >> getLocals expr
    Op _ a b -> getLocals a >> getLocals b
    App a b -> getLocals a >> getLocals b
    If i t e -> getLocals i >> getLocals t >> getLocals e
    Let name val expr -> locName name >> getLocals val >> getLocals expr
    _ -> return ()
  where
    locName :: Typed Name -> State (Set.Set String) ()
    locName (_ ::: (TVar name)) = modify (Set.insert name)
    locName _ = return ()

class TypeMap a where
  mapTypes :: (Type -> Type) -> a -> a
  verifyTypes :: a -> Either String ()

instance (Show a, TypeMap a) => TypeMap (Typed a) where
  mapTypes f (x ::: t) = (mapTypes f x ::: f t)

  verifyTypes (x ::: t) = do
    verifyTypes x
    if deny t then
      Left ("cannot infer a concrete type for `" ++ show x ++ "`")
    else
      Right ()
    where
      deny (TAnon _) = True
      deny (TFunc a b) = deny a || deny b
      deny _ = False

instance TypeMap Name where
  mapTypes _ = id
  verifyTypes _ = Right ()

instance TypeMap Expr where
  mapTypes f (Val v) = Val (mapTypes f v)
  mapTypes f (Op op a b) = Op op (mapTypes f a) (mapTypes f b)
  mapTypes f (App a b) = App (mapTypes f a) (mapTypes f b)
  mapTypes f (If i t e) = If (mapTypes f i) (mapTypes f t) (mapTypes f e)
  mapTypes f (Let name val expr) = Let (mapTypes f name) (mapTypes f val) (mapTypes f expr)
  mapTypes _ other = other

  verifyTypes (Val v) = verifyTypes v
  verifyTypes (Op _ a b) = verifyTypes a >> verifyTypes b
  verifyTypes (App a b) = verifyTypes a >> verifyTypes b
  verifyTypes (If i t e) = verifyTypes i >> verifyTypes t >> verifyTypes e
  verifyTypes (Let name val expr) = verifyTypes name >> verifyTypes val >> verifyTypes expr
  verifyTypes _ = Right ()

instance TypeMap Value where
  mapTypes f (Func xs expr) = Func (map (mapTypes f) xs) (mapTypes f expr)
  mapTypes _ other = other

  verifyTypes (Func xs expr) = do
    sequence $ map verifyTypes xs
    verifyTypes expr
  verifyTypes _ = Right ()

ty :: Globals -> Env Type -> Typed Expr -> InferState Type
ty glob env (x ::: fin) = do
  case x of
    Val Unit -> unify fin tUnit
    Val (Nat _) -> unify fin tNat
    Val (Bool _) -> unify fin tBool
    Val (Func xs expr) -> do
      let types = map (\(n ::: t) -> (n, t)) xs
      res <- ty glob (reverse types ++ env) expr
      unify fin $ mkFuncTy (map typeof xs) res
    Id name -> do
      ty <-
        case Map.lookup name (globalVariables glob) of
          Just ty -> alias globalAlias ty
          Nothing ->
            case Map.lookup name (inferenceVariables glob) of
              Just ty -> alias inferAlias ty
              Nothing ->
                case lookup name env of
                  Just ty -> return ty
                  Nothing -> lift $ Left ("cannot find value: `" ++ show name ++ "`")
      unify fin ty
    Op op a b -> do
      a <- ty glob env a
      (t, r, _) <- lift $ getOp op
      b <- ty glob env b
      unify a t
      unify b t
      unify fin r
    App a b -> do
      a <- ty glob env a
      b <- ty glob env b
      unify a $ TFunc b fin
    If i t e -> do
      i <- ty glob env i
      unify i tBool
      t <- ty glob env t
      e <- ty glob env e
      unify t e
      unify fin t
    Let (name ::: ex) val expr -> do
      v <- ty glob env val
      unify v ex
      e <- ty glob ((name, v):env) expr
      unify fin e
  return fin

simplify :: InferMap -> Type -> Type
simplify m (TAnon a) =
  case Map.lookup a m of
    Just n -> simplify m n
    Nothing -> TAnon a
simplify m (TFunc a b) = TFunc (simplify m a) (simplify m b)
simplify _ other = other

simplify1 :: InferMap -> Type -> Type
simplify1 m (TAnon a) =
  case Map.lookup a m of
    Just n -> simplify m n
    Nothing -> TAnon a
simplify1 _ other = other

unify :: Type -> Type -> InferState ()
unify a b = do
  m <- gets getAnonMap
  u (simplify m a) (simplify m b)
  where
    u (TAnon a) (TAnon b) =
      if a == b then
        return ()
      else
        insertTAnon a (TAnon b)
    u (TAnon a) other = insertTAnon a other
    u other (TAnon a) = insertTAnon a other
    u (TId a) (TId b) =
      if a == b then
        return ()
      else
        lift $ Left ("cannot unify named types `" ++ show a ++ "` and `" ++ show b ++ "`")
    u (TVar a) (TVar b) =
      if a == b then
        return ()
      else
        lift $ Left ("cannot unify type variables `" ++ show a ++ "` and `" ++ show b ++ "`")
    u (TFunc a0 b0) (TFunc a1 b1) = do
      unify a0 a1
      unify b0 b1
    u a b = lift $ Left ("cannot unify types `" ++ show a ++ "` and `" ++ show b ++ "`")

insertTAnon :: Word64 -> Type -> InferState ()
insertTAnon k v =
  if typeContains k v then
    lift $ Left ("infinitely recursive type constraint: " ++ show (TAnon k) ++ " = " ++ show v)
  else do
    modify (insertAnon k v)

typeContains :: Word64 -> Type -> Bool
typeContains v (TAnon a) = a == v
typeContains v (TFunc a b) = typeContains v a || typeContains v b
typeContains _ _ = False
