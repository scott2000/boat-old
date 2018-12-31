{-# LANGUAGE RecordWildCards, PatternSynonyms #-}

module AST where

import Data.Word
import Data.List
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map

type MatchCase = ([Typed Pattern], Typed Expr)

data Expr
  = Val Value                                   -- values
  | Id Name                                     -- identifiers
  | Op String (Typed Expr) (Typed Expr)         -- primitive operations
  | App (Typed Expr) (Typed Expr)               -- (a b)
  | If (Typed Expr) (Typed Expr) (Typed Expr)   -- (if a then b else c)
  | Let (Typed Name) (Typed Expr) (Typed Expr)  -- (let a = b in c)
  | Match [Typed Expr] [MatchCase]              -- (match a in b c)
  | Panic String                                -- panic
  | ICons Name String [Typed Expr]
  deriving Eq

data Type
  = TAnon Word64    -- anonymous types
  | TId Name        -- identifiers
  | TVar String     -- type variables
  | TArrow          -- (->)
  | TApp Type Type  -- (a b)
  deriving (Eq, Ord)

data Typed a = (:::)
  { valof :: a,
    typeof :: Type }
  deriving Eq

data Value
  = Unit
  | Nat Word64
  | Bool Bool
  | Cons Name String [Typed Value]
  | Func [Typed Name] (Typed Expr)
  deriving Eq

data Pattern
  = PAny (Maybe Name)
  | PNat Word64
  | PBool Bool
  | PCons Name [Typed Pattern]
  deriving Eq

data ModuleTree = ModuleTree
  { treeModules :: Map.Map String ModuleTree,
    treeDatas :: Map.Map String DataDecl,
    treeValues :: Map.Map String (Typed Expr) }
  deriving Eq

data DataDecl = DataDecl
  { typeParams :: [String],
    variants :: [(String, [Type])] }
  deriving (Show, Eq)

newtype Name = Name
  { unname :: [String] }
  deriving (Eq, Ord)

--TODO replace most usages of Env with Map for efficiency?
type Env a = [(Name, a)]

instance Show Expr where
  show (Val v) = show v
  show (Id name) = show name
  show (Op op a b) = "(" ++ show a ++ " " ++ op ++ " " ++ show b ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (If i t e) = "(if " ++ show i ++ " then " ++ show t ++ " else " ++ show e ++ ")"
  show (Let name val expr) = "(let " ++ show name ++ " = " ++ show val ++ " in " ++ show expr ++ ")"
  show (Match exprs cases) = "(match " ++ intercalate " " (map show exprs) ++ " in\n" ++ intercalate "\n" (map showCase cases) ++ ")"
  show (Panic []) = "(panic\n)"
  show (Panic msg) = "(panic " ++ msg ++ "\n)"
  show (ICons name variant []) = show (name.|.variant)
  show (ICons name variant list) =
    "(" ++ intercalate " " (show (name.|.variant) : map show list) ++ ")"

showCase :: MatchCase -> String
showCase (p, e) = "  " ++ intercalate " " (map show p) ++ " -> " ++ show e

instance Show Type where
  show (TAnon n) = "{-" ++ show n ++ "-}"
  show (TId s) = show s
  show (TVar s) = s
  show TArrow = "(->)"
  show (TFunc a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (TApp a b) = "(" ++ show a ++ " " ++ show b ++ ")"

instance Show a => Show (Typed a) where
  show (x ::: t) = show x

instance Show Value where
  show Unit = "unit"
  show (Nat n) = show n
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Cons name variant []) = show (name.|.variant)
  show (Cons name variant vals) =
    "(" ++ intercalate " " (show (name.|.variant) : map show vals) ++ ")"
  show (Func xs expr) = "<func>"

instance Show Pattern where
  show (PAny Nothing) = "_"
  show (PAny (Just n)) = show n
  show (PNat n) = show n
  show (PBool True) = "true"
  show (PBool False) = "false"
  show (PCons n []) = show n
  show (PCons n pats) = "(" ++ intercalate " " (show n : map show pats) ++ ")"

instance Show ModuleTree where
  show ModuleTree {..} =
    intercalate "\n" (
      map m (Map.toList treeModules)
      ++ map showData (Map.toList treeDatas)
      ++ map showVal (Map.toList treeValues))
    where
      m (name, _) = "{- mod " ++ name ++ " -}"

showData :: (String, DataDecl) -> String
showData (name, DataDecl {..}) =
  "data " ++ parameterized ++ " = " ++ intercalate " | " (map showVariant variants)
  where
    parameterized = intercalate " " (name : typeParams)
    showVariant (name, types) = intercalate " " (name : map show types)

showVal :: (String, Typed Expr) -> String
showVal (name, val ::: TAnon _) =
  "val " ++ name ++ " = " ++ show val
showVal (name, val ::: ty) =
  "val " ++ name ++ " : " ++ show ty ++ " = " ++ show val

instance Show Name where
  show (Name s) = intercalate "." s

(...) :: Name -> String -> Name
(...) (Name a) b = Name (a ++ [b])

(.|.) :: Name -> String -> Name
(.|.) (Name a) b = Name (go a)
  where
    go [_] = [b]
    go (x:xs) = x : go xs

type SerializedTree = (Env DataDecl, Env (Typed Expr))

treeCollect :: ModuleTree -> SerializedTree
treeCollect m = treeCollect' (Name []) m ([], [])

treeCollect' :: Name -> ModuleTree -> SerializedTree -> SerializedTree
treeCollect' name ModuleTree {..} (datas, values) =
  foldr ($) (add treeDatas datas, add treeValues values) mods
  where
    change (n, x) = (name...n, x)
    add a b = map change (Map.toList a) ++ b
    convert (n, m) = treeCollect' (name...n) m
    mods = map convert (Map.toList treeModules)

isGeneric :: Type -> Bool
isGeneric (TId _) = False
isGeneric TArrow = False
isGeneric (TApp a b) = isGeneric a || isGeneric b
isGeneric _ = True

emptyModule :: ModuleTree
emptyModule = ModuleTree
  { treeModules = Map.empty,
    treeDatas = Map.empty,
    treeValues = Map.empty }

uniqueInsert :: Ord k => e -> k -> v -> Map.Map k v -> Either e (Map.Map k v)
uniqueInsert e k v m
  | k `Map.member` m = Left e
  | otherwise = Right (Map.insert k v m)

addSubModule :: String -> ModuleTree -> ModuleTree -> Either String ModuleTree
addSubModule name m ModuleTree {..} = do
  new <- uniqueInsert err name m treeModules
  return ModuleTree { treeModules = new, .. }
  where
    err = "multipe submodules with name: " ++ show name

addDataDecl :: String -> DataDecl -> ModuleTree -> Either String ModuleTree
addDataDecl name data' ModuleTree {..} = do
  new <- uniqueInsert err name data' treeDatas
  return ModuleTree { treeDatas = new, .. }
  where
    err = "data type defined multiple times in module: " ++ show name

addValDecl :: String -> Typed Expr -> ModuleTree -> Either String ModuleTree
addValDecl name val ModuleTree {..} = do
  new <- uniqueInsert err name val treeValues
  return ModuleTree { treeValues = new, .. }
  where
    err = "value defined multiple times in module: " ++ show name

replaceSubModule :: String -> ModuleTree -> ModuleTree -> ModuleTree
replaceSubModule name m ModuleTree {..} = ModuleTree
  { treeModules = Map.insert name m treeModules, .. }

replaceDataDecl :: String -> DataDecl -> ModuleTree -> ModuleTree
replaceDataDecl name data' ModuleTree {..} = ModuleTree
  { treeDatas = Map.insert name data' treeDatas, .. }

replaceValDecl :: String -> Typed Expr -> ModuleTree -> ModuleTree
replaceValDecl name val ModuleTree {..} = ModuleTree
  { treeValues = Map.insert name val treeValues, .. }

constructorsForData :: (Name, DataDecl) -> Env (Typed Expr)
constructorsForData (name, DataDecl {..}) = map constructorFor variants
  where
    constructorFor (vname, []) = (name.|.vname, Val (Cons name vname []) ::: ty)
    constructorFor (vname, types) =
      (name.|.vname, (Val $ Func names $ ICons name vname exprs ::: ty) ::: fty)
      where
        names = zipWith (:::) allNames types
        exprs = zipWith idFor allNames types
        idFor name ty = Id name ::: ty
        fty = mkFuncTy types ty
    ty = foldl' TApp (TId name) tvars
    tvars = map TVar typeParams
    allNames = for [0..] $ \x -> Name ["p" ++ show x]

constructorTypesForData :: (Name, DataDecl) -> Env Type
constructorTypesForData (name, DataDecl {..}) = map typeFor variants
  where
    typeFor (vname, types) = (name.|.vname, mkFuncTy types ty)
    ty = foldl' TApp (TId name) $ map TVar typeParams

constructorPatternsForData :: (Name, DataDecl) -> Env (Type, [Type])
constructorPatternsForData (name, DataDecl {..}) = map patFor variants
  where
    patFor (vname, types) = (name.|.vname, (ty, types))
    ty = foldl' TApp (TId name) $ map TVar typeParams

deps :: Bool -> [Name] -> Typed Expr -> State (Set.Set Name) ()
deps lam env (expr ::: _) =
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
    Match exprs cases -> do
      sequence_ $ map (deps lam env) exprs
      let caseDeps (p, e) = deps lam ((map fst $ allPatternNames p) ++ env) e
      sequence_ $ map caseDeps cases
    Panic _ -> return ()
    ICons _ _ list -> sequence_ $ for list $ deps lam env

-- TODO verification of non-duplication for pattern names
patternNames :: Typed Pattern -> Env Type
patternNames (pat ::: ty) =
  case pat of
    PAny (Just name) -> [(name, ty)]
    PCons _ list -> concat $ map patternNames list
    _ -> []

allPatternNames :: [Typed Pattern] -> Env Type
allPatternNames = concat . map patternNames

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
    Match exprs cases ->
      matchLocals exprs cases $ foldr ($) env $ map countLocals exprs
    Panic _ -> env
    ICons _ _ list ->
      foldr ($) env $ map countLocals list
  where
    addName name [] = []
    addName name ((e@(n, x)) : xs)
      | n == name = (n, x+1) : xs
      | otherwise = e : addName name xs

matchLocals :: [Typed Expr] -> [MatchCase] -> Env Int -> Env Int
matchLocals exprs cases env =
  let
    caseToEnv (pats, expr) = drop (length patternEnv) $ newEnv
      where
        newEnv = countLocals expr (patternEnv ++ env)
        patternEnv = map namesToEnv $ allPatternNames pats
        namesToEnv (name, _) = (name, 0)
  in
    combineEnvs $ map caseToEnv cases

countOccurances :: Name -> Typed Expr -> Int -> Int
countOccurances name = go
  where
    go (expr ::: ty) x =
      case expr of
        Val (Func params expr)
          | name `elem` map valof params -> x
          | otherwise -> go expr x
        Val _ -> x
        Id n
          | n == name -> x+1
          | otherwise -> x
        Op _ a b -> go a $ go b x
        App a b -> go a $ go b x
        If i t e -> go i $ go t $ go e x
        Let (n ::: _) val expr ->
          go val $ if n == name then x else go expr x
        Match exprs cases ->
          let
            x' = foldr ($) x $ map go exprs
            iterCase (pats, expr) x
              | name `elem` map fst (allPatternNames pats) = x
              | otherwise = go expr x
          in
            foldr ($) x' $ map iterCase cases
        Panic _ -> x
        ICons _ _ list ->
          foldr ($) x $ map go list

substitute :: Name -> Expr -> Typed Expr -> Typed Expr
substitute name value (expr ::: ty) =
  (::: ty) $ case expr of
    Val (Func xs expr) ->
      Val (Func xs (checkFunc xs name value expr))
    Val other -> Val other
    Id n
      | n == name -> value
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
    Match exprs cases ->
      Match (map (substitute name value) exprs) $ for cases $ \(p, e) ->
        if name `elem` (map fst $ allPatternNames p) then
          (p, e)
        else
          (p, substitute name value e)
    Panic msg -> Panic msg
    ICons n variant list ->
      ICons n variant $ for list $ substitute name value

checkFunc :: [Typed Name] -> Name -> Expr -> Typed Expr -> Typed Expr
checkFunc [] name value expr = substitute name value expr
checkFunc ((n ::: _):ns) name value expr
  | n == name = expr
  | otherwise = checkFunc ns name value expr

combineEnvs :: [Env Int] -> Env Int
combineEnvs (e:es) = foldr (zipEnv max) e es

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
    n s op = (s, (TNat, TNat, f))
      where
        f (Nat a) (Nat b) = Right (Nat (op a b))
        f _ _ = Left ("invalid inputs for numeric operator `" ++ s ++ "`, expected two `Nat` arguments")
    c s op = (s, (TNat, TBool, f))
      where
        f (Nat a) (Nat b) = Right (Bool (op a b))
        f _ _ = Left ("invalid inputs for comparison operator `" ++ s ++ "`, expected two `Nat` arguments")
    b s op = (s, (TBool, TBool, f))
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

tIdVar :: Name -> Type
tIdVar (name@(Name [s])) =
  if isCap $ head s then
    TId name
  else
    TVar s
tIdVar name = TId name

pIdVar :: Name -> Pattern
pIdVar (name@(Name [s])) =
  if isCap $ head s then
    PCons name []
  else
    PAny $ Just $ name
pIdVar name = PCons name []

isCap :: Char -> Bool
isCap ch
  | ch `elem` ['A'..'Z'] || ch == '_' = True
  | otherwise = False

for :: [a] -> (a -> b) -> [b]
for = flip map

lookup' :: (Eq k, Show k, Show v) => k -> [(k, v)] -> v
lookup' name xs = go xs
  where
    go [] = error ("cannot find `" ++ show name ++ "` in " ++ show xs)
    go ((n,x):xs)
      | n == name = x
      | otherwise = go xs

pattern Internal :: String -> Name
pattern Internal s = Name [{-"Internal",-} s]

pattern TUnit :: Type
pattern TUnit = TId (Internal "Unit")

pattern TNat :: Type
pattern TNat = TId (Internal "Nat")

pattern TBool :: Type
pattern TBool = TId (Internal "Bool")

pattern TFunc :: Type -> Type -> Type
pattern TFunc a b = TApp (TApp TArrow a) b
