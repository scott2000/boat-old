{-# LANGUAGE RecordWildCards #-}

module NameResolve where

import AST

import Data.List
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map

type ModuleList = Map.Map String ModuleInterface

data ModuleInterface = ModuleInterface
  { moduleNames :: Set.Set String,
    subModules :: ModuleList }

instance Show ModuleInterface where
  show ModuleInterface {..} =
    intercalate ", " (Set.toList moduleNames) ++ "\n"
      ++ intercalate "\n" (map m $ Map.toList subModules)
    where
      m (name, i) = name ++ ":\n" ++ indent2 (show i)

internalInterface :: ModuleInterface
internalInterface = ModuleInterface
  { moduleNames = Set.fromList ["Unit", "Nat", "Bool"],
    subModules = Map.empty }

isAbsolute :: Set.Set String -> UsePath -> Bool
isAbsolute rootNames u =
  case u of
    UseAll -> False
    UseMember name   -> name `Set.member` rootNames
    UseModule name _ -> name `Set.member` rootNames

toAbsolute :: Set.Set String -> Name -> UsePath -> UsePath
toAbsolute rootNames path u
  | isAbsolute rootNames u = u
  | otherwise = go (unname path) u
  where
    go [] u = u
    go (name:rest) u = UseModule name [go rest u]

treeInterface :: ModuleTree -> ModuleInterface
treeInterface ModuleTree {..} = ModuleInterface
  { moduleNames = Map.keysSet treeModules
      `Set.union` Map.keysSet treeDatas
      `Set.union` Map.keysSet treeValues,
    subModules = Map.map treeInterface treeModules }

defaultUsePaths :: [UsePath]
defaultUsePaths = [UseAll, UseModule InternalRoot [UseAll]]

nameResolveAll :: String -> ModuleTree -> Either String ModuleTree
nameResolveAll package tree = go (Name [package]) tree
  where
    go path ModuleTree {..} = do
      let imports = map (toAbsolute rootNames path) (defaultUsePaths ++ treeImports)
      names <- interfaceNames globalInterface imports
      let mapModule name m = go (path...name) m
      modules <- sequence $ Map.mapWithKey mapModule treeModules
      datas <- sequence $ Map.map (nameResolve rootNames names []) treeDatas
      values <- sequence $ Map.map (nameResolve rootNames names []) treeValues
      return ModuleTree
        { treeImports = [],
          treeModules = modules,
          treeDatas = datas,
          treeValues = values,
          .. }
    globalInterface = ModuleInterface
      { moduleNames = rootNames,
        subModules = moduleList }
    rootNames = Map.keysSet moduleList
    -- TODO add support for more than two packages
    moduleList = Map.fromList
      [ (InternalRoot, internalInterface),
        (package, treeInterface tree) ]

interfaceNames :: ModuleInterface
               -> [UsePath]
               -> Either String (Set.Set Name)
interfaceNames i us =
  execStateT (goAll EmptyName i us) Set.empty
  where
    goAll path i us = sequence_ $ map (go path i) us
    go :: Name
       -> ModuleInterface
       -> UsePath
       -> StateT (Set.Set Name) (Either String) ()
    go path ModuleInterface {..} u =
      case u of
        UseAll ->
          modify $ Set.union $ Set.map (path...) moduleNames
        UseMember name
          | name `Set.member` moduleNames ->
            modify $ Set.insert (path...name)
          | otherwise -> packageOr "member" name
        UseModule name rest ->
          case Map.lookup name subModules of
            Nothing -> packageOr "module" name
            Just sub -> do
              let modPath = path...name
              modify $ Set.insert modPath
              goAll modPath sub rest
      where
        packageOr ty name
          | null $ unname path =
            lift $ Left ("cannot find package `" ++ name ++ "`")
          | otherwise =
            lift $ Left ("cannot find " ++ ty ++ " `" ++ name ++ "` in `" ++ show path ++ "`")

possibleNames :: Name -> Set.Set Name -> [Name]
possibleNames (Name (name:names)) = foldl' add []
  where
    add xs (Name n)
      | last n == name = Name (n ++ names) : xs
      | otherwise = xs

class NameResolve a where
  nameResolve :: Set.Set String -> Set.Set Name -> [Name] -> a -> Either String a

instance NameResolve a => NameResolve (Typed a) where
  nameResolve rootNames s l (x ::: ty) =
    (:::) <$> nameResolve rootNames s l x <*> nameResolve rootNames s [] ty

instance NameResolve Name where
  nameResolve rootNames s l name
    | name `elem` l = Right name
    | head (unname name) `Set.member` rootNames = Right name
    | otherwise =
      case possibleNames name s of
        [] -> Left ("cannot find `" ++ show name ++ "` in current scope\n  locals: " ++ intercalate ", " (map show l))
        [x] -> Right x
        xs -> Left ("ambiguous name `" ++ show name ++ "` could refer to:\n  " ++ intercalate "\n  " (map show xs))

instance NameResolve Expr where
  nameResolve rootNames s l x =
    case x of
      Val v ->
        Val <$> cont v
      Id name ->
        Id <$> cont name
      Op op a b ->
        Op op <$> cont a <*> cont b
      App a b ->
        App <$> cont a <*> cont b
      If i t e ->
        If <$> cont i <*> cont t <*> cont e
      Let name val expr ->
        Let name <$> cont val <*> contWith (valof name : l) expr
      Match exprs cases -> do
        exprs <- sequence $ map cont exprs
        cases <- sequence $ for cases $ \(pats, expr) -> do
          let names = map fst $ allPatternNames pats
          pats <- sequence $ map cont pats
          expr <- contWith (names ++ l) expr
          return (pats, expr)
        return $ Match exprs cases
      ICons name variant list ->
        ICons name variant <$> sequence (map cont list)
      other -> Right other
    where
      contWith :: NameResolve a => [Name] -> a -> Either String a
      contWith = nameResolve rootNames s
      cont :: NameResolve a => a -> Either String a
      cont = contWith l

instance NameResolve Value where
  nameResolve rootNames s l x =
    case x of
      Cons name variant list ->
        Cons name variant <$> sequence (map cont list)
      Func xs expr -> do
        xs <- sequence $ for xs $ \(x ::: t) ->
          (x :::) <$> cont t
        expr <- contWith (map valof xs ++ l) expr
        return $ Func xs expr
      other -> Right other
    where
      contWith :: NameResolve a => [Name] -> a -> Either String a
      contWith = nameResolve rootNames s
      cont :: NameResolve a => a -> Either String a
      cont = contWith l

instance NameResolve Pattern where
  nameResolve rootNames s l (PCons name pats) = do
    name <- nameResolve rootNames s [] name
    pats <- sequence $ map (nameResolve rootNames s l) pats
    return $ PCons name pats
  nameResolve _ _ _ other = Right other

instance NameResolve Type where
  nameResolve rootNames s _ (TId name) =
    TId <$> nameResolve rootNames s [] name
  nameResolve rootNames s l (TApp a b) =
    TApp <$> nameResolve rootNames s l a <*> nameResolve rootNames s l b
  nameResolve _ _ _ other = Right other

instance NameResolve DataDecl where
  nameResolve rootNames s _ DataDecl {..} = do
    variants <- sequence $ for variants $ \(name, types) -> do
      types <- sequence $ map (nameResolve rootNames s []) types
      return (name, types)
    return DataDecl {..}
