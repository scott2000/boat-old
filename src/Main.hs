{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}

module Main where

import AST
import Parser
import NameResolve
import Infer
import Run
import Compile

import qualified System.Console.ANSI as F

import System.Console.Haskeline
import System.FilePath
import System.Directory
import System.IO (hFlush, stdout, readFile)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import Data.Word
import Text.Megaparsec
import Control.Monad.State
import qualified Data.Map as Map

version :: String
version = "0.1.0"

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> startRepl
    [path] -> startCompile path
    other -> do
      putStrLn ("too many arguments: " ++ unwords other)
      putStrLn "Usage: boat [file]"

findNamed :: Name -> Env (Typed a) -> Either String (Typed Name)
findNamed name env =
  case lookup name env of
    Nothing -> Left ("cannot find a definition for `" ++ show name ++ "`")
    Just (_ ::: ty)
      | isGeneric ty -> Left ("type of entry point `" ++ show name ++ "` is not concrete: " ++ show ty)
      | otherwise -> Right (name ::: ty)

startCompile :: FilePath -> IO ()
startCompile path = do
  header "parse"
  assertOrFail (isValid path) ("invalid path: " ++ path)
  let (dirPath, extension) = splitExtension path
  assertOrFail (extension == ".boat") ("expected an extension of .boat, found " ++ extension)
  let package = takeBaseName dirPath
  assertOrFail (isValidName package) ("invalid package name: " ++ package)
  let parseModules = compileStep package dirPath (Name [package])
  (tree, nextAnon) <- execStateT parseModules (emptyModule, 0)
  header "tree"
  putStrLn $ show $ tree
  header "name resolve"
  case nameResolveAll package tree of
    Left err -> printerr err
    Right tree -> do
      putStrLn $ show $ tree
      header "infer"
      let (datas, values) = treeCollect package tree
      case inferAll nextAnon datas values of
        Left err -> printerr err
        Right (inferred, _) -> do
          putStr $ unlines $ for inferred $ \(n, _ ::: ty) -> show n ++ " : " ++ show ty
          header "evaluate"
          case findNamed (Name [package, "main"]) inferred of
            Left err -> printerr err
            Right name ->
              case evaluateEntry name inferred of
                Left err -> printerr err
                Right (mainVal, runMap) -> do
                  putStrLn (show mainVal ++ " : " ++ show (typeof mainVal))
                  header "compile"
                  compile path mainVal runMap datas 64

compileStep :: String -> FilePath -> Name -> StateT (ModuleTree, AnonCount) IO ()
compileStep package dirPath name = do
  lift $ putStrLn $ show name
  let path = dirPath <.> "boat"
  fileExists <- lift $ doesFileExist path
  lift $ assertOrFail fileExists ("cannot find source file: " ++ path)
  file <- lift $ readFile path
  (tree, nextAnon) <- get
  let parser = runCustomParser nextAnon $ moduleParser name tree
  case runParser parser path file of
    Left err ->
      let msg = errorFmt ++ "syntax error: " ++ reset ++ errorBundlePretty err in
      lift (putStr msg >> flushOut >> exitFailure)
    Right new -> do
      put new
      dirExists <- lift $ doesDirectoryExist dirPath
      if dirExists then do
        files <- lift $ listDirectory dirPath
        sequence_ $ for files $ \file ->
          let (subName, extension) = splitExtension file in
          if extension /= ".boat" then return () else do
          lift $ assertOrFail (isValidName subName) ("invalid module name: " ++ subName)
          let parseModules = compileStep package (dirPath </> subName) (name...subName)
          (ModuleTree {..}, nextAnon) <- get
          let sub = Map.findWithDefault emptyModule subName treeModules
          (sub', nextAnon) <- lift $ execStateT parseModules (sub, nextAnon)
          put (ModuleTree { treeModules = Map.insert subName sub' treeModules, .. }, nextAnon)
      else
        return ()

assertOrFail :: Bool -> String -> IO ()
assertOrFail True _ = return ()
assertOrFail False err = printerr err

isValidName :: String -> Bool
isValidName [] = False
isValidName (first:rest) = isAlpha first && all isAlphaNum rest
  where
    isAlpha ch = ch `elem` ['A'..'Z'] || ch `elem` ['a'..'z'] || ch == '_'
    isAlphaNum ch = isAlpha ch || ch `elem` ['0'..'9']

printerr, header :: String -> IO ()
printerr err = putStrLn (errorFmt ++ "error: " ++ reset ++ err) >> exitFailure
header x = putStrLn ("\n-- " ++ x ++ " --\n")

green, red, reset, errorFmt, promptFmt, dullBlue :: String
green = F.setSGRCode [F.SetColor F.Foreground F.Dull F.Green]
red = F.setSGRCode [F.SetColor F.Foreground F.Dull F.Red]
reset = F.setSGRCode [F.Reset]
errorFmt = F.setSGRCode
  [ F.SetColor F.Foreground F.Vivid F.Red,
    F.SetConsoleIntensity F.BoldIntensity ]
promptFmt = F.setSGRCode
  [ F.SetColor F.Foreground F.Vivid F.Blue,
    F.SetConsoleIntensity F.BoldIntensity ]
dullBlue = F.setSGRCode
  [ F.SetColor F.Foreground F.Dull F.Blue ]

flushOut :: IO ()
flushOut = hFlush stdout

type Repl = StateT ReplState (InputT IO)

-- TODO use separate list for res0, res1, res2, etc?
data ReplState = ReplState
  { replNextAnon :: Word64,
    replNextExpr :: Word64,
    replSetInfo :: Bool,
    replFirst :: Bool,
    replImports :: [UsePath],
    replDatas :: Map.Map Name DataDecl,
    replValues :: Map.Map Name (Typed Expr) }

data ReplResult
  = Quit
  | Ignore
  | Reset
  | DeclareUse [UsePath]
  | DeclareVal (String, Typed Expr)
  | DeclareData (String, DataDecl)
  | Eval (Typed Expr)

defaultRepl :: ReplState
defaultRepl = ReplState
  { replNextAnon = 0,
    replNextExpr = 0,
    replSetInfo = False,
    replFirst = True,
    replImports = [],
    replDatas = Map.empty,
    replValues = Map.empty }

startRepl :: IO ()
startRepl = do
  putStrLn $ unlines $
    [ "",
      "        |\\",
      "       /| \\         Boat " ++ version,
      "      /_|  \\",
      "        |___\\     Type a declaration to add it to the scope,",
      "  ______|______   type an expression to evaluate it,",
      "  \\  o  o  o  /   or type `:help` to see available commands.",
      "   \\_________/" ]
  let
    settings = Settings
      { complete = noCompletion,
        historyFile = Nothing,
        autoAddHistory = True }
  runInputT settings $ evalStateT repl defaultRepl

repl :: Repl ()
repl = lift $ outputStrLn (errorFmt ++ "repl is currently disabled" ++ reset ++ "\n")

{-

-- TODO reimplement repl to support modules
repl :: Repl ()
repl = go ""
  where
    outputError str = do
      lift $ outputStrLn (errorFmt ++ "error: " ++ reset ++ str)
      repl
    go continuation = do
      ReplState { replNextExpr, replSetInfo, replFirst } <- get
      let
        replRes = "res" ++ show replNextExpr
        replSpace = map (const ' ') replRes
        replIntro
          | not replSetInfo = ""
          | null continuation && replFirst = replRes
          | otherwise = replSpace
        replSeparator
          | null continuation = "> "
          | otherwise         = "| "
        reset = F.setSGRCode
          [ F.Reset ]
      line <- lift $ getInputLine (promptFmt ++ replIntro ++ replSeparator ++ reset)
      case line of
        Nothing -> return ()
        Just line -> do
          let
            fullLine = continuation ++ line
            tryLine x
              | null line = Just x
              | otherwise = Nothing
          case unfinished fullLine of
            Just c ->
              case
                case c of
                  ')' -> Just $ "missing opening parenthesis: .. )"
                  ']' -> Just $ "missing opening bracket: .. ]"
                  '}' -> Just $ "missing opening brace: .. }"
                  '(' -> tryLine $ "missing closing parenthesis: ( .. "
                  '[' -> tryLine $ "missing closing bracket: [ .. "
                  '{' -> tryLine $ "missing closing brace: { .. "
                  _   -> tryLine "incomplete expression"
              of
                Nothing -> go (fullLine ++ "\n")
                Just msg -> outputError msg
            Nothing
              | null line -> repl
              | otherwise -> do
                result <- iterRepl $ consumeSpaces fullLine
                case result of
                  Quit -> return ()
                  Ignore -> repl
                  Reset -> do
                    put defaultRepl
                    repl
                  DeclareUse us -> do
                    modify $ \s -> s { replImports = us ++ replImports s, replFirst = False }
                    outputError "use declarations in repl are not yet implemented"
                  DeclareVal (name, val)
                    | invalidName name ->
                      outputError ("cannot declare value with name `" ++ name ++ "`, try `result" ++ drop 3 name ++ "` instead")
                    | otherwise -> do
                      modify $ \s -> s { replValues = Map.insert (Name [name]) val (replValues s), replFirst = False }
                      repl
                  DeclareData (name, data') -> do
                    modify $ \s ->
                      let
                        dataName = Name [name]
                        insertAll [] m = m
                        insertAll ((n, x):xs) m =
                          insertAll xs $ Map.insert (Name [n]) x m
                      in s
                        { replDatas = Map.insert dataName data' (replDatas s),
                          replValues = insertAll (constructorsForData dataName data') $ replValues s,
                          replFirst = False }
                    repl
                  Eval expr -> do
                    ReplState {..} <- get
                    let
                      resName = Name [replRes]
                      dataDecls = Map.toList replDatas
                      valDecls = (resName, expr) : Map.toList replValues
                    -- TODO name resolution
                    case inferAll replNextAnon dataDecls valDecls of
                      Left err -> outputError err
                      Right (inferred, newAnon) ->
                        case findNamed resName inferred of
                          Left err -> outputError err
                          Right typedName ->
                            case evaluateEntry typedName inferred of
                              Left err -> outputError err
                              Right (evaluated, _) -> do
                                let
                                  typeInfo str
                                    | replSetInfo = str ++ dullBlue ++ " : "
                                                    ++ show (typeof evaluated) ++ reset
                                    | otherwise   = str
                                  output = typeInfo $ show evaluated
                                lift $ outputStrLn output
                                put $ ReplState
                                  { replNextAnon = newAnon,
                                    replNextExpr = replNextExpr+1,
                                    replFirst = True,
                                    replValues = Map.insert resName (embed evaluated) $ Map.fromList inferred,
                                    .. }
                                repl

unfinished :: String -> Maybe Char
unfinished str = foldl1 (<|>) $ map check [('(', ')'), ('[', ']'), ('{', '}')]
  where
    check (a, b) =
      case compare (count a) (count b) of
        GT -> Just a
        LT -> Just b
        EQ -> Nothing
    count c = count' 0 c str
    count' a c [] = a
    count' a c (x:xs)
      | x == c = count' (a+1) c xs
      | otherwise = count' a c xs

invalidName :: String -> Bool
invalidName "res0" = True
invalidName ('r':'e':'s':'0':_) = False
invalidName ('r':'e':'s':n)
  | all isDigit n = True
  | otherwise     = False
  where
    isDigit n = n `elem` ['0'..'9']
invalidName _ = False

iterRepl :: String -> Repl ReplResult
iterRepl (':' : commands) = parseCommands commands
iterRepl string = do
  ReplState {..} <- get
  let parser = runCustomParser replNextAnon $ parseRepl replNextExpr
  case runParser parser "<repl>" string of
    Left err -> lift $ do
      outputStr (errorFmt ++ "syntax error: " ++ reset ++ errorBundlePretty err)
      return Ignore
    Right (state, nextAnon) -> do
      modify $ \s -> s { replNextAnon = nextAnon }
      return state

parseRepl :: Word64 -> Parser ReplResult
parseRepl n =
  DeclareUse <$> useDeclParser
  <|> DeclareVal <$> parseReplVal n
  <|> DeclareData <$> dataDeclParser
  <|> Eval <$> parseReplExpr n

parseReplVal :: Word64 -> Parser (String, Typed Expr)
parseReplVal 0 = valDeclParser
parseReplVal n = do
  (name, expr) <- valDeclParser
  return (name, substituteN n expr)

parseReplExpr :: Word64 -> Parser (Typed Expr)
parseReplExpr 0 = parser
parseReplExpr n = substituteN n <$> parser

substituteN :: Word64 -> Typed Expr -> Typed Expr
substituteN n = substitute (Name ["res"]) $ Id $ Name ["res" ++ show (n-1)]

parseCommands :: String -> Repl ReplResult
parseCommands commands =
  case separate commands of
    ("help", _) -> lift $ do
      sequence_ $ map outputStrLn $
        [ "",
          "Tips:",
          "  - The special identifier `res` refers to the result of the last expression",
          "  - Blocks surrounded by (), [], or {} can span multiple lines",
          "",
          "Commands:",
          "  :help           display this help info",
          "  :clear          clear the display",
          "  :reset          clear and reset all declarations",
          "  :list           list declarations",
          "  :info [on|off]  toggle info",
          "  :quit           exit the repl",
          "" ]
      return Ignore
    ("clear", _) -> clear >> return Ignore
    ("reset", _) -> clear >> return Reset
    ("list", _) -> do
      ReplState {..} <- get
      let
        showFst (a, b) = (show a, b)
        imports = map (("use " ++) . show) replImports
        datas = map (showData . showFst) $ Map.toList replDatas
        values = map (showVal . showFst) $ Map.toList replValues
      lift $ outputStrLn $ unlines (imports ++ datas ++ values)
      return Ignore
    ("info", "on") -> setInfo $ const True
    ("info", "off") -> setInfo $ const False
    ("info", []) -> setInfo not
    ("info", _) ->
      outputError "command `info` expects either no argument or `on` or `off`"
    ("quit", _) ->
      return Quit
    (command, _) ->
      outputError ("unknown command: `" ++ command ++ "`")
  where
    clear = lift $ outputStr "\x1b[3J\x1b[H\x1b[2J"
    separate [] = ([], [])
    separate (' ':xs) = ([], consumeSpaces xs)
    separate (x:xs) =
      let
        (b, r) = separate xs
      in
        (x:b, r)
    outputError str = do
      lift $ outputStrLn (errorFmt ++ "error: " ++ reset ++ str)
      return Ignore

setInfo :: (Bool -> Bool) -> Repl ReplResult
setInfo f = do
  s <- get
  let
    old = replSetInfo s
    new = f old
    msg =
      case (old, new) of
        (False, True) ->
          green ++ "info enabled" ++ reset
        (True, False) ->
          red ++ "info disabled" ++ reset
        (False, False) ->
          red ++ "info already off" ++ reset
        (True, True) ->
          green ++ "info already on" ++ reset
  put $ s { replSetInfo = new, replFirst = True }
  lift $ outputStrLn msg
  return Ignore

consumeSpaces :: String -> String
consumeSpaces (' ':xs) = consumeSpaces xs
consumeSpaces other = other

-}
