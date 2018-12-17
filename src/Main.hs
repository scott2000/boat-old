{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import AST
import Parser
import Infer
import Run
import Compile

import qualified System.Console.ANSI as F

import System.Console.Haskeline

import System.IO (hFlush, stdout, readFile)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import Data.Word
import Data.Maybe
import Text.Megaparsec
import Control.Monad.State

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
      putStrLn "expected either a file name or nothing"

startCompile :: String -> IO ()
startCompile path = do
  header path
  file <- readFile path
  putStr $ dropWhile ('\n' ==) file
  header "parsed"
  let parser = runCustomParser 0 declsParser
  case runParser parser path file of
    Left err -> putStr (errorFmt ++ "syntax error: " ++ reset ++ errorBundlePretty err) >> flushOut >> exitFailure
    Right (decls, nextAnon) -> do
      let datas = dataDecls decls
      putStr $ unlines $ map showDataDecl $ datas
      putStr $ unlines $ map showValDecl $ valDecls decls
      header "inferred"
      case inferAll nextAnon decls of
        Left err -> putStrLn (errorFmt ++ "error: " ++ reset ++ err) >> exitFailure
        Right (inferred, _) -> do
          putStr $ unlines $ map showValDecl inferred
          header "evaluate"
          case evaluateAll inferred datas of
            Left err -> putStrLn (errorFmt ++ "error: " ++ reset ++ err) >> exitFailure
            Right evaluated -> do
              putStr $ unlines $ map (\(n,x) -> show n ++ " : " ++ show (typeof x) ++ " = " ++ show x) evaluated
              header "compiled"
              compile path evaluated datas 64
  where
    header x = putStrLn ("\n-- " ++ x ++ " --\n")

type Repl = StateT ReplState (InputT IO)

data ReplState = ReplState
  { replNextAnon :: Word64,
    replNextExpr :: Word64,
    replSetInfo :: Bool,
    replDecls :: Decls,
    replFirst :: Bool }

data ReplResult
  = Quit
  | Ignore
  | Reset
  | DeclareVal (Name, Typed Expr)
  | DeclareData (Name, DataDecl)
  | Eval (Typed Expr)

defaultRepl :: ReplState
defaultRepl = ReplState
  { replNextAnon = 0,
    replNextExpr = 0,
    replSetInfo = False,
    replDecls = emptyDecls,
    replFirst = True }

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
                  DeclareVal val
                    | invalidName name ->
                      outputError ("cannot declare value with name `" ++ name ++ "`, try `result" ++ drop 3 name ++ "` instead")
                    | otherwise -> do
                      modify $ \s -> s { replDecls = changeValDecl val (replDecls s), replFirst = False }
                      repl
                    where
                      name = show $ fst val
                  DeclareData data' -> do
                    modify $ \s -> s { replDecls = changeDataDecl data' (replDecls s), replFirst = False }
                    repl
                  Eval expr -> do
                    ReplState {..} <- get
                    let newDecls = changeValDecl (Name replRes, expr) replDecls
                    case inferAll replNextAnon newDecls of
                      Left err -> outputError err
                      Right (inferred, newAnon) ->
                        case evaluateAll inferred $ dataDecls newDecls of
                          Left err -> outputError err
                          Right evaluated -> do
                            let
                              outputExpr = fromJust $ lookup (Name replRes) evaluated
                              typeInfo str
                                | replSetInfo = str ++ dullBlue ++ " : "
                                                ++ show (typeof outputExpr) ++ reset
                                | otherwise   = str
                              output = typeInfo $ show outputExpr
                              toExprs (x, y ::: t) = (x, Val y ::: t)
                            lift $ outputStrLn output
                            put $ ReplState
                              { replNextAnon = newAnon,
                                replNextExpr = replNextExpr+1,
                                replDecls = replDecls { valDecls = map toExprs evaluated },
                                replFirst = True,
                                .. }
                            repl

unfinished :: String -> Maybe Char
unfinished str = foldl (<|>) Nothing $ map check [('(', ')'), ('[', ']'), ('{', '}')]
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

changeValDecl :: (Name, Typed Expr) -> Decls -> Decls
changeValDecl val Decls {..} = Decls { valDecls = changeVal val valDecls, .. }

changeDataDecl :: (Name, DataDecl) -> Decls -> Decls
changeDataDecl data' Decls {..} = Decls { dataDecls = changeVal data' dataDecls, .. }

changeVal :: Eq k => (k, v) -> [(k, v)] -> [(k, v)]
changeVal entry [] = [entry]
changeVal entry (x:xs)
  | fst x == fst entry = entry : xs
  | otherwise          = x : changeVal entry xs

iterRepl :: String -> Repl ReplResult
iterRepl (':' : commands) = parseCommands commands
iterRepl string = do
  ReplState {..} <- get
  let parser = runCustomParser replNextAnon $ followedByEnd $ parseRepl replNextExpr
  case runParser parser "<repl>" string of
    Left err -> lift $ do
      outputStr (errorFmt ++ "syntax error: " ++ reset ++ errorBundlePretty err)
      return Ignore
    Right (state, nextAnon) -> do
      modify $ \s -> s { replNextAnon = nextAnon }
      return state

parseRepl :: Word64 -> Parser ReplResult
parseRepl n = try (DeclareVal <$> valDeclParser) <|> try (DeclareData <$> dataDeclParser) <|> (Eval <$> parseReplExpr n)

parseReplExpr :: Word64 -> Parser (Typed Expr)
parseReplExpr 0 = parser
parseReplExpr n = substitute (Name "res") (Id $ Name ("res" ++ show (n-1))) <$> parser

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
          "  :list [all]     list declarations (`all` includes results)",
          "  :info [on|off]  toggle info",
          "  :quit           exit the repl",
          "" ]
      return Ignore
    ("clear", _) -> clear >> return Ignore
    ("reset", _) -> clear >> return Reset
    ("list", "all") -> list True
    ("list", []) -> list False
    ("list", _) ->
      outputError "command `list` expects either no argument or `all`"
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

list :: Bool -> Repl ReplResult
list a = do
  decls <- gets replDecls
  let vals = valDecls decls
  lift $ sequence_ $ map (outputStrLn . showValDecl) $
    if a then
      vals
    else
      filter (not . invalidName . show . fst) vals
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

flushOut :: IO ()
flushOut = hFlush stdout

declsParser :: Parser Decls
declsParser = followedByEnd manyDecls
  where
    decl = addDataDecl <$> dataDeclParser
      <|> addValDecl <$> valDeclParser
    manyDecls = try (decl <*> manyDecls) <|> return emptyDecls

followedByEnd :: Parser a -> Parser a
followedByEnd p = do
  res <- p
  sc' >> eof
  return res
