module Main where

import Infer
import Parser
import AST
import Compile

import System.IO (hFlush, stdout, readFile)
import System.Environment (getArgs)
import Data.Char
import Data.Word
import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Monad.State
import qualified Data.Map as Map

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> error "repl currently disabled" -- (FIXME) startRepl
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
  let parser = runStateT manyDeclEnd 0
  case runParser parser path file of
    Left err -> putStr ("SYNTAX ERROR: " ++ parseErrorPretty err)
    Right (vals, nextAnon) -> do
      putStr $ unlines $ map show vals
      header "inferred"
      case inferAll nextAnon $ declToList vals of
        Left err -> putStrLn ("ERROR: " ++ err)
        Right inferred -> do
          putStr $ unlines $ map show $ declFromList inferred
          header "compiled"
          testCompile inferred 64
  where
    header x = putStrLn ("\n-- " ++ x ++ " --\n")

-- startRepl :: IO ()
-- startRepl = do
--   putStrLn "\nType an expression to parse and evaluate it, type `:help` for options.\n"
--   repl
--
-- repl :: IO ()
-- repl = do
--   putStr "birch> "
--   hFlush stdout
--   state <- getLine >>= iterRepl
--   case state of
--     Quit -> return ()
--     Ignore -> repl
--     Eval expr ->
--       case eval [] expr of
--         Left err -> do
--           putStrLn ("RUNTIME ERROR: " ++ err)
--           repl
--         Right res -> do
--           putStrLn (show res ++ " : " ++ show (typeof expr))
--           repl
--
-- data ReplState
--   = Quit
--   | Ignore
--   | Eval (Typed Expr)
--
-- iterRepl :: String -> IO ReplState
-- iterRepl line = expect $ runParser (evalStateT parser 0) "repl" line
--   where
--     parser = do
--       c <- command <?> "command"
--       e <- (end <|> Just <$> exprParserEnd) <?> "repl expression"
--       return (c, e)
--     end = try $ symbol $ eof >> return Nothing
--     command = tryCommand <|> return []
--     tryCommand = do
--       sc' >> char ':'
--       c <- takeWhile1P Nothing isAlpha
--       sc' >> return c
--     expect (Left err) = putStr ("SYNTAX ERROR: " ++ parseErrorPretty err) >> return Ignore
--     expect (Right (c, Nothing)) = run c Nothing
--     expect (Right (c, Just e)) =
--       case infer (Map.empty) e of
--         Left err -> putStrLn ("ERROR: " ++ err) >> return Ignore
--         Right expr -> run c $ Just expr
--
-- run :: String -> Maybe (Typed Expr) -> IO ReplState
-- run [] (Just expr) = return (Eval expr)
-- run [] Nothing = return Ignore
-- run "eval" (Just expr) = return (Eval expr)
-- run "repr" (Just expr) = putStrLn (show expr) >> return (Eval expr)
-- run "help" Nothing = do
--   putStrLn ""
--   putStrLn "Commands:"
--   putStrLn "  :eval <expr>  evaluate an expression (default command)"
--   putStrLn "  :repr <expr>  display representation of an expression"
--   putStrLn "  :help         display this help menu"
--   putStrLn "  :clear        clear the display"
--   putStrLn "  :quit         exit the repl"
--   putStrLn ""
--   return Ignore
-- run "clear" Nothing = putStr "\x1b[3J\x1b[H\x1b[2J" >> hFlush stdout >> return Ignore
-- run "quit" Nothing = return Quit
-- run "eval" _ = missexpr
-- run "repr" _ = missexpr
-- run "help" _ = noexpr
-- run "clear" _ = noexpr
-- run "quit" _ = noexpr
-- run other _ = putStrLn ("unknown command: `" ++ other ++ "`") >> return Ignore
--
-- missexpr :: IO ReplState
-- missexpr = putStrLn "expected expression after command" >> return Ignore
--
-- noexpr :: IO ReplState
-- noexpr = putStrLn "unexpected expression after command" >> return Ignore

manyDeclEnd :: Parser [Decl]
manyDeclEnd = followedByEnd manyDecl
  where
    someDecl = do
      decl <- declParser
      others <- manyDecl
      return (decl : others)
    manyDecl = try someDecl <|> return []

exprParserEnd :: Parser (Typed Expr)
exprParserEnd = followedByEnd exprParser

followedByEnd :: Parser a -> Parser a
followedByEnd p = do
  res <- p
  sc' >> eof
  return res
