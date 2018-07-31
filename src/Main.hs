module Main where

import Infer
import Parser
import AST

import System.IO (hFlush, stdout)
import Data.Char
import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Monad.State

main :: IO ()
main = putStrLn "\nType an expression to parse and evaluate it, type `:help` for options.\n" >> repl

repl :: IO ()
repl = do
  putStr "birch> "
  hFlush stdout
  state <- getLine >>= iterRepl
  case state of
    Quit -> return ()
    Ignore -> repl
    Eval expr ->
      case eval [] expr of
        Left err -> do
          putStrLn ("RUNTIME ERROR: " ++ err)
          repl
        Right res -> do
          putStrLn (show res ++ " : " ++ show (typeof expr))
          repl

data ReplState
  = Quit
  | Ignore
  | Eval (Typed Expr)

iterRepl :: String -> IO ReplState
iterRepl line = expect $ runParser (evalStateT parser 0) "repl" line
  where
    parser = do
      c <- command <?> "command"
      e <- (end <|> Just <$> exprParserEnd) <?> "repl expression"
      return (c, e)
    end = try $ symbol $ eof >> return Nothing
    command = tryCommand <|> return []
    tryCommand = do
      sc' >> char ':'
      c <- takeWhile1P Nothing isAlpha
      sc' >> return c
    expect (Left err) = putStr ("SYNTAX ERROR: " ++ parseErrorPretty err) >> return Ignore
    expect (Right (c, Nothing)) = run c Nothing
    expect (Right (c, Just e)) =
      case infer e of
        Left err -> putStrLn ("ERROR: " ++ err) >> return Ignore
        Right expr -> run c $ Just expr

run :: String -> Maybe (Typed Expr) -> IO ReplState
run [] (Just expr) = return (Eval expr)
run [] Nothing = return Ignore
run "eval" (Just expr) = return (Eval expr)
run "repr" (Just expr) = putStrLn (show expr) >> return (Eval expr)
run "help" Nothing = do
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :eval <expr>  evaluate an expression (default command)"
  putStrLn "  :repr <expr>  display representation of an expression"
  putStrLn "  :help         display this help menu"
  putStrLn "  :clear        clear the display"
  putStrLn "  :quit         exit the repl"
  putStrLn ""
  return Ignore
run "clear" Nothing = putStr "\x1b[3J\x1b[H\x1b[2J" >> hFlush stdout >> return Ignore
run "quit" Nothing = return Quit
run "eval" _ = missexpr
run "repr" _ = missexpr
run "help" _ = noexpr
run "clear" _ = noexpr
run "quit" _ = noexpr
run other _ = putStrLn ("unknown command: `" ++ other ++ "`") >> return Ignore

missexpr :: IO ReplState
missexpr = putStrLn "expected expression after command" >> return Ignore

noexpr :: IO ReplState
noexpr = putStrLn "unexpected expression after command" >> return Ignore

exprParserEnd :: Parser (Typed Expr)
exprParserEnd = followedByEnd exprParser

followedByEnd :: Parser a -> Parser a
followedByEnd p = do
  res <- p
  sc' >> eof
  return res
