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
    Eval expr ty ->
      case eval [] expr of
        Left err -> do
          putStrLn ("EVAL ERROR: " ++ err)
          repl
        Right res -> do
          putStrLn $ case ty of
            Just ty -> show res ++ " : " ++ show ty
            Nothing -> show res
          repl

data ReplState
  = Quit
  | Ignore
  | Eval Expr (Maybe Type)

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
    expect (Left err) = putStr ("PARSE ERROR: " ++ parseErrorPretty err) >> return Ignore
    expect (Right (c, Nothing)) = run c Nothing
    expect (Right (c, Just e)) =
      case infer e of
        Left err -> putStrLn ("INFER ERROR: " ++ err) >> return Ignore
        Right expr -> run c $ Just expr

run :: String -> Maybe (Expr, Type) -> IO ReplState
run [] (Just (expr, _)) = return (Eval expr Nothing)
run [] Nothing = return Ignore
run "eval" (Just (expr, _)) = return (Eval expr Nothing)
run "repr" (Just (expr, ty)) = putStrLn (show expr ++ " : " ++ show ty) >> return (Eval expr Nothing)
run "type" (Just (expr, ty)) = return (Eval expr (Just ty))
run "help" Nothing = do
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :eval <expr>  evaluate an expression (default command)"
  putStrLn "  :repr <expr>  display representation of an expression"
  putStrLn "  :type <expr>  display the type of the result"
  putStrLn "  :help         display this help menu"
  putStrLn "  :clear        clear the display"
  putStrLn "  :quit         exit the repl"
  putStrLn ""
  return Ignore
run "clear" Nothing = putStr "\x1b[3J\x1b[H\x1b[2J" >> hFlush stdout >> return Ignore
run "quit" Nothing = return Quit
run "eval" _ = missexpr
run "repr" _ = missexpr
run "type" _ = missexpr
run "help" _ = noexpr
run "clear" _ = noexpr
run "quit" _ = noexpr
run other _ = putStrLn ("unknown command: `" ++ other ++ "`") >> return Ignore

missexpr :: IO ReplState
missexpr = putStrLn "expected expression after command" >> return Ignore

noexpr :: IO ReplState
noexpr = putStrLn "unexpected expression after command" >> return Ignore

exprParserEnd :: Parser Expr
exprParserEnd = followedByEnd exprParser

followedByEnd :: Parser a -> Parser a
followedByEnd p = do
  res <- p
  sc' >> eof
  return res
