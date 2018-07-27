module Main where

import Parser

import System.IO (hFlush, stdout)
import Data.Char
import Text.Megaparsec
import Text.Megaparsec.Char

main :: IO ()
main = putStrLn "\nType an expression to parse and evaluate it, type `:help` for options.\n" >> repl []

repl :: [[(String, Expr)]] -> IO ()
repl list = do
  putStr "birch> "
  hFlush stdout
  state <- getLine >>= iterRepl
  case state of
    Quit -> return ()
    Ignore -> repl list
    Eval expr -> do
      let res = eval list expr
      putStrLn (show res)
      repl [[("res", res)]]

data ReplState
  = Quit
  | Ignore
  | Eval Expr

iterRepl :: String -> IO ReplState
iterRepl line = expect $ parse parser "repl" line
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
    expect (Left err) = putStr (parseErrorPretty err) >> return Ignore
    expect (Right (c, e)) = run c e
    missexpr = putStrLn "expected expression after command" >> return Ignore
    noexpr = putStrLn "unexpected expression after command" >> return Ignore
    run [] (Just expr) = return (Eval expr)
    run [] Nothing = return Ignore
    run "eval" (Just expr) = return (Eval expr)
    run "repr" (Just expr) = putStrLn (show expr) >> return (Eval expr)
    run "help" Nothing = do
      putStrLn ""
      putStrLn "Commands:"
      putStrLn "  :eval <expr>  evaluate <expr> (default command)"
      putStrLn "  :repr <expr>  display representation of <expr>"
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

exprParserEnd :: Parser Expr
exprParserEnd = followedByEnd exprParser

followedByEnd :: Parser a -> Parser a
followedByEnd p = do
  res <- p
  sc' >> eof
  return res
