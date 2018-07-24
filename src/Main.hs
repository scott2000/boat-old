module Main where

import System.IO (hFlush, stdout)
import Control.Monad (void, forever)
import Data.Void
import Data.Word
import Data.Char
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

keywords :: [String]
keywords = ["val", "if", "then", "else", "true", "false"]

data OpKind
  = Wide
  | Prefix
  | Postfix
  | Compact
  deriving (Show, Eq)

data Assoc
  = ALeft
  | ANon
  | ARight
  deriving (Show, Eq)

type Prec = Int

data Expr
  = Nat Data.Word.Word64
  | Bool Bool
  | Op String Expr Expr
  | Id String
  | Let String Expr Expr
  deriving Eq

instance Show Expr where
  show (Nat n) = show n
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Op op a b) = "(" ++ show a ++ " " ++ op ++ " " ++ show b ++ ")"
  show (Id name) = name
  show (Let name val expr) = "(let " ++ name ++ " = " ++ show val ++ " in " ++ show expr ++ ")"

eval :: Expr -> Expr
eval = f []
  where
    runOp :: String -> Expr -> Expr -> Expr
    runOp op (Nat a) (Nat b) =
      case op of
        "+" -> Nat $ a+b
        "-" -> Nat $ a-b
        "*" -> Nat $ a*b
        "/" -> Nat $ quot a b
        "%" -> Nat $ rem a b
        "^" -> Nat $ a^b
        ">" -> Bool $ a>b
        "<" -> Bool $ a<b
        ">=" -> Bool $ a>=b
        "<=" -> Bool $ a<=b
        "==" -> Bool $ a==b
        "!=" -> Bool $ a/=b
        _   -> Op op (Nat a) (Nat b)
    runOp op (Bool a) (Bool b) =
      case op of
        "||" -> Bool $ a||b
        "&&" -> Bool $ a&&b
        "==" -> Bool $ a==b
        "!=" -> Bool $ a/=b
        _   -> Op op (Bool a) (Bool b)
    runOp op a b = Op op a b

    f :: [[(String, Expr)]] -> Expr -> Expr
    f l (Op op a b) = runOp op (f l a) (f l b)
    f l (Id name) =
      case name !? l of
        Just x -> x
        Nothing -> Id name
    f l (Let name val expr) =
      f ([(name, f l val)]:l) expr
    f _ x = x

(!?) :: Eq k => k -> [[(k, v)]] -> Maybe v
(!?) _ [] = Nothing
(!?) key (list:rest) =
  case find key list of
    Just v -> Just v
    Nothing -> key !? rest
  where
    find _ [] = Nothing
    find key ((k, v):rest)
      | k == key = Just v
      | otherwise = find key rest

main :: IO ()
main = forever $ do
  putStr "\n> "
  hFlush stdout
  testCode <- getLine
  case parse (wholeFile exprParserDefault) "test" testCode of
    Left err -> putStr ("ERROR: "++ parseErrorPretty err)
    Right expr -> displayResults expr

wholeFile :: Parser a -> Parser a
wholeFile p = do
  res <- p
  eof
  return res

displayResults :: Expr -> IO ()
displayResults expr = do
  putStrLn (show expr)
  putStrLn (" => " ++ show (eval expr))

type Parser = Parsec Void String

word :: Parser String
word = do
  first <- satisfy isIdentFirst
  rest <- takeWhileP Nothing isIdentRest
  symbol (return (first:rest)) <?> "identifier"
  where
    isIdentFirst x = (isAlpha x || x == '_') && isAscii x
    isIdentRest x = (isAlpha x || isDigit x || x == '_') && isAscii x

identifier :: Parser String
identifier = try $ symbol $ do
  ident <- word
  if ident `elem` keywords then
    fail ("expected an identifier, found keyword `" ++ ident ++ "`")
  else
    return ident

key :: String -> Parser ()
key w = try $ symbol $ do
  ident <- word
  if ident /= w then
    fail ("expected keyword `" ++ w ++ "`, found `" ++ ident ++ "`")
  else
    return ()

operator :: Parser String
operator = (some $ oneOf "+-*/%^!=<>:?|&~$.") <?> "operator"

operatorInContext :: Parser (String, OpKind)
operatorInContext = try wide <|> try prefix <|> try postfix <|> compact
  where
    wide = do
      sc
      op <- operator
      lookAhead sc
      return (op, Wide)
    prefix = do
      sc
      op <- operator
      return (op, Prefix)
    postfix = do
      op <- operator
      lookAhead sc
      return (op, Postfix)
    compact = do
      op <- operator
      return (op, Compact)

lineCmnt = L.skipLineComment "--"
blockCmnt = L.skipBlockCommentNested "{-" "-}"

sc :: Parser ()
sc = (skipSome $ choice [space1, lineCmnt, blockCmnt]) <?> "whitespace"

sc' :: Parser ()
sc' = (skipMany $ choice [space1, lineCmnt, blockCmnt]) <?> "whitespace"

symbol :: Parser a -> Parser a
symbol p = sc' >> p

letbinding :: Parser Expr
letbinding = do
  key "let"
  name <- identifier
  sc' >> string "=" >> sc'
  val <- exprParserDefault
  key "in"
  expr <- exprParserDefault
  return (Let name val expr)

number :: Parser Word64
number = try (symbol (try (char '0' >> char 'x' >> L.hexadecimal) <|> L.decimal)) <?> "number"

bool :: Parser Bool
bool = try (symbol (try (key "true" >> return True) <|> (key "false" >> return False))) <?> "boolean"

paren :: Parser Expr
paren = do
  try $ symbol $ char '('
  expr <- exprParserDefault
  symbol $ char ')'
  return expr

exprParser1 :: Parser Expr
exprParser1 = paren
  <|> letbinding
  <|> Id <$> identifier
  <|> Bool <$> bool
  <|> Nat <$> number
  <?> "expression"

exprParser :: (Prec, Assoc) -> Parser Expr
exprParser = exprParserBase exprParser1

exprParserBase :: Parser Expr -> (Prec, Assoc) -> Parser Expr
exprParserBase base prec =
  try (opExpr prec) <|> base
  where
    opExpr prec = do
      expr <- base
      (op, kind) <- operatorInContext
      let newPrec = adjustPrec kind $ precedence op
      case precError prec newPrec of
        Just err -> fail err
        Nothing -> do
          other <- exprParser newPrec
          exprParserBase (return (Op op expr other)) prec

exprParserDefault :: Parser Expr
exprParserDefault = symbol $ exprParser minPrec

minPrec :: (Prec, Assoc)
minPrec = (-1, ANon)

defaultPrec :: (Prec, Assoc)
defaultPrec = (9, ALeft)

appPrec :: (Prec, Assoc)
appPrec = (10, ALeft)

maxPrec :: (Prec, Assoc)
maxPrec = (21, ANon)

precError :: (Prec, Assoc) -> (Prec, Assoc) -> Maybe String
precError (p0, a0) (p1, a1)
  | p0 == p1 =
    if a0 /= a1 then
      Just ("cannot mix associativities of operators in same precedence level (" ++ show p0 ++ ")")
    else if a0 == ALeft then
      Just "left-assoc"
    else if a0 == ANon then
      Just "non-associative operator chaining not allowed"
    else
      Nothing
  | p0 > p1 = Just "high-prec"
  | otherwise = Nothing


adjustPrec :: OpKind -> (Prec, Assoc) -> (Prec, Assoc)
adjustPrec Wide x = x
adjustPrec _ (p, a) = (p+offset, a)
  where offset = 11

precTable :: [([String], (Prec, Assoc))]
precTable =
  [ (["||"], (2, ARight)),
    (["&&"], (3, ARight)),
    (["==", "!=", "<", "<=", ">", ">="], (4, ANon)),
    (["+", "-"], (6, ALeft)),
    (["*", "/", "%"], (7, ALeft)),
    (["^"], (8, ARight)) ]

precedence :: String -> (Prec, Assoc)
precedence = plook precTable
  where
    plook [] x = defaultPrec
    plook ((s, p):rest) x
      | x `elem` s = p
      | otherwise = plook rest x
