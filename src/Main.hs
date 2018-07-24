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

isInfix :: OpKind -> Bool
isInfix Wide = True
isInfix Compact = True
isInfix _ = False

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

eval :: [[(String, Expr)]] -> Expr -> Expr
eval l (Op op a b) = runOp op (eval l a) (eval l b)
eval l (Id name) =
  case name !? l of
    Just x -> x
    Nothing -> Id name
eval l (Let name val expr) =
  eval ([(name, eval l val)]:l) expr
eval _ x = x

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
main = putStrLn "\nType an expression to parse and evaluate it, leave blank to exit.\n" >> repl []

repl :: [[(String, Expr)]] -> IO ()
repl list = do
  putStr "> "
  hFlush stdout
  testCode <- getLine
  if null testCode then
    return ()
  else
    case parse (wholeFile exprParserDefault) "test" testCode of
      Left err -> do
        putStr ("ERROR: "++ parseErrorPretty err)
        repl list
      Right expr -> do
        let res = eval list expr
        putStrLn (show res)
        repl [[("repr", expr), ("res", res)]]

wholeFile :: Parser a -> Parser a
wholeFile p = do
  res <- p
  sc' >> eof
  return res

type Parser = Parsec Void String

word :: Parser String
word = do
  first <- satisfy isIdentFirst
  rest <- takeWhileP Nothing isIdentRest
  return (first:rest) <?> "identifier"
  where
    isIdentFirst x = (isAlpha x || x == '_') && isAscii x
    isIdentRest x = (isAlpha x || isDigit x || x == '_') && isAscii x

identifier :: Parser String
identifier = symbol $ do
  ident <- word
  if ident `elem` keywords then
    fail ("expected an identifier, found keyword `" ++ ident ++ "`")
  else
    return ident

key :: String -> Parser ()
key w = do
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
  symbol $ key "let"
  name <- identifier
  symbol $ char '='
  val <- exprParserDefault
  symbol $ key "in"
  expr <- exprParserDefault
  return (Let name val expr)

number :: Parser Word64
number = symbol (try (char '0' >> char 'x' >> L.hexadecimal) <|> L.decimal) <?> "number"

paren :: Parser Expr
paren = do
  symbol $ char '('
  expr <- exprParserDefault
  symbol $ char ')'
  return expr

exprParser1 :: Parser Expr
exprParser1 = try paren
  <|> try letbinding
  <|> Id <$> try identifier
  <|> try (symbol $ key "true" >> return (Bool True))
  <|> try (symbol $ key "false" >> return (Bool False))
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
      if isInfix kind then
        let newPrec = adjustPrec kind $ precedence op in
        case precError prec newPrec of
          Just err -> fail err
          Nothing -> do
            other <- exprParser newPrec
            exprParserBase (return (Op op expr other)) prec
      else
        error ("cannot use operator of kind " ++ show kind ++ " here")

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
      error ("cannot mix associativities of operators in same precedence level (" ++ show p0 ++ ")")
    else if a0 == ALeft then
      Just "left-assoc"
    else if a0 == ANon then
      error "non-associative operator chaining not allowed"
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
    (["::"], (5, ARight)),
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
