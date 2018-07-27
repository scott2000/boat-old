module Parser ( Expr (..), Type (..), Parser, eval, (!?), exprParser, symbol, sc, sc' ) where

import Data.Maybe
import Data.Void
import Data.Word
import Data.Char
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

data Expr
  = Nat Data.Word.Word64
  | Bool Bool
  | Op String Expr Expr
  | App Expr Expr
  | Id String
  | Let String Expr Expr
  | Func String [String] Expr
  deriving Eq

data Type
  = TVar Word64
  | TNat
  | TBool
  | TFunc Type Type
  deriving Eq

instance Show Expr where
  show (Nat n) = show n
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Op op a b) = "(" ++ show a ++ " " ++ op ++ " " ++ show b ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Id name) = name
  show (Let name val expr) = "(let " ++ name ++ " = " ++ show val ++ " in " ++ show expr ++ ")"
  show (Func x xs expr) = "(\\" ++ x ++ " " ++ unwords xs ++ " -> " ++ show expr ++ ")"

eval :: [[(String, Expr)]] -> Expr -> Expr
eval l (Op op a b) = runOp op (eval l a) (eval l b)
eval l (App a b) =
  case (eval l a, eval l b) of
    (Func x [] expr, param) ->
      eval ([(x, eval l param)]:l) expr
    (Func x (y:xs) expr, param) ->
      Func y xs (eval ([(x, eval l param)]:l) expr)
    (a, b) -> App a b
eval l (Id name) =
  case name !? l of
    Just x -> x
    Nothing -> Id name
eval l (Let name val expr) =
  eval ([(name, eval l val)]:l) expr
eval l (Func x xs expr) = Func x xs (eval l expr)
eval _ x = x

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

type Parser = Parsec Void String

exprParser :: Parser Expr
exprParser = symbol $ exprParserPrec minPrec

exprParserPartial :: Parser Expr
exprParserPartial = try paren
  <|> try function
  <|> try letbinding
  <|> Id <$> try identifier
  <|> try (symbol $ key "true" >> return (Bool True))
  <|> try (symbol $ key "false" >> return (Bool False))
  <|> Nat <$> number
  <?> "expression"

exprParserPrec :: (Prec, Assoc) -> Parser Expr
exprParserPrec = exprParserBase exprParserPartial

exprParserBase :: Parser Expr -> (Prec, Assoc) -> Parser Expr
exprParserBase base prec = do
  expr <- base
  try (opExpr expr) <|> try (appExpr expr) <|> return expr
  where
    opExpr expr = do
      (op, kind) <- operatorInContext
      if isInfix kind then
        let newPrec = adjustPrec kind $ precedence op in
        case precError prec newPrec of
          Just err -> fail err
          Nothing -> do
            other <- exprParserPrec newPrec
            exprParserBase (return (Op op expr other)) prec
      else
        error ("cannot use operator of kind " ++ show kind ++ " here")
    appExpr expr =
      case precError prec appPrec of
        Just err -> fail err
        Nothing -> do
          other <- exprParserPrec appPrec
          exprParserBase (return (App expr other)) prec

symbol :: Parser a -> Parser a
symbol p = sc' >> p

sc :: Parser ()
sc = hidden (skipSome $ choice [space1, lineCmnt, blockCmnt])

sc' :: Parser ()
sc' = hidden (skipMany $ choice [space1, lineCmnt, blockCmnt])

letbinding :: Parser Expr
letbinding = do
  symbol $ key "let"
  name <- identifier
  symbol $ char '='
  val <- exprParser
  symbol $ key "in"
  expr <- exprParser
  return (Let name val expr)

function :: Parser Expr
function = do
  symbol $ char '\\'
  vars <- manyIdents
  symbol $ string "->"
  expr <- exprParser
  case vars of
    [] -> fail "functions must have at least one parameter (\\ -> ... is not allowed)"
    (x:xs) -> return (Func x xs expr)
  where
    someIdents = do
      ident <- symbol identifier
      others <- manyIdents
      return (ident : others)
    manyIdents = try someIdents <|> return []

number :: Parser Word64
number = symbol (try (char '0' >> char 'x' >> L.hexadecimal) <|> L.decimal) <?> "number"

paren :: Parser Expr
paren = do
  symbol $ char '('
  expr <- exprParser
  symbol $ char ')'
  return expr

keywords :: [String]
keywords = ["let", "in", "true", "false"]

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

natOps :: [(String, Word64 -> Word64 -> Word64)]
natOps =
  [ ("+", (+)),
    ("-", (-)),
    ("*", (*)),
    ("/", quot),
    ("%", rem),
    ("^", (^)) ]

natCmpOps :: [(String, Word64 -> Word64 -> Bool)]
natCmpOps =
  [ ("<", (<)),
    (">", (>)),
    ("<=", (<=)),
    (">=", (>=)),
    ("==", (==)),
    ("!=", (/=)) ]

boolOps :: [(String, Bool -> Bool -> Bool)]
boolOps =
  [ ("||", (||)),
    ("&&", (&&)),
    ("==", (==)),
    ("!=", (/=)) ]

tryOp :: String -> a -> a -> (b -> Expr) -> [(String, a -> a -> b)] -> Maybe Expr
tryOp _ _ _ _ [] = Nothing
tryOp op a b c ((x, y):xs) =
  if x == op then
    Just $ c $ y a b
  else
    tryOp op a b c xs

runOp :: String -> Expr -> Expr -> Expr
runOp op (Nat a) (Nat b) =
  fromMaybe (Op op (Nat a) (Nat b))
    (tryOp op a b Nat natOps <|> tryOp op a b Bool natCmpOps)
runOp op (Bool a) (Bool b) =
  fromMaybe (Op op (Bool a) (Bool b))
    (tryOp op a b Bool boolOps)
runOp op a b = Op op a b

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
  else if not (w `elem` keywords) then
    error ("not a keyword: " ++ w)
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

lineCmnt :: Parser ()
lineCmnt = L.skipLineComment "--"

blockCmnt :: Parser ()
blockCmnt = L.skipBlockCommentNested "{-" "-}"

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
