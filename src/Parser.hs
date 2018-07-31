module Parser ( Parser, valParser, exprParser, symbol, sc, sc' ) where

import AST

import Data.Void
import Data.Word
import Data.Char
import Control.Monad.State
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type MParser = Parsec Void String
type Parser = StateT Word64 MParser

valParser :: Parser Decl
valParser = do
  key "val"
  name <- name
  symbol $ string "="
  expr <- exprParser
  return (Decl name expr)

exprParser :: Parser (Typed Expr)
exprParser = symbol $ exprParserPrec minPrec

exprParserPartial :: Parser (Typed Expr)
exprParserPartial = try paren
  <|> try (typed function)
  <|> try (typed letbinding)
  <|> try (typed ifThenElse)
  <|> try (typed (Id <$> name))
  <|> try (symbol $ key "true" >> return (Lit (Bool True) ::: tBool))
  <|> try (symbol $ key "false" >> return (Lit (Bool False) ::: tBool))
  <|> (::: tNat) <$> Lit <$> Nat <$> number

exprParserPrec :: (Prec, Assoc) -> Parser (Typed Expr)
exprParserPrec = exprParserBase exprParserPartial

exprParserBase :: Parser (Typed Expr) -> (Prec, Assoc) -> Parser (Typed Expr)
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
            exprParserBase (typed (return (Op op expr other))) prec
      else
        error ("cannot use operator of kind " ++ show kind ++ " here")
    appExpr expr =
      case precError prec appPrec of
        Just err -> fail err
        Nothing -> do
          other <- exprParserPrec appPrec
          exprParserBase (typed (return (App expr other))) prec

symbol :: Parser a -> Parser a
symbol p = sc' >> p

sc :: Parser ()
sc = hidden (skipSome $ choice [space1, lineCmnt, blockCmnt])

sc' :: Parser ()
sc' = hidden (skipMany $ choice [space1, lineCmnt, blockCmnt])

letbinding :: Parser Expr
letbinding = do
  symbol $ key "let"
  name <- typed name
  symbol $ char '='
  val <- exprParser
  symbol $ key "in"
  expr <- exprParser
  return (Let name val expr) <?> "let binding"

function :: Parser Expr
function = do
  symbol $ char '\\'
  vars <- manyIdents
  symbol $ string "->"
  expr <- exprParser
  case vars of
    [] -> fail "functions must have at least one parameter (\\ -> ... is not allowed)"
    xs -> return (Func xs expr) <?> "function literal"
  where
    someIdents = do
      ident <- typed name
      others <- manyIdents
      return (ident : others)
    manyIdents = try someIdents <|> return []

ifThenElse :: Parser Expr
ifThenElse = do
  symbol $ key "if"
  i <- exprParser
  symbol $ key "then"
  t <- exprParser
  symbol $ key "else"
  e <- exprParser
  return (If i t e) <?> "if-then-else"

number :: Parser Word64
number = symbol (try (char '0' >> char 'x' >> L.hexadecimal) <|> L.decimal) <?> "number"

paren :: Parser (Typed Expr)
paren = do
  symbol $ char '('
  expr <- exprParser
  symbol $ char ')'
  return expr

keywords :: [String]
keywords = ["val", "let", "in", "true", "false", "if", "then", "else"]

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

name :: Parser Name
name = Name <$> identifier

typed :: Parser a -> Parser (Typed a)
typed x = do
  new <- x
  ty <- newType
  return (new ::: ty)

newType :: Monad m => StateT Word64 m Type
newType = do
  var <- get
  put $ var+1
  return (TAnon var)

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
