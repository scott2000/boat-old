{-# LANGUAGE FlexibleInstances #-}

module Parser ( MParser, Parser, Parsable (..), valDeclParser, parser, symbol, sc, sc' ) where

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

class Parsable a where
  parsePartial :: Parser a
  parsedOp :: String -> a -> a -> Parser a
  parsedApp :: a -> a -> Parser a

valDeclParser :: Parser (Name, Typed Expr)
valDeclParser = do
  try $ symbol $ key "val"
  name <- name
  ty <- parseAscription
  symbol $ string "="
  expr <- parser
  return (name, ascribe expr ty)

parser :: Parsable a => Parser a
parser = symbol $ (parserPrec minPrec)

instance Parsable (Typed Expr) where
  parsePartial = maybeRetype $ try paren
    <|> try (typed function)
    <|> try (typed letbinding)
    <|> try (typed ifThenElse)
    <|> try (typed (Id <$> name))
    <|> try (symbol $ key "unit" >> return (Val Unit ::: tUnit))
    <|> try (symbol $ key "true" >> return (Val (Bool True) ::: tBool))
    <|> try (symbol $ key "false" >> return (Val (Bool False) ::: tBool))
    <|> (::: tNat) <$> Val <$> Nat <$> number

  parsedOp "->" _ _ = error ("cannot use (->) operator in expression")
  parsedOp op a b = typed $ return $ Op op a b

  parsedApp a b = typed $ return $ App a b

instance Parsable Type where
  parsePartial = try paren
    <|> try (tIdVar <$> identifier)
    <|> (symbol $ key "_" >> newType)

  parsedOp "->" a b = return $ TFunc a b
  parsedOp op _ _ = error ("cannot use (" ++ op ++ ") operator in type")

  parsedApp a b = error ("cannot use application in type")

parserPrec :: Parsable a => (Prec, Assoc) -> Parser a
parserPrec = parserBase parsePartial
  where
  parserBase base prec = do
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
              other <- parserPrec newPrec
              parserBase (parsedOp op expr other) prec
        else
          error ("cannot use operator of kind " ++ show kind ++ " here")
      appExpr expr =
        case precError prec appPrec of
          Just err -> fail err
          Nothing -> do
            other <- parserPrec appPrec
            parserBase (parsedApp expr other) prec

symbol :: Parser a -> Parser a
symbol p = sc' >> p

comment :: Parser ()
comment = hidden $ skipMany $ choice [lineCmnt, blockCmnt]

sc :: Parser ()
sc = hidden $ skipSome $ choice [space1, lineCmnt, blockCmnt]

sc' :: Parser ()
sc' = hidden $ skipMany $ choice [space1, lineCmnt, blockCmnt]

letbinding :: Parser Expr
letbinding = do
  symbol $ key "let"
  name <- typed name
  symbol $ char '='
  val <- parser
  symbol $ key "in"
  expr <- parser
  return (Let name val expr) <?> "let binding"

function :: Parser Expr
function = do
  symbol $ (char '\\' <|> char '\x3bb')
  vars <- manyIdents
  symbol $ (string "->" <|> string "\x2192")
  expr <- parser
  case vars of
    [] -> fail "functions must have at least one parameter (\\ -> ... is not allowed)"
    xs -> return (Val (Func xs expr)) <?> "function literal"
  where
    someIdents = do
      ident <- typed name
      others <- manyIdents
      return (ident : others)
    manyIdents = try someIdents <|> return []

ifThenElse :: Parser Expr
ifThenElse = do
  symbol $ key "if"
  i <- parser
  symbol $ key "then"
  t <- parser
  symbol $ key "else"
  e <- parser
  return (If i t e) <?> "if-then-else"

number :: Parser Word64
number = symbol (try (char '0' >> char 'x' >> L.hexadecimal) <|> L.decimal) <?> "number"

paren :: Parsable a => Parser a
paren = do
  symbol $ char '('
  expr <- parser
  symbol $ char ')'
  return expr

keywords :: [String]
keywords = ["val", "let", "in", "unit", "true", "false", "if", "then", "else", "_"]

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
typed p = (:::) <$> p <*> newType

maybeRetype :: Parser (Typed a) -> Parser (Typed a)
maybeRetype p = ascribe <$> p <*> parseAscription

parseAscription :: Parser (Maybe Type)
parseAscription = (<|> return Nothing) $ do
  try $ symbol $ char ':'
  Just <$> parser

ascribe :: Typed a -> (Maybe Type) -> Typed a
ascribe (x ::: old) (Just new) =
  case earlyUnify old new of
    Just ty -> (x ::: ty)
    Nothing -> error ("cannot ascribe type " ++ show new ++ " to expression of type " ++ show old)
ascribe expr Nothing = expr

earlyUnify :: Type -> Type -> Maybe Type
earlyUnify (TAnon _) t = Just t
earlyUnify t (TAnon _) = Just t
earlyUnify (TFunc a0 b0) (TFunc a1 b1) =
  TFunc <$> earlyUnify a0 a1 <*> earlyUnify b0 b1
earlyUnify a b
  | a == b    = Just a
  | otherwise = Nothing

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

reservedOps :: [String]
reservedOps = [":", "."]

operator :: Parser String
operator = do
  op <- (some $ oneOf "+-*/%^!=<>:?|&~$.") <?> "operator"
  if op `elem` reservedOps then
    fail ("keyword operator (" ++ op ++ ") not allowed here")
  else
    return op

operatorInContext :: Parser (String, OpKind)
operatorInContext = widePrefix <|> postfixCompact
  where
    followed k = do
      lookAhead sc
      return k
    widePrefix = do
      try sc
      op <- operator
      kind <- followed Wide <|> return Prefix
      return (op, kind)
    postfixCompact = do
      op <- operator
      kind <- followed Postfix <|> return Compact
      return (op, kind)

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
  [ (["->"], (0, ARight)),
    (["||"], (2, ARight)),
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
