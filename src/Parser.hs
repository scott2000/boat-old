{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

module Parser where
import AST

import Data.Void
import Data.Word
import Data.Char
import Control.Monad.State
import Control.Monad.Reader
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Set as Set

-- The minimum possible indentation
type LinePosition = Int

-- The number of anonymous types assigned
type AnonCount = Word64

type MParser = Parsec Void String
type Parser = ReaderT LinePosition (StateT AnonCount MParser)

runCustomParser :: AnonCount -> Parser a -> MParser (a, AnonCount)
runCustomParser c p = runStateT (runReaderT p 0) c

anyIndent :: Parser a -> Parser a
anyIndent = withLevel 0

blockOf :: Parser a -> Parser a
blockOf p = do
  anySpaceChunk
  current <- ask
  level <- (subtract 1 . unPos) <$> L.indentLevel
  if level < current then
    error ("block indented less then containing block (" ++ show level ++ " < " ++ show current ++ ")")
  else
    withLevel level p

withLevel :: Int -> Parser a -> Parser a
withLevel level p = lift $ runReaderT p level

class Parsable a where
  parsePartial :: Parser a
  parsedOp :: String -> a -> a -> Parser a
  parsedApp :: a -> a -> Parser a

keywords :: [String]
keywords = ["data", "val", "let", "match", "in", "unit", "true", "false", "if", "then", "else", "panic", "_"]

valDeclParser :: Parser (Name, Typed Expr)
valDeclParser = label "value declaration" $ do
  try $ symbol $ key "val"
  name <- name
  ty <- parseAscription
  symbol $ string "="
  expr <- parser
  return (name, ascribe expr ty)

dataDeclParser :: Parser (Name, DataDecl)
dataDeclParser = label "data declaration" $ do
  try $ symbol $ key "data"
  (name, typeParams) <- variant
  symbol $ string "="
  variants <- multiline <|> singleline
  return (name, DataDecl { typeParams = map into typeParams, variants })
  where
    into (TVar s) = s
    into other = error ("data declaration expected type variables, found other type: " ++ show other)
    multiline = do
      try $ symbol $ string "|"
      singleline
    manyVariants = many $ do
      try $ symbol $ string "|"
      variant
    singleline = (:) <$> variant <*> manyVariants

variant :: Parser (Name, [Type])
variant = symbol $ do
  name <- name
  types <- many (try parserNoSpace)
  return (name, types)

parser :: Parsable a => Parser a
parser = symbol $ (parserPrec minPrec)

parserNoSpace :: Parsable a => Parser a
parserNoSpace = symbol $ (parserPrec appPrec)

instance Parsable (Typed Expr) where
  parsePartial = label "expression" $ maybeRetype $ paren
    <|> typed function
    <|> typed letbinding
    <|> typed matchbinding
    <|> typed ifThenElse
    <|> typed panic
    <|> try (typed (Id <$> name))
    <|> try (symbol $ key "unit" >> return (Val Unit ::: TUnit))
    <|> try (symbol $ key "true" >> return (Val (Bool True) ::: TBool))
    <|> try (symbol $ key "false" >> return (Val (Bool False) ::: TBool))
    <|> (::: TNat) <$> Val <$> Nat <$> number

  parsedOp "->" _ _ = fail ("cannot use (->) operator in expression")
  parsedOp op a b = typed $ return $ Op op a b

  parsedApp a b = typed $ return $ App a b

instance Parsable Type where
  parsePartial = label "type" $ try paren
    <|> try (tIdVar <$> identifier)
    <|> (symbol $ key "_" >> newType)

  parsedOp "->" a b = return $ TFunc a b
  parsedOp op _ _ = fail ("cannot use (" ++ op ++ ") operator in type")

  parsedApp a b = return $ TApp a b

instance Parsable (Typed Pattern) where
  parsePartial = label "pattern" $ maybeRetype $ paren
    <|> try (typed (pIdVar <$> identifier))
    <|> try (symbol $ key "_" >> typed (return $ PAny Nothing))
    <|> try (symbol $ key "unit" >> return (PAny Nothing ::: TUnit))
    <|> try (symbol $ key "true" >> return (PBool True ::: TBool))
    <|> try (symbol $ key "false" >> return (PBool False ::: TBool))
    <|> (::: TNat) <$> PNat <$> number

  parsedOp op _ _ = fail ("cannot use (" ++ op ++ ") operator in pattern")

  parsedApp (PCons name xs ::: _) x = typed $ return $ PCons name (xs ++ [x])
  parsedApp other _ = fail ("cannot apply to (" ++ show other ++ ") in pattern")

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

whitespace :: Parser ()
whitespace = void $ takeWhile1P Nothing isSpace
  where
    isSpace ' '  = True
    isSpace '\r' = True
    isSpace _    = False

indentedNewline :: Parser ()
indentedNewline = try $ do
  char '\n'
  minIndent <- ask
  parseSpaces minIndent minIndent

parseSpaces :: LinePosition -> LinePosition -> Parser ()
parseSpaces _        0 = return ()
parseSpaces original n = token test Set.empty >>= id
  where
    test ' '  = Just $ parseSpaces original $ n-1
    test '\n' = Just $ parseSpaces original original
    test '\r' = Just $ parseSpaces original n
    test _    = Nothing

spaceChunk :: Parser ()
spaceChunk = choice [whitespace, indentedNewline, lineCmnt, blockCmnt]

anySpaceChunk :: Parser ()
anySpaceChunk =  hidden $ skipMany $ choice [whitespace, void $ char '\n', lineCmnt, blockCmnt]

sc :: Parser ()
sc = label "whitespace" $ skipSome spaceChunk

sc' :: Parser ()
sc' = hidden $ skipMany spaceChunk

function :: Parser Expr
function = do
  try $ symbol $ (char '\\' <|> char '\x3bb')
  vars <- manyIdents
  symbol $ (string "->" <|> string "\x2192")
  expr <- parser
  case vars of
    [] -> fail "functions must have at least one parameter (\\ -> ... is not allowed)"
    xs -> return (Val (Func xs expr))
  where
    someIdents = do
      ident <- typed name
      others <- manyIdents
      return (ident : others)
    manyIdents = try someIdents <|> return []

letbinding :: Parser Expr
letbinding = do
  try $ symbol $ key "let"
  (name, val) <- anyIndent $ do
    name <- typed name
    symbol $ char '='
    val <- parser
    symbol $ key "in"
    return (name, val)
  expr <- parser
  return $ Let name val expr

matchbinding :: Parser Expr
matchbinding = do
  try $ symbol $ key "match"
  exprs <- someExprs
  cases <- some $ parseCase $ length exprs
  return $ Match exprs cases
  where
    parseCase len = do
      pats <- try somePatterns
      expr <- blockOf parser
      if length pats == len then
        return (pats, expr)
      else
        error "different number of patterns and expressions in match"
    someExprs = do
      e <- symbol $ parserNoSpace
      (e:) <$> manyExprs
    manyExprs = symbol $ (try (key "in" >> return []) <|> someExprs)
    somePatterns = do
      p <- symbol $ parserNoSpace
      (p:) <$> manyPatterns
    manyPatterns = symbol $ (try (string "->" >> return []) <|> somePatterns)

ifThenElse :: Parser Expr
ifThenElse = do
  try $ symbol $ key "if"
  (i, t) <- anyIndent $ do
    i <- parser
    symbol $ key "then"
    t <- parser
    symbol $ key "else"
    return (i, t)
  e <- blockOf parser
  return $ If i t e

panic :: Parser Expr
panic = do
  try $ symbol $ key "panic"
  msg <- takeWhileP Nothing notNewline
  return $ Panic $ dropWhile (' ' ==) msg
  where
    notNewline ch = ch /= '\n' && ch /= '\r'

number :: Parser Word64
number = symbol (try (char '0' >> char 'x' >> L.hexadecimal) <|> L.decimal) <?> "number"

paren :: Parsable a => Parser a
paren = do
  try $ symbol $ char '('
  anyIndent $ do
    expr <- parser
    symbol $ char ')'
    return expr

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
  return (first:rest)
  where
    isIdentFirst x = (isAlpha x || x == '_') && isAscii x
    isIdentRest x = (isAlpha x || isDigit x || x == '_') && isAscii x

identifier :: Parser String
identifier = label "identifier" $ symbol $ do
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

newType :: Parser Type
newType = lift $ do
  var <- get
  put $ var+1
  return (TAnon var)

key :: String -> Parser ()
key w = label w $ do
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
operatorInContext = label "operator" $ widePrefix <|> postfixCompact
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
lineCmnt = hidden $ L.skipLineComment "--"

blockCmnt :: Parser ()
blockCmnt = hidden $ L.skipBlockCommentNested "{-" "-}"

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
