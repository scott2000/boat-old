{-# LANGUAGE FlexibleInstances, NamedFieldPuns, RecordWildCards #-}

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
import qualified Data.Map as Map

-- The minimum possible indentation, whether to parse newlines, and whether extra indentation is allowed
type LinePosition = (Int, Bool, Bool)

-- The number of anonymous types assigned
type AnonCount = Word64

type MParser = Parsec Void String
type Parser = ReaderT LinePosition (StateT AnonCount MParser)

runCustomParser :: AnonCount -> Parser a -> MParser (a, AnonCount)
runCustomParser c p = runStateT (runReaderT (followedByEnd p) (0, True, False)) c

followedByEnd :: Parser a -> Parser a
followedByEnd p = do
  res <- p
  sc' >> eof
  return res

blockOf :: Parser a -> Parser a
blockOf = blockAllowingOf True

strictBlockOf :: Parser a -> Parser a
strictBlockOf = blockAllowingOf False

blockAllowingOf :: Bool -> Parser a -> Parser a
blockAllowingOf allow p = do
  newLine <- anySpaceChunk
  (current, _, _) <- ask
  if newLine then do
    level <- (subtract 1 . unPos) <$> L.indentLevel
    if level < current then
      fail ("block indented less then containing block (" ++ show level ++ " < " ++ show current ++ ")")
    else
      withLinePos (level, True, allow) p
  else
    withLinePos (current, False, allow) p

anyIndent :: Parser a -> Parser a
anyIndent = withLinePos (0, True, True)

withLinePos :: LinePosition -> Parser a -> Parser a
withLinePos pos p = lift $ runReaderT p pos

class Parsable a where
  parsePartial :: Parser a
  parsedOp :: String -> a -> a -> Parser a
  parsedApp :: a -> a -> Parser a

keywords :: [String]
keywords =
  [ "use",
    "mod",
    "data",
    "val",
    "let",
    "match",
    "in",
    "rec",
    "unit",
    "true",
    "false",
    "if",
    "then",
    "else",
    "panic",
    "_" ]

moduleParser :: Name -> ModuleTree -> Parser ModuleTree
moduleParser path current =
  (try sc' >> (use <|> module' <|> data' <|> value <|> (eof >> return current))) <|> return current
  where
    use = do
      paths <- useDeclParser
      moduleParser path $ addUseDecls paths current
    module' = modDeclParser path current
    p parser add = do
      (name, val) <- parser
      case add name val current of
        Right new -> moduleParser path new
        Left err -> fail err
    data' = p dataDeclParser $ addDataDecl path
    value = p valDeclParser addValDecl

modDeclParser :: Name -> ModuleTree -> Parser ModuleTree
modDeclParser path ModuleTree {..} = label "mod declaration" $ do
  try $ key "mod"
  name <- anyIndent $ identifier
  let sub = Map.findWithDefault emptyModule name treeModules
  sub'<- strictBlockOf $ moduleParser (path...name) sub
  moduleParser path ModuleTree { treeModules = Map.insert name sub' treeModules, .. }

useDeclParser :: Parser [UsePath]
useDeclParser = label "use declaration" $ do
  try $ key "use"
  anyIndent $ symbol usePaths

usePaths :: Parser [UsePath]
usePaths = manyPaths <|> singlePath
  where
    singlePath = (:[]) <$> usePath
    manyPaths = do
      firstPath <- char '(' >> symbol usePath
      restPaths <- some $ try (sc' >> char ',' >> symbol usePath)
      sc' >> ((char ',' >> sc') <|> return ()) >> char ')'
      return (firstPath : restPaths)

usePath :: Parser UsePath
usePath = useAll <|> useOne
  where
    useAll = char '_' >> return UseAll
    useOne = do
      name <- identifier
      UseModule name <$> (char '.' >> usePaths) <|> return (UseMember name)

valDeclParser :: Parser (String, Typed Expr)
valDeclParser = label "val declaration" $ do
  try $ key "val"
  (name, ty) <- anyIndent $ do
    name <- identifier
    ty <- parseAscription
    symbol $ char '='
    return (name, ty)
  expr <- blockOf parser
  (,) name <$> ascribe expr ty

dataDeclParser :: Parser (String, DataDecl)
dataDeclParser = label "data declaration" $ do
  try $ key "data"
  (name, tp) <- anyIndent $ do
    (name, typeParams) <- variant
    tp <- sequence $ map into typeParams
    symbol $ char '='
    return (name, tp)
  variants <- blockOf (multiline <|> singleline)
  return (name, DataDecl { typeParams = tp, variants })
  where
    into (TVar s) = return s
    into other = fail ("data declaration expected type variables, found other type: " ++ show other)
    multiline = do
      try $ symbol $ char '|'
      singleline
    manyVariants = many $ do
      try $ symbol $ char '|'
      variant
    singleline = (:) <$> variant <*> manyVariants

variant :: Parser (String, [Type])
variant = symbol $ do
  name <- identifier
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
    <|> typed recbranch
    <|> try (typed (Id <$> name))
    <|> try (symbol $ key "unit" >> return (Val Unit ::: TUnit))
    <|> try (symbol $ key "true" >> return (Val (Bool True) ::: TBool))
    <|> try (symbol $ key "false" >> return (Val (Bool False) ::: TBool))
    <|> (::: TNat) <$> Val <$> Nat <$> number
    -- TODO fix bug: (3 : Nat) => cannot ascribe type Nat to expression of type Internal.Nat

  parsedOp "->" _ _ = fail ("cannot use (->) operator in expression")
  parsedOp op a b = typed $ return $ Op op a b

  parsedApp a b = typed $ return $ App a b

instance Parsable Type where
  parsePartial = label "type" $ paren
    <|> try (tIdVar <$> name)
    <|> try (symbol $ key "_" >> newType)

  parsedOp "->" a b = return $ TFunc a b
  parsedOp op _ _ = fail ("cannot use (" ++ op ++ ") operator in type")

  parsedApp a b = return $ TApp a b

instance Parsable (Typed Pattern) where
  parsePartial = label "pattern" $ maybeRetype $ paren
    <|> try (typed (pIdVar <$> name))
    <|> try (symbol $ key "_" >> typed (return $ PAny Nothing))
    <|> try (symbol $ key "unit" >> return (PAny Nothing ::: TUnit))
    <|> try (symbol $ key "true" >> return (PBool True ::: TBool))
    <|> try (symbol $ key "false" >> return (PBool False ::: TBool))
    <|> (::: TNat) <$> PNat <$> try number

  parsedOp op _ _ = fail ("cannot use (" ++ op ++ ") operator in pattern")

  parsedApp (PCons name xs ::: _) x = typed $ return $ PCons name (xs ++ [x])
  parsedApp other _ = fail ("cannot apply to (" ++ show other ++ ") in pattern")

parserPrec :: Parsable a => (Prec, Assoc) -> Parser a
parserPrec = parserBase parsePartial
  where
  parserBase base prec = do
    expr <- base
    res <- try (opExpr expr) <|> try (appExpr expr) <|> return (Right expr)
    case res of
      Left err -> fail err
      Right expr -> return expr
    where
      opExpr expr = do
        (op, kind) <- try operatorInContext
        if isInfix kind then
          let newPrec = adjustPrec kind $ precedence op in
          tryPrec prec newPrec $ do
            other <- parserPrec newPrec
            parserBase (parsedOp op expr other) prec
        else
          return $ Left ("cannot use operator (" ++ op ++ ") of kind " ++ show kind ++ " here")
      appExpr expr =
        tryPrec prec appPrec $ do
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
indentedNewline = do
  (minIndent, newline, allow) <- ask
  if newline then do
    try $ char '\n'
    parseSpaces allow minIndent
  else
    fail "newline not allowed here"

parseSpaces :: Bool -> Int -> Parser ()
parseSpaces allow minIndent = go 0
  where
    go :: Int -> Parser ()
    go n = ((lineCmnt <|> blockCmnt) >> go 0) <|> (token cont Set.empty >>= id) <|> stop
      where
        cont ' '  = Just $ go (n+1)
        cont '\n' = Just $ go 0
        cont '\r' = Just $ go n
        cont _    = Nothing
        stop
          | n == minIndent || (allow && n > minIndent) = return ()
          | otherwise =
            fail ("expected indent of " ++ show minIndent ++ ", found " ++ show n)

spaceChunk :: Parser ()
spaceChunk = choice [whitespace, indentedNewline, lineCmnt, blockCmnt]

anySpaceChunk :: Parser Bool
anySpaceChunk = fmap (foldr (||) False) $ hidden $ many $ choice
  [ whitespace >> return False,
    char '\n' >> return True,
    lineCmnt  >> return False,
    blockCmnt  >> return False ]

lookAheadSpace :: Parser ()
lookAheadSpace = choice [whitespace, void $ char '\n', lineCmnt, blockCmnt]

sc :: Parser ()
sc = label "whitespace" $ skipSome spaceChunk

sc' :: Parser ()
sc' = hidden $ skipMany spaceChunk

function :: Parser Expr
function = do
  try $ symbol $ (char '\\' <|> char '\x3bb')
  cases <- strictBlockOf $ some $ matchCase
  let
    ((p0, _ ::: t0) : tailed) = cases
    len = length p0
    types = map typeof p0
    mapTy xs = zipWith (:::) xs types
    idents = for [0..len-1] $ \n -> Name ["{-" ++ show n ++ "-}"]
  sequence_ $ for tailed $ \(pats, _) ->
    if length pats /= len then
      fail "different number of patterns in function cases"
    else
      return ()
  return $ Val $ Func (mapTy idents) $ Match (mapTy $ map Id idents) cases ::: t0

letbinding :: Parser Expr
letbinding = do
  try $ symbol $ key "let"
  (name, val) <- anyIndent $ do
    name <- typed name
    symbol $ char '='
    val <- parser
    symbol $ key "in"
    return (name, val)
  expr <- blockOf parser
  return $ Let name val expr

matchbinding :: Parser Expr
matchbinding = do
  try $ symbol $ key "match"
  exprs <- anyIndent someExprs
  cases <- strictBlockOf $ some $ parseCase $ length exprs
  return $ Match exprs cases
  where
    parseCase len = do
      (pats, expr) <- matchCase
      if length pats == len then
        return (pats, expr)
      else
        fail "different number of patterns and expressions in match"
    someExprs = do
      e <- symbol $ parserNoSpace
      (e:) <$> manyExprs
    manyExprs = symbol $ (try (key "in" >> return []) <|> someExprs)

matchCase :: Parser MatchCase
matchCase = do
  (,) <$> try somePatterns <*> blockOf parser
  where
    somePatterns = do
      p <- symbol $ parserNoSpace
      (p:) <$> manyPatterns
    manyPatterns = symbol $ ((string "->" >> return []) <|> somePatterns)

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

recbranch :: Parser Expr
recbranch = do
  try $ symbol $ key "rec"
  Rec <$> many (try parserNoSpace)

number :: Parser Word64
number = symbol ((try (char '0' >> char 'x') >> L.hexadecimal) <|> L.decimal) <?> "number"

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
    fail "expected identifier"
  else
    return ident

name :: Parser Name
name = Name <$> ((:) <$> identifier <*> (many (try (char '.') >> identifier)))

typed :: Parser a -> Parser (Typed a)
typed p = (:::) <$> p <*> newType

maybeRetype :: Parser (Typed a) -> Parser (Typed a)
maybeRetype p = do
  v <- p
  a <- parseAscription
  ascribe v a

parseAscription :: Parser (Maybe Type)
parseAscription = (<|> return Nothing) $ do
  try $ symbol $ char ':'
  Just <$> parser

ascribe :: Typed a -> (Maybe Type) -> Parser (Typed a)
ascribe (x ::: old) (Just new) =
  case earlyUnify old new of
    Just ty -> return (x ::: ty)
    Nothing -> fail ("cannot ascribe type " ++ show new ++ " to expression of type " ++ show old)
ascribe expr Nothing = return expr

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
    fail ("expected keyword `" ++ w ++ "`")
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
      lookAhead lookAheadSpace
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

tryPrec :: (Prec, Assoc) -> (Prec, Assoc) -> Parser a -> Parser (Either String a)
tryPrec (p0, a0) (p1, a1) m
  | p0 == p1 =
    if a0 /= a1 then
      return $ Left ("cannot mix associativities of operators in same precedence level (" ++ show p0 ++ ")")
    else if a0 == ALeft then
      empty
    else if a0 == ANon then
      return $ Left "non-associative operator chaining not allowed"
    else
      Right <$> m
  | p0 > p1 = empty
  | otherwise = Right <$> m


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
