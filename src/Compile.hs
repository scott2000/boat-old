{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}

module Compile (testCompile) where

import AST

import qualified LLVM.AST as LLVM
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Linkage as L
import qualified LLVM.AST.Visibility as V
import LLVM.AST (Operand)
import LLVM.AST.IntegerPredicate as ICMP
import LLVM.AST.AddrSpace
import LLVM.AST.Type (void, i1, i8, i16, i32, i64, double, ptr)
import LLVM.IRBuilder.Constant
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Instruction as INST
import LLVM.IRBuilder.Monad

import LLVM.Pretty

import Data.Word
import Data.Maybe
import Data.String
import Control.Monad.State hiding (void)
import Data.Text.Lazy (unpack)
import qualified Data.Map as Map
import qualified Data.Set as Set

data Codegen = Codegen
  { anonymousFunctions :: [ClosureData],
    values :: Env Value,
    getWordSize :: Word32,
    getMalloc :: Maybe Operand }

data ClosureData = ClosureData
  { getClosureIndex :: !Int,
    getFreeVars :: [Typed Name],
    getParameters :: [Typed Name],
    getInnerExpr :: Typed Expr,
    getInfo :: Operand,
    getFunc :: Operand }
  deriving Show

type BuilderState = StateT Codegen ModuleBuilder
type Builder = IRBuilderT BuilderState

newCodegen :: Word32 -> Codegen
newCodegen wordSize = Codegen
  { anonymousFunctions = [],
    values = [],
    getWordSize = wordSize,
    getMalloc = Nothing }

allValues :: BuilderState [Name]
allValues = (map fst) <$> (gets values)

testCompile :: Env (Typed Expr) -> Word32 -> IO ()
testCompile env wordSize =
  putStrLn
  $ unpack
  $ ppllvm
  $ buildModule "test"
  $ flip evalStateT (newCodegen wordSize)
  $ genAllVals env
  -- $ (genAllVals env >>
  -- getStaticClosureData
  --   [Name "y" ::: tNat]
  --   (Op "+" (Id (Name "x") ::: tNat) (Id (Name "y") ::: tNat) ::: tNat))

genAllVals :: Env (Typed Expr) -> BuilderState (Env Operand)
genAllVals env = do
  wordSize <- gets getWordSize
  malloc <- extern "malloc" [LLVM.IntegerType wordSize] (ptr i8)
  modify $ \s -> s { getMalloc = Just malloc }
  sequence $ map genValFunc env

genValFunc :: (Name, Typed Expr) -> BuilderState (Name, Operand)
genValFunc (name, expr) =
  let
    name' = fromString $ show name
    ty = genTy $ typeof expr
    generator _ = do
      block `named` "entry"
      genExpr [] expr `named` "ret" >>= ret
  in do
    f <- function name' [] ty generator
    return (name, f)

genExpr :: [(Name, Operand)] -> Typed Expr -> Builder Operand
genExpr env (expr ::: ty) =
  case expr of
    Lit l -> genLit l
    Id name ->
      case lookup name env of
        Just x -> return x
        Nothing -> fail ("cannot find name `" ++ show name ++ "`")
    Op op a b -> do
      a <- genExpr env a `named` "lhs"
      b <- genExpr env b `named` "rhs"
      genOp op a b
    If i t e -> do
      i <- genExpr env i `named` "if.cond"
      genIf i (genExpr env t) (genExpr env e)
    Let (name ::: _) val expr -> do
      val <- genExpr env val `named` (fromString $ show name)
      genExpr ((name, val):env) expr
    Func xs expr ->
      lift (getStaticClosureData xs expr) >>= genClosureForData env
    other -> error ("not yet implemented: code gen for " ++ show other)

genTy :: Type -> LLVM.Type
genTy (TId "Nat") = i64
genTy (TId "Bool") = i1
genTy (TFunc _ _) = funcTy

funcTy :: LLVM.Type
funcTy = LLVM.StructureType False [ptr infoTy, i32, ptr i8]

infoTy :: LLVM.Type
infoTy = LLVM.StructureType False [ptr voidFuncTy, ptr destructorTy]

voidFuncTy :: LLVM.Type
voidFuncTy = LLVM.FunctionType void [] False

destructorTy :: LLVM.Type
destructorTy = LLVM.FunctionType void [ptr i8] False

genLit :: Literal -> Builder Operand
genLit (Nat n) = int64 (toInteger n)
genLit (Bool False) = bit 0
genLit (Bool True) = bit 1

genIf :: Operand -> Builder Operand -> Builder Operand -> Builder Operand
genIf i t e = mdo
  condBr i thenBlock elseBlock
  thenBlock <- block `named` "if.then"
  thenRes <- t `named` "if.then.res"
  br endBlock
  elseBlock <- block `named` "if.else"
  elseRes <- e `named` "if.else.res"
  br endBlock
  endBlock <- block `named` "if.end"
  phi [(thenRes, thenBlock), (elseRes, elseBlock)]

genOp :: String -> Operand -> Operand -> Builder Operand
genOp "+" = add
genOp "-" = sub
genOp "*" = mul
genOp "/" = udiv
genOp "<" = icmp ICMP.ULT
genOp ">" = icmp ICMP.UGT
genOp "<=" = icmp ICMP.ULE
genOp ">=" = icmp ICMP.UGE
genOp "==" = icmp ICMP.EQ
genOp "!=" = icmp ICMP.NE
genOp "||" = INST.or
genOp "&&" = INST.and

getFreeNames :: [Name] -> Typed Expr -> BuilderState [Typed Name]
getFreeNames env expr = do
  globalValues <- allValues
  return $ execState (deps (env ++ globalValues) expr) []
  where
    deps :: [Name] -> Typed Expr -> State [Typed Name] ()
    deps env (expr ::: ty) =
      case expr of
        Id name ->
          if name `elem` env then
            return ()
          else
            modify ((name ::: ty):)
        Op _ a b -> deps env a >> deps env b
        App a b -> deps env a >> deps env b
        If i t e -> deps env i >> deps env t >> deps env e
        Let name val expr -> deps env val >> deps (valof name : env) expr
        Func params expr -> deps (map valof params ++ env) expr
        _ -> return ()

getStaticClosureData :: [Typed Name] -> Typed Expr -> BuilderState ClosureData
getStaticClosureData params expr = do
  free <- getFreeNames (map valof params) expr
  anons <- gets anonymousFunctions
  let
    findMatch [] = Nothing
    findMatch (c:cs)
      | getFreeVars c == free,
        getParameters c == params,
        getInnerExpr c == expr    = Just c
      | otherwise                 = findMatch cs
  case findMatch anons of
    Just c -> return c
    Nothing -> buildStaticClosure free params expr

buildStaticClosure :: [Typed Name] -> [Typed Name] -> Typed Expr -> BuilderState ClosureData
buildStaticClosure free params expr = mdo
  anons <- gets anonymousFunctions
  modify (\codegen -> codegen { anonymousFunctions = result : anons })
  let
    len = length anons
    infoName = fromString ("info." ++ show len)
    defType = LLVM.FunctionType returnType (map (genTy . typeof) combinedArgs) False
    def = LLVM.GlobalVariable
      infoName
      L.External
      V.Default
      Nothing
      Nothing
      Nothing
      True
      infoTy
      (AddrSpace 0)
      (Just (C.Struct Nothing False
        [ C.BitCast (C.GlobalReference (ptr defType) closureName) (ptr voidFuncTy),
          C.Null (ptr destructorTy) ]))
      Nothing
      Nothing
      0
      []
    paramType (Name name ::: ty) = (genTy ty, fromString name)
    closureName = fromString ("func." ++ show len)
    returnType = genTy $ typeof expr
  emitDefn (LLVM.GlobalDefinition def)
  func <- function closureName (map paramType combinedArgs) returnType body
  let
    result = ClosureData
      { getClosureIndex = len,
        getFreeVars = free,
        getParameters = params,
        getInnerExpr = expr,
        getInfo = LLVM.ConstantOperand (C.GlobalReference (ptr infoTy) infoName),
        getFunc = func }
  return result
  where
    combinedArgs = free ++ params
    body args = do
      block `named` "entry"
      expr <- genExpr env expr `named` "ret"
      ret expr
      where
        env = zipWith (\p a -> (valof p, a)) combinedArgs args

genClosureForData :: [(Name, Operand)] -> ClosureData -> Builder Operand
genClosureForData env closureData = do
  let
    params = getParameters closureData
    frees = getFreeVars closureData
    storedType = map (genTy . typeof) frees
  dataPtr <- if null frees then
      return $ LLVM.ConstantOperand $ C.Null $ ptr i8
    else do
      dataPtr <- malloc $ LLVM.StructureType False storedType
      let
        freeMap (name ::: _) n =
          case lookup name env of
            Nothing -> error ("missing capture for closure: `" ++ show name ++ "`")
            Just res -> do
              addr <- gep dataPtr
                [ LLVM.ConstantOperand $ C.Int 32 0,
                  LLVM.ConstantOperand $ C.Int 32 n ] `named` "capture"
              store addr 0 res
      sequence $ zipWith freeMap frees [0..]
      bitcast dataPtr (ptr i8) `named` "data.ptr"
  genStruct [getInfo closureData, LLVM.ConstantOperand $ C.Int 32 $ toInteger $ length params - 1, dataPtr]

genStruct :: [Operand] -> Builder Operand
genStruct operands = iter 0 operands $ LLVM.ConstantOperand $ C.Struct Nothing False $ map base operands
  where
    base (LLVM.ConstantOperand c) = c
    base (LLVM.LocalReference t _) = C.Undef t
    base (LLVM.MetadataOperand _) = error "metadata not allowed in struct"

    iter _ [] o = return o
    iter n (LLVM.ConstantOperand _ : xs) o = iter (n+1) xs o
    iter n (x:xs) o = insertValue o x [n] >>= iter (n+1) xs

malloc :: LLVM.Type -> Builder Operand
malloc ty = do
  Just malloc <- lift $ gets getMalloc
  wordSize <- gets getWordSize
  let gep = C.GetElementPtr False (C.Null $ ptr ty) [C.Int 32 1]
  res <- call malloc [(LLVM.ConstantOperand $ C.PtrToInt gep (LLVM.IntegerType wordSize), [])] `named` "malloc.call"
  bitcast res (ptr ty) `named` "malloc.ptr"
