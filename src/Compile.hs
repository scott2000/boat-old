{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Compile (compile) where

import AST
import Run (getInstanceOfValue)

import qualified LLVM.AST as LLVM
import qualified LLVM.AST.Typed as LLVM
import qualified LLVM.AST.FunctionAttribute as FnAttr
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.CallingConvention as CC
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

import LLVM.Internal.Target (withHostTargetMachine, getTargetMachineDataLayout)
import LLVM.Internal.Context (withContext)
import LLVM.Module (File (..), moduleAST, withModuleFromAST, writeObjectToFile)
import LLVM.PassManager (PassSetSpec (..), defaultCuratedPassSetSpec, withPassManager, runPassManager)

import LLVM.Pretty

import System.Exit (exitFailure)
import Data.Word
import Data.Maybe
import Data.List
import Data.String
import Control.Monad.State hiding (void)
import Data.Text.Lazy (unpack)
import qualified Data.Map as Map
import qualified Data.Set as Set

{-

Current Goals:

- add `rec` keyword for tail recursion
- use fastcc calling convention
- add generalized tuples and tuple extensions
- algebraic data types

Possible Future Optimizations:

- add No Signed Wrap (NSW) flag for reference count increments
- statically optimized currying
    (not using application)
- replacement of recursion for top-level values with `rec` keyword where applicable
    (possibly emit warning?)
- tuple expansion into arguments, substitute `void` for `unit`

-}

debugMode :: Bool
debugMode = False

type DestructorEntry = ([Type], [Type]) -- args, frees
type FunctionEntry = (LLVM.Type, Maybe LLVM.Type) -- arg, (Just = NF ret, Nothing = function)

data Codegen = Codegen
  { anonymousFunctions :: [ClosureData],
    values :: Env (Typed Value),
    getWordSize :: !Word32,
    getDestructors :: Map.Map DestructorEntry C.Constant,
    getCallers :: Map.Map FunctionEntry Operand,
    getFnInc :: Maybe Operand,
    getFnDec :: Maybe Operand,
    getMalloc :: Maybe Operand,
    getFree :: Maybe Operand,
    getPuts :: Maybe Operand,
    getPrintf :: Maybe Operand,
    getDebugTrap :: Maybe Operand,
    getStringCount :: !Int,
    getFunctionName :: String }

data ClosureData = ClosureData
  { getClosureIndex :: !Int,
    getFreeVars :: [Typed Name],
    getParameters :: [Typed Name],
    getInnerExpr :: Typed Expr,
    getFunc :: Operand,
    getFwd :: Operand }
  deriving Show

type BuilderState = StateT Codegen ModuleBuilder
type Builder = IRBuilderT BuilderState

newCodegen :: Env (Typed Value) -> Word32 -> Codegen
newCodegen values wordSize = Codegen
  { anonymousFunctions = [],
    values = values,
    getWordSize = wordSize,
    getDestructors = Map.empty,
    getCallers = Map.empty,
    getFnInc = Nothing,
    getFnDec = Nothing,
    getMalloc = Nothing,
    getFree = Nothing,
    getPuts = Nothing,
    getPrintf = Nothing,
    getDebugTrap = Nothing,
    getStringCount = 0,
    getFunctionName = "main" }

localHidden :: L.Linkage
localHidden = if debugMode then L.External else L.Private

allValues :: BuilderState [Name]
allValues = (map fst) <$> (gets values)

inVal :: Builder a -> String -> Builder a
inVal builder name' = inLet builder (const name')

inLet :: Builder a -> (String -> String) -> Builder a
inLet builder namef = do
  s <- lift get
  let name = getFunctionName s
  put (s { getFunctionName = namef name })
  r <- builder
  modify $ \s -> s { getFunctionName = name }
  return r

compile :: String -> Env (Typed Value) -> Word32 -> IO ()
compile path env wordSize =
  case lookup (Name "main") env of
    Nothing -> putStrLn "no `main` value found"
    Just main
      | notConcrete (typeof main) ->
        putStrLn ("`main` value has generic type: " ++ show (typeof main)) >> exitFailure
      | otherwise -> do
        let
          m = buildModule "test"
            $ evalStateT (genMain main)
            $ newCodegen env wordSize
          ofile = File (replaceExtension "o" path)
        withContext $ \c ->
          withModuleFromAST c m $ \cm ->
            withHostTargetMachine $ \tm -> do
              layout <- getTargetMachineDataLayout tm
              let
                spec = defaultCuratedPassSetSpec
                  { optLevel = Just (if debugMode then 0 else 1),
                    dataLayout = Just layout,
                    targetMachine = Just tm }
              withPassManager spec $ \pm -> runPassManager pm cm
              mm <- moduleAST cm
              let lloutput = unpack $ ppllvm mm
              putStrLn lloutput
              writeObjectToFile tm ofile cm
              writeFile (replaceExtension "ll" path) lloutput
  where
    notConcrete (TId _) = False
    notConcrete (TFunc a b) = notConcrete a || notConcrete b
    notConcrete _ = True
    replaceExtension ext = reverse . r . reverse
      where
        r []       = []
        r ('.':xs) = reverse ext ++ "." ++ xs
        r (x  :xs) = r xs

genMain :: Typed Value -> BuilderState Operand
genMain main = do
  wordSize <- gets getWordSize
  llvmFn $ newFn
    { fnName = "main",
      fnRetTy = i32,
      fnParams = [],
      fnBody = Just generator }
  where
    generator _ = do
      block `named` "entry"
      res <- genVal mainArgs [] main `named` "main.res"
      printf (" => " ++ tyFmt retType) [res]
      rcDec (-1) res retType
      ret (lcint 32 0)
    (retType, mainArgs) =
      case typeof main of
        TFunc (TId "Unit") r -> (r, [unit])
        r -> (r, [])

genExpr :: [Operand] -> Env (Typed Operand) -> Typed Expr -> Builder Operand
genExpr app env (expr ::: ty) =
  case expr of
    Val v ->
      genVal app env (v ::: ty)
    App a b -> do
      arg <- genExpr [] env b `named` "app.arg"
      genExpr (arg:app) env a
    Id name -> do
      values <- lift $ gets values
      case lookup name values of
        Just val -> do
          genVal app [] (getInstanceOfValue ty val) `inVal` (show name)
        Nothing ->
          case lookup name env of
            Just (x ::: _) -> genApp ty app x
            Nothing -> fail ("cannot find name `" ++ show name ++ "`")
    Op op a b -> do
      let aTy = typeof a
      let bTy = typeof b
      a <- genExpr [] env a `named` "lhs"
      b <- genExpr [] env b `named` "rhs"
      rcDec (-1) a aTy
      rcDec (-1) b bTy
      r <- genOp op a b
      genApp ty app r
    If (Val (Bool b) ::: _) t e ->
      if b then
        genExpr app env t
      else
        genExpr app env e
    If i t e -> do
      let thenScope = countLocals t localEnv
      let elseScope = countLocals e localEnv
      let diffScope = zipEnv (-) thenScope elseScope
      i <- genExpr [] env i `named` "if.cond"
      genIf i (genExpr app env t) (genExpr app env e) (map fromEnv diffScope)
    Let (name ::: ty) val expr -> do
      let ((_, inc):_) = countLocals expr ((name, 0) : localEnv)
      if inc == 0 then
        genExpr app env expr
      else do
        val <- genExpr [] env val `named` (fromString $ show name) `inLet` (++ "." ++ show name)
        let realInc = inc - 1
        if realInc /= 0 then
          rcInc realInc val ty
        else
          return ()
        genExpr app ((name, val ::: ty):env) expr
  where
    localEnv = toLocalEnv env
    fromEnv (name, count) = (fromJust $ lookup name env, count)

toLocalEnv :: Env (Typed Operand) -> Env Int
toLocalEnv = map (\(x, _) -> (x, 0))

genStaticCall :: [Operand] -> ClosureData -> Builder Operand
genStaticCall args closureData =
  call (getFunc closureData) (map (\x -> (x, [])) args)

genApp :: Type -> [Operand] -> Operand -> Builder Operand
genApp _  [] val = return val
genApp (TFunc _ (TFunc _ _)) [arg] closure =
  genCallClosure closure arg
genApp (TFunc _ ty) [arg] closure =
  genCallClosureNF (genTy ty) closure arg
genApp (TFunc _ ty) (arg:rest) closure =
  genCallClosure closure arg `named` "partial" >>= genApp ty rest

genTy :: Type -> LLVM.Type
genTy (TId "Unit") = unitTy
genTy (TId "Nat") = i64
genTy (TId "Bool") = i1
genTy (TFunc _ _) = funcTy

isRc :: Type -> Bool
isRc (TId "Unit") = False
isRc (TId "Nat") = False
isRc (TId "Bool") = False
isRc (TFunc _ _) = True

unitTy :: LLVM.Type
unitTy = LLVM.StructureType False []

funcTy :: LLVM.Type
funcTy = LLVM.StructureType False [ptr voidFuncTy, i32, ptr i8]

voidFuncTy :: LLVM.Type
voidFuncTy = LLVM.FunctionType void [] False

destructorTy :: LLVM.Type
destructorTy = LLVM.FunctionType void [ptr i8] False

rcInc :: Int -> Operand -> Type -> Builder ()
rcInc i o (TFunc _ _) = fnInc i o
rcInc i o ty = return ()

rcDec :: Int -> Operand -> Type -> Builder ()
rcDec i o (TFunc _ _) = fnDec i o
rcDec i o ty = return ()

fnInc :: Int -> Operand -> Builder ()
fnInc i closure = do
  s <- lift get
  let wordSize = getWordSize s
  incrementer <- case getFnInc s of
    Nothing -> do
      incrementer <-
        lift $ llvmFn $ newFn
          { fnLinkage = localHidden,
            fnName = "fn.inc",
            fnRetTy = void,
            fnParams = [(funcTy, ParameterName "closure"), (LLVM.IntegerType wordSize, ParameterName "inc")],
            fnBody = Just body }
      lift $ modify $ \s -> s { getFnInc = Just incrementer }
      return incrementer
    Just incrementer -> return incrementer
  call incrementer [(closure, []), (lcint wordSize $ toInteger i, [])]
  return ()
  where
    body :: [Operand] -> Builder ()
    body [closure, inc] = mdo
      block `named` "entry"
      dataPtr <- extractValue closure [2] `named` "data.ptr"
      isnull <- icmp ICMP.EQ dataPtr (LLVM.ConstantOperand $ C.Null (ptr i8)) `named` "isnull"
      condBr isnull done nonnull

      nonnull <- block `named` "nonnull"
      wordSize <- lift $ gets getWordSize
      rcPtr <- bitcast dataPtr (ptr $ LLVM.IntegerType wordSize) `named` "rc.ptr"
      rc <- load rcPtr 0 `named` "rc"
      newRc <- add rc inc `named` "rc.new"
      store rcPtr 0 newRc
      retVoid

      done <- block `named` "done"
      retVoid

fnDec :: Int -> Operand -> Builder ()
fnDec i closure = do
  s <- lift get
  let wordSize = getWordSize s
  decrementer <- case getFnDec s of
    Nothing -> do
      decrementer <-
        lift $ llvmFn $ newFn
          { fnLinkage = localHidden,
            fnName = "fn.dec",
            fnRetTy = void,
            fnParams = [(funcTy, ParameterName "closure"), (LLVM.IntegerType wordSize, ParameterName "inc")],
            fnBody = Just body }
      lift $ modify $ \s -> s { getFnDec = Just decrementer }
      return decrementer
    Just decrementer -> return decrementer
  call decrementer [(closure, []), (lcint wordSize $ toInteger i, [])]
  return ()
  where
    body :: [Operand] -> Builder ()
    body [closure, inc] = mdo
      block `named` "entry"
      dataPtr <- extractValue closure [2] `named` "data.ptr"
      isnull <- icmp ICMP.EQ dataPtr (LLVM.ConstantOperand $ C.Null (ptr i8)) `named` "isnull"
      condBr isnull done nonnull

      nonnull <- block `named` "nonnull"
      wordSize <- lift $ gets getWordSize
      rcPtr <- bitcast dataPtr (ptr $ LLVM.IntegerType wordSize) `named` "rc.ptr"
      rc <- load rcPtr 0 `named` "rc"
      newRc <- add rc inc `named` "rc.new"
      zero <- icmp ICMP.EQ newRc (lcint 32 0) `named` "rc.zero"
      condBr zero destroy keep

      destroy <- block `named` "destroy"
      funcPtr <- extractValue closure [0] `named` "func.ptr"
      arity <- extractValue closure [1] `named` "arity"
      destructorList <- bitcast funcPtr (ptr $ ptr destructorTy) `named` "destructors"
      destructorPtr <- gep destructorList [arity] `named` "destructor.ptr"
      destructor <- load destructorPtr 0 `named` "destructor"
      call destructor [(dataPtr, [])]
      retVoid

      keep <- block `named` "keep"
      store rcPtr 0 newRc
      retVoid

      done <- block `named` "done"
      retVoid


genVal :: [Operand] -> Env (Typed Operand) -> Typed Value -> Builder Operand
genVal [] _ (Unit ::: _) = return unit
genVal [] _ (Nat n ::: _) = int64 (toInteger n)
genVal [] _ (Bool False ::: _) = bit 0
genVal [] _ (Bool True ::: _) = bit 1
genVal app env (Func xs expr ::: ty) = do
  closureData <- lift (getStaticClosureData xs expr)
  if length (getParameters closureData) == length app then
    genStaticCall app closureData
  else do
    genClosureForData env closureData >>= genApp ty app

unit :: Operand
unit = LLVM.ConstantOperand (C.Struct Nothing False [])

genIf :: Operand -> Builder Operand -> Builder Operand -> [(Typed Operand, Int)] -> Builder Operand
genIf i t e diffs = mdo
  condBr i thenBlock elseBlock
  thenBlock <- block `named` "if.then"
  sequence_ $ map thenDec diffs
  thenRes <- t `named` "if.then.res"
  thenEndBlock <- currentBlock
  br endBlock
  elseBlock <- block `named` "if.else"
  sequence_ $ map elseDec diffs
  elseRes <- e `named` "if.else.res"
  elseEndBlock <- currentBlock
  br endBlock
  endBlock <- block `named` "if.end"
  phi [(thenRes, thenEndBlock), (elseRes, elseEndBlock)]
  where
    thenDec (o ::: ty, n)
      | n < 0     = rcDec n o ty
      | otherwise = return ()
    elseDec (o ::: ty, n)
      | n > 0     = rcDec (-n) o ty
      | otherwise = return ()

genOp :: String -> Operand -> Operand -> Builder Operand
genOp "+" = add
genOp "-" = sub
genOp "*" = mul
genOp "/" = udiv
genOp "%" = urem
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
        Val (Func params expr) -> deps (map valof params ++ env) expr
        Id name -> do
          s <- get
          let entry = (name ::: ty)
          if name `elem` env || entry `elem` s then
            return ()
          else
            put (entry:s)
        Op _ a b -> deps env a >> deps env b
        App a b -> deps env a >> deps env b
        If i t e -> deps env i >> deps env t >> deps env e
        Let name val expr -> deps env val >> deps (valof name : env) expr
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
  destructors <- buildDestructorList (tail $ reverse $ map typeof params) (map typeof free)
  codegen <- get
  let
    combinedArgs = free ++ params
    freeNames = map valof free
    isFree name = name `elem` freeNames
    body args = do
      block `named` "entry"
      let localScope = countLocals expr localEnv
      sequence_ $ map localInc localScope
      expr <- genExpr [] env expr `named` "ret"
      ret expr
      where
        env = zipWith (\p a -> (valof p, a ::: typeof p)) combinedArgs args
        localEnv = toLocalEnv env
        localInc (name, inc)
          | isFree name = rcInc inc o ty
          | inc == 0    = rcDec (-1) o ty
          | inc == 1    = return ()
          | otherwise   = rcInc (inc-1) o ty
          where
            (o ::: ty) = fromJust $ lookup name env
    anons = anonymousFunctions codegen
    currentValue = getFunctionName codegen
    len = length anons
    paramType (Name name ::: ty) = (genTy ty, fromString name)
    returnType = genTy $ typeof expr
  put (codegen { anonymousFunctions = result : anons })
  func <-
    llvmFn $ newFn
      { fnLinkage = localHidden,
        fnName = "func." ++ currentValue ++ "." ++ show len ++ ".",
        fnRetTy = returnType,
        fnParams = map paramType combinedArgs,
        fnBody = Just body }
  wordSize <- gets getWordSize
  let
    isize = LLVM.IntegerType wordSize
    fwdBody [dataPtr, lastParam] = do
      block `named` "entry"
      (args, freePtr) <- iter dataPtr [lastParam] $ tail $ reverse params
      loadedFrees <- if null free then
        return []
      else do
        let structTy = LLVM.StructureType False (isize : map (genTy . typeof) free)
        castPtr <- bitcast freePtr (ptr structTy) `named` "free.cast"
        let
          loadFree n = do
            varPtr <- gep castPtr [lcint 32 0, lcint 32 n] `named` "free.ptr"
            load varPtr 0 `named` "free"
        sequence $ map loadFree [1 .. toInteger (length free)]
      res <- call func (map (\x -> (x, [])) (loadedFrees ++ args)) `named` "forward"
      ret res
      where
        iter p a []     = return (a, p)
        iter p a (x:xs) = do
          cast <- bitcast p (ptr $ LLVM.StructureType False [isize, genTy $ typeof x, ptr i8]) `named` "data.cast"
          paramPtr <- gep cast [lcint 32 0, lcint 32 1] `named` "data.param.ptr"
          param <- load paramPtr 0 `named` "data.param"
          rcInc 1 param (typeof x)
          nextPtr <- gep cast [lcint 32 0, lcint 32 2] `named` "data.next.ptr"
          next <- load nextPtr 0 `named` "data.next"
          iter next (param:a) xs
  fwd <-
    llvmFn $ newFn
      { fnLinkage = localHidden,
        fnName = "fwd." ++ currentValue ++ "." ++ show len ++ ".",
        fnPrefix =
          if null destructors then
            Nothing
          else Just $ C.Array
            (ptr $ LLVM.FunctionType void [ptr i8] False)
            (reverse destructors),
        fnRetTy = returnType,
        fnParams = [(ptr i8, "data.ptr"), paramType $ last params],
        fnBody = Just fwdBody }
  let
    result = ClosureData
      { getClosureIndex = len,
        getFreeVars = free,
        getParameters = params,
        getInnerExpr = expr,
        getFunc = func,
        getFwd = fwd }
  return result

buildDestructorList :: [Type] -> [Type] -> BuilderState [C.Constant]
buildDestructorList [] [] = return []
buildDestructorList [] frees = (: []) <$> buildDestructorNA frees
buildDestructorList (args@(t:ts)) frees = do
  rest <- buildDestructorList ts frees
  (: rest) <$> buildDestructor args frees

buildDestructorNA :: [Type] -> BuilderState C.Constant
buildDestructorNA frees
  | not $ any isRc frees = toConstant <$> genFree
  | otherwise = do
    destructors <- gets getDestructors
    case Map.lookup label destructors of
      Just destructor -> return destructor
      Nothing -> genDestructor label functionName body
  where
    label = ([], frees)
    functionName = "destructor;" ++ typeFmt frees
    body [dataPtr] = do
      block `named` "entry"
      wordSize <- lift $ gets getWordSize
      let isize = LLVM.IntegerType wordSize
      castPtr <- bitcast dataPtr (ptr (LLVM.StructureType False (isize : map genTy frees)))
      sequence_ $ zipWith (gen castPtr) frees [1..]
      callFree dataPtr
      retVoid
    gen castPtr ty n
      | isRc ty = do
        ptr <- gep castPtr [lcint 32 0, lcint 32 n] `named` "ptr"
        val <- load ptr 0 `named` "val"
        rcDec (-1) val ty
      | otherwise = return ()

buildDestructor :: [Type] -> [Type] -> BuilderState C.Constant
buildDestructor [] frees = buildDestructorNA frees
buildDestructor (args@(t:ts)) frees
  | null ts && null frees && not (isRc t) = toConstant <$> genFree
  | otherwise = do
    destructors <- gets getDestructors
    case Map.lookup label destructors of
      Just destructor -> return destructor
      Nothing -> genDestructor label functionName body
  where
    label = (args, frees)
    functionName = "destructor;" ++ typeFmt args ++ ';' : typeFmt frees
    body [dataPtr] = do
      block `named` "entry"
      wordSize <- lift $ gets getWordSize
      let isize = LLVM.IntegerType wordSize
      castPtr <- bitcast dataPtr (ptr (LLVM.StructureType False [isize, genTy t, ptr isize])) `named` "cast.ptr"
      if isRc t then do
        ptr <- gep castPtr [lcint 32 0, lcint 32 1] `named` "ptr"
        val <- load ptr 0 `named` "val"
        rcDec (-1) val t
      else return ()
      if null ts && null frees
        then do
          callFree dataPtr
          retVoid
        else mdo
          nextPtr <- gep castPtr [lcint 32 0, lcint 32 2] `named` "next.ptr"
          next <- load nextPtr 0 `named` "next"
          rc <- load next 0 `named` "rc"
          newRc <- add rc (lcint wordSize (-1)) `named` "new.rc"
          callFree dataPtr
          continue <- icmp ICMP.EQ newRc (lcint 32 0) `named` "continue"
          condBr continue yes no

          yes <- block `named` "yes"
          nextDestructor <- lift $ buildDestructor ts frees
          cast <- bitcast next (ptr i8) `named` "next.cast"
          call (LLVM.ConstantOperand nextDestructor) [(cast, [])]
          retVoid

          no <- block `named` "no"
          store next 0 newRc
          retVoid

typeFmt :: [Type] -> String
typeFmt types = intercalate "," $ map show types

toConstant :: Operand -> C.Constant
toConstant (LLVM.ConstantOperand c) = c

genDestructor :: DestructorEntry -> String -> ([Operand] -> Builder ()) -> BuilderState C.Constant
genDestructor label name body = do
  destructor <-
    llvmFn $ newFn
      { fnName = name,
        fnRetTy = void,
        fnParams = [(ptr i8, "data.ptr")],
        fnBody = Just body }
  let c = toConstant destructor
  modify (\s -> s { getDestructors = Map.insert label c (getDestructors s) })
  return c

genClosureForData :: Env (Typed Operand) -> ClosureData -> Builder Operand
genClosureForData env closureData = do
  wordSize <- lift (gets getWordSize)
  let
    isize = LLVM.IntegerType wordSize
    params = getParameters closureData
    frees = getFreeVars closureData
    storedType = isize : map (genTy . typeof) frees
    funcPtr = LLVM.ConstantOperand $ C.BitCast (toConstant $ getFwd closureData) (ptr voidFuncTy)
  dataPtr <- if null frees then
      return $ LLVM.ConstantOperand $ C.Null $ ptr i8
    else do
      (dataPtr, dataPtrI8) <- malloc $ LLVM.StructureType False storedType
      addr <- gep dataPtr [lcint 32 0, lcint 32 0] `named` "rc.ptr"
      store addr 0 (lcint wordSize 1)
      let
        freeMap (name ::: _) n =
          case lookup name env of
            Nothing -> error ("missing capture for closure: `" ++ show name ++ "`")
            Just (res ::: _) -> do
              addr <- gep dataPtr [lcint 32 0, lcint 32 n] `named` "capture"
              store addr 0 res
      sequence_ $ zipWith freeMap frees [1..]
      return dataPtrI8
  genStruct [funcPtr, lcint 32 $ toInteger $ negate $ length params, dataPtr]

genCaller :: Maybe LLVM.Type -> ([Operand] -> Builder ()) -> Operand -> Operand -> Builder Operand
genCaller output body closure arg = do
  m <- lift $ gets getCallers
  let
    index = Map.size m
    argty = LLVM.typeOf arg
    retty =
      case output of
        Just ty -> ty
        Nothing -> funcTy
    key = (argty, output)
  caller <- case Map.lookup key m of
    Nothing -> do
      caller <-
        lift $ llvmFn $ newFn
          { fnLinkage = localHidden,
            fnName = "caller." ++ show index ++ ".",
            fnRetTy = retty,
            fnParams = [(funcTy, ParameterName "closure"), (argty, ParameterName "arg")],
            fnBody = Just body }
      lift $ modify $ \s -> s { getCallers = Map.insert key caller m }
      return caller
    Just caller -> return caller
  call caller [(closure, []), (arg, [])]

genCallClosureNF :: LLVM.Type -> Operand -> Operand -> Builder Operand
genCallClosureNF retType =
  genCaller (Just retType) $ \[closure, arg] -> do
    block `named` "entry"
    funcPtr <- extractValue closure [0] `named` "func.ptr"
    dataPtr <- extractValue closure [2] `named` "data.ptr"
    let funcTy = LLVM.FunctionType retType [ptr i8, LLVM.typeOf arg] False
    castFunc <- bitcast funcPtr (ptr funcTy) `named` "func.cast"
    res <- call castFunc [(dataPtr, []), (arg, [])] `named` "res"
    fnDec (-1) closure
    ret res

genCallClosure :: Operand -> Operand -> Builder Operand
genCallClosure =
  genCaller Nothing $ \[closure, arg] -> mdo
    block `named` "entry"
    wordSize <- lift $ gets getWordSize
    let isize = LLVM.IntegerType wordSize
    arity <- extractValue closure [1] `named` "arity"
    dataPtr <- extractValue closure [2] `named` "data.ptr"
    isSaturated <- icmp ICMP.EQ arity (lcint 32 (-1)) `named` "saturated"
    condBr isSaturated thenBlock elseBlock

    thenBlock <- block `named` "call.saturated"
    funcPtr <- extractValue closure [0] `named` "func.ptr"
    let castTy = LLVM.FunctionType funcTy [ptr i8, LLVM.typeOf arg] False
    castFunc <- bitcast funcPtr (ptr castTy) `named` "func.cast"
    thenRes <- call castFunc [(dataPtr, []), (arg, [])] `named` "res.sat"
    fnDec (-1) closure
    ret thenRes

    -- For unsaturated calls, the rc doesn't need to be decremented because
    -- the existing closure reference is stored in the new data pointer
    elseBlock <- block `named` "call.unsaturated"
    (newDataPtr, newDataPtrI8) <- malloc $ LLVM.StructureType False [isize, LLVM.typeOf arg, ptr i8]
    newRcPtr <- gep newDataPtr [lcint 32 0, lcint 32 0] `named` "data.rc"
    store newRcPtr 0 (lcint wordSize 1)
    argPtr <- gep newDataPtr [lcint 32 0, lcint 32 1] `named` "data.arg"
    store argPtr 0 arg
    nextPtr <- gep newDataPtr [lcint 32 0, lcint 32 2] `named` "data.next"
    store nextPtr 0 dataPtr
    newArity <- add arity (lcint 32 1) `named` "arity.new"
    closureUpdated <- insertValue closure newArity [1] `named` "insert"
    elseRes <- insertValue closureUpdated newDataPtrI8 [2] `named` "res.unsat"
    ret elseRes

lcint :: Word32 -> Integer -> Operand
lcint n m = LLVM.ConstantOperand $ C.Int n m

genStruct :: [Operand] -> Builder Operand
genStruct operands = iter 0 operands $ LLVM.ConstantOperand $ C.Struct Nothing False $ map base operands
  where
    base (LLVM.ConstantOperand c) = c
    base (LLVM.LocalReference t _) = C.Undef t
    base (LLVM.MetadataOperand _) = error "metadata not allowed in struct"

    iter _ [] o = return o
    iter n (LLVM.ConstantOperand _ : xs) o = iter (n+1) xs o
    iter n (x:xs) o = insertValue o x [n] >>= iter (n+1) xs

malloc :: LLVM.Type -> Builder (Operand, Operand)
malloc ty = do
  s <- lift get
  let wordSize = getWordSize s
  malloc <- case getMalloc s of
    Nothing -> do
      malloc <-
        lift $ llvmFn $ newFn
          { fnName = "malloc",
            fnRetTy = ptr i8,
            fnParams = [(LLVM.IntegerType wordSize, NoParameterName)] }
      lift $ put $ s { getMalloc = Just malloc }
      return malloc
    Just malloc -> return malloc
  let gep = C.GetElementPtr False (C.Null $ ptr ty) [C.Int 32 1]
  let size = LLVM.ConstantOperand $ C.PtrToInt gep (LLVM.IntegerType wordSize)
  res <- call malloc [(size, [])] `named` "malloc.call"
  cast <- bitcast res (ptr ty) `named` "malloc.ptr"
  return (cast, res)

genFree :: BuilderState Operand
genFree = do
  s <- get
  case getFree s of
    Nothing -> do
      free <-
        llvmFn $ newFn
          { fnName = "free",
            fnRetTy = void,
            fnParams = [(ptr i8, NoParameterName)] }
      put $ s { getFree = Just free }
      return free
    Just free -> return free

callFree :: Operand -> Builder ()
callFree arg = do
  free <- lift genFree
  cast <- bitcast arg (ptr i8) `named` "free.ptr"
  call free [(cast, [])]
  return ()

puts :: String -> Builder ()
puts string = do
  s <- lift get
  let count = getStringCount s
  (count, puts) <- case getPuts s of
    Nothing -> do
      puts <-
        lift $ llvmFn $ newFn
          { fnName = "puts",
            fnRetTy = i32,
            fnParams = [(ptr i8, NoParameterName)] }
      lift $ put $ s { getStringCount = count+1, getPuts = Just puts }
      return (count, puts)
    Just puts -> do
      lift $ put $ s { getStringCount = count+1 }
      return (count, puts)
  str <- emitString count string
  call puts [(str, [])] `named` (fromString ("_" ++ show count))
  return ()

tyFmt :: Type -> String
tyFmt (TId "Unit") = "unit"
tyFmt (TId "Bool") = "bool(%d)"
tyFmt (TId "Nat") = "nat(%llu)"
tyFmt (TFunc _ _) = fnFmt

fnFmt :: String
fnFmt = "func(%p, %d, %p)"

printf :: String -> [Operand] -> Builder ()
printf fmt args = do
  s <- lift get
  let wordSize = getWordSize s
  let count = getStringCount s
  (count, printf) <- case getPrintf s of
    Nothing -> do
      printf <-
        lift $ llvmFn $ newFn
          { fnVarargs = True,
            fnRetTy = i32,
            fnParams = [(ptr i8, "fmt")],
            fnName = "printf" }
      lift $ put $ s { getStringCount = count+1, getPrintf = Just printf }
      return (count, printf)
    Just printf -> do
      lift $ put $ s { getStringCount = count+1 }
      return (count, printf)
  str <- emitString count (fmt ++ "\n")
  call printf ((str, []) : map (\x -> (x, [])) args) `named` (fromString ("_" ++ show count))
  return ()

emitString :: Int -> String -> Builder Operand
emitString count string = lift $ do
  global <- llvmGlobal $ newGlobal
      { globalName = "str." ++ show count,
        globalLinkage = L.Private,
        globalUnnamedAddress = True,
        globalConstant = True,
        globalType = LLVM.ArrayType (fromIntegral (length asciiString)) i8,
        globalInitializer = Just (C.Array i8 asciiString) }
  return $ LLVM.ConstantOperand $ C.BitCast global (ptr i8)
  where
    asciiString = map charToByte (string ++ "\0")
    charToByte ch = C.Int 8 (toInteger (fromEnum ch))

debugTrap :: Builder ()
debugTrap = do
  s <- lift get
  debugTrap <- case getDebugTrap s of
    Nothing -> do
      debugTrap <-
        lift $ llvmFn $ newFn
          { fnName = "llvm.debugtrap",
            fnRetTy = void,
            fnParams = [],
            fnAttrs = [FnAttr.NoUnwind] }
      lift $ put $ s { getDebugTrap = Just debugTrap }
      return debugTrap
    Just debugTrap ->
      return debugTrap
  call debugTrap []
  return ()

llvmGlobal :: GlobalHelper -> BuilderState C.Constant
llvmGlobal GlobalHelper {..} = do
  let llname = fromString globalName
  emitDefn $ LLVM.GlobalDefinition (LLVM.GlobalVariable
    llname
    globalLinkage
    globalVisibility
    Nothing
    Nothing
    (if globalUnnamedAddress then Just LLVM.GlobalAddr else Nothing)
    globalConstant
    globalType
    (AddrSpace 0)
    globalInitializer
    Nothing
    Nothing
    0
    [])
  return $ C.GlobalReference (ptr globalType) llname

data GlobalHelper = GlobalHelper
  { globalName :: String,
    globalLinkage :: L.Linkage,
    globalVisibility :: V.Visibility,
    globalUnnamedAddress :: Bool,
    globalConstant :: Bool,
    globalType :: LLVM.Type,
    globalInitializer :: Maybe C.Constant }

newGlobal :: GlobalHelper
newGlobal = GlobalHelper
  { globalName = error "missing global name",
    globalLinkage = L.External,
    globalVisibility = V.Default,
    globalUnnamedAddress = False,
    globalConstant = error "missing global constant",
    globalType = error "missing global type",
    globalInitializer = Nothing }

llvmFn :: FunctionHelper -> BuilderState Operand
llvmFn FunctionHelper {..} = do
  (params, blocks) <- runIRBuilderT emptyIRBuilder $ do
    params <- sequence $ flip map fnParams $ \(t, x) -> case x of
      NoParameterName -> (,) t <$> fresh
      ParameterName p -> (,) t <$> fresh `named` p
    case fnBody of
      Nothing -> return ()
      Just body ->
        body $ map (uncurry LLVM.LocalReference) params
    return params
  let llname = fromString fnName
  let ty = ptr (LLVM.FunctionType fnRetTy (map fst params) fnVarargs)
  emitDefn $ LLVM.GlobalDefinition (LLVM.Function
    fnLinkage
    fnVisibility
    Nothing
    fnCC
    []
    fnRetTy
    llname
    (map (\(t, n) -> LLVM.Parameter t n []) params, fnVarargs)
    (map Right fnAttrs)
    Nothing
    Nothing
    0
    Nothing
    fnPrefix
    blocks
    Nothing
    [])
  return $ LLVM.ConstantOperand $ C.GlobalReference ty llname

data FunctionHelper = FunctionHelper
  { fnName :: String,
    fnLinkage :: L.Linkage,
    fnVisibility :: V.Visibility,
    fnCC :: CC.CallingConvention,
    fnPrefix :: Maybe C.Constant,
    fnRetTy :: LLVM.Type,
    fnParams :: [(LLVM.Type, ParameterName)],
    fnVarargs :: Bool,
    fnAttrs :: [FnAttr.FunctionAttribute],
    fnBody :: Maybe ([Operand] -> Builder ()) }

newFn :: FunctionHelper
newFn = FunctionHelper
  { fnName = error "missing function name",
    fnLinkage = L.External,
    fnVisibility = V.Default,
    fnCC = CC.C,
    fnPrefix = Nothing,
    fnRetTy = error "missing return type",
    fnParams = error "missing parameter types",
    fnVarargs = False,
    fnAttrs = [],
    fnBody = Nothing }
