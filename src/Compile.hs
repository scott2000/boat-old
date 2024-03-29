{-# LANGUAGE RecursiveDo, OverloadedStrings, RecordWildCards, FlexibleContexts #-}

module Compile (compile) where

import AST
import Run

import qualified LLVM.AST as LLVM
import qualified LLVM.AST.Typed as LLVM
import qualified LLVM.AST.FunctionAttribute as FnAttr
import qualified LLVM.AST.ParameterAttribute as ParamAttr
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Linkage as L
import qualified LLVM.AST.Visibility as V
import qualified LLVM.AST.IntegerPredicate as ICMP
import LLVM.AST (Operand)
import LLVM.AST.AddrSpace
import LLVM.AST.Type (void, i1, i8, i32, i64, ptr)
import LLVM.IRBuilder.Constant
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Instruction as INST
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Internal.SnocList

import LLVM.Internal.Target (withHostTargetMachine, getTargetMachineDataLayout)
import LLVM.Internal.Context (withContext)
import LLVM.Module (File (..), moduleAST, withModuleFromAST, writeObjectToFile)
import LLVM.PassManager (PassSetSpec (..), defaultCuratedPassSetSpec, withPassManager, runPassManager)

import LLVM.Pretty

import System.FilePath

import Data.Word
import Data.List
import Data.String
import Control.Monad.State hiding (void)
import Control.Monad.Trans.Maybe
import Data.Text.Lazy (unpack)
import qualified Data.Map as Map

{- TODO remove excessive `lift`s

Current Goals:

- replace let with match in implementation (being careful of `rec`)
- reimplement repl
- data modules (constructors in separate module, module extension)
- better error handling
- char, int, float types
- slices/arrays/strings?
- string, list, tuple syntactic sugar
- compile-time simplification (with gas limit)
- prefix and suffix operators (use ~ for negation?)
- replace Unit and Bool with user-defined types
- name resolution based on namespaces (module/data/value)
- user-defined operators (generalized names)
- typeclasses and constraints
- full generic type verification (kinds for type parameters)
- standard library

Possible Future Optimizations:

- statically optimized currying
    (not using application)
- remove error block from pattern match when unnecessary
    (possibly emit warning if inexhaustive?)
- replacement of recursion for top-level values with `rec` keyword where applicable
    (possibly emit warning?)
- tuple expansion into arguments, substitute `void` for `unit`

-}

debugMode :: Bool
debugMode = True

type DestructorEntry = ([Type], [Type]) -- args, frees
type FunctionEntry = (LLVM.Type, Maybe LLVM.Type) -- arg, (Just = NF ret, Nothing = function)

data Codegen = Codegen
  { anonymousFunctions :: [ClosureData],
    getRunMap :: RunMap,
    datas :: Env DataDecl,
    getWordSize :: !Word32,
    getDestructors :: Map.Map DestructorEntry C.Constant,
    getCallers :: Map.Map FunctionEntry Operand,
    getStaticAllocs :: Map.Map [C.Constant] C.Constant,
    getDataArrays :: Map.Map [[Type]] Operand,
    getPtrDestructors :: Map.Map [Type] C.Constant,
    getStrings :: Map.Map String (Int, Operand),
    getReprPrinters :: Map.Map [(String, [Type])] C.Constant,
    getPtrDestructorCaller :: Maybe Operand,
    getInc :: Maybe Operand,
    getFnDec :: Maybe Operand,
    getMalloc :: Maybe Operand,
    getFree :: Maybe Operand,
    getPuts :: Maybe Operand,
    getPrintf :: Maybe Operand,
    getDebugTrap :: Maybe Operand,
    getExit :: Maybe Operand,
    getSideEffect :: Maybe Operand,
    -- generator state
    getRecBrInfo :: Maybe (LLVM.Name, [(LLVM.Name, [Operand])]),
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
type FallibleBuilder = MaybeT Builder

newCodegen :: RunMap -> Env DataDecl -> Word32 -> Codegen
newCodegen runMap datas wordSize = Codegen
  { anonymousFunctions = [],
    getRunMap = runMap,
    datas = datas,
    getWordSize = wordSize,
    getDestructors = Map.empty,
    getCallers = Map.empty,
    getStaticAllocs = Map.empty,
    getDataArrays = Map.empty,
    getPtrDestructors = Map.empty,
    getStrings = Map.empty,
    getReprPrinters = Map.empty,
    getPtrDestructorCaller = Nothing,
    getInc = Nothing,
    getFnDec = Nothing,
    getMalloc = Nothing,
    getFree = Nothing,
    getPuts = Nothing,
    getPrintf = Nothing,
    getDebugTrap = Nothing,
    getExit = Nothing,
    getSideEffect = Nothing,
    getRecBrInfo = Nothing,
    getFunctionName = "main" }

allValues :: BuilderState [Name]
allValues = Map.keys <$> gets getRunMap

inVal :: (MonadIRBuilder m, MonadState Codegen m) => m a -> String -> m a
inVal builder name' = inLet builder (const name')

inLet :: (MonadIRBuilder m, MonadState Codegen m) => m a -> (String -> String) -> m a
inLet builder namef = do
  s <- get
  let name = getFunctionName s
  put (s { getFunctionName = namef name })
  r <- builder
  modify $ \s -> s { getFunctionName = name }
  return r

compile :: FilePath -> Typed Value -> RunMap -> Env DataDecl -> Word32 -> IO ()
compile boatPath mainVal runMap datas wordSize = do
  let
    (boatDir, boatFile) = splitFileName boatPath
    boatName = dropExtension boatFile
    path = boatDir </> "out" </> boatName
    m = buildModule (fromString boatName)
      $ evalStateT (genMain mainVal)
      $ newCodegen runMap datas wordSize
    ofile = File (path <.> "o")
  putStrLn $ unpack $ ppllvm m
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
        writeObjectToFile tm ofile cm
        mm <- moduleAST cm
        writeFile (path <.> "ll") $ unpack $ ppllvm mm

genMain :: Typed Value -> BuilderState Operand
genMain mainVal = do
  wordSize <- gets getWordSize
  llvmFn $ newFn
    { fnName = "main",
      fnRetTy = i32,
      fnParams = [],
      fnBody = Just generator }
  where
    generator _ = do
      block `named` "entry"
      res <- genVal False mainArgs [] mainVal `named` "main.res"
      printf " => " []
      printx res retType
      printf "\n" []
      rcDec 1 res retType
      ret (lcint 32 0)
    (retType, mainArgs) =
      case typeof mainVal of
        TFunc TUnit r -> (r, [unit])
        r -> (r, [])

genVal :: Bool -> [Operand] -> Env (Typed Operand) -> Typed Value -> Builder Operand
genVal isConstant app env (v ::: ty) =
  case v of
    Unit -> return unit
    Nat n -> int64 (toInteger n)
    Bool False -> bit 0
    Bool True -> bit 1
    Cons name variant list -> do
      datas <- gets datas
      let DataDecl {..} = lookup' name datas
      v <- case variants of
        [_] -> do
          let genCons expr = toConstant <$> genVal isConstant [] [] expr
          sequence $ map genCons list
        (_:_) -> do
          zeroSized <- lift $ allZeroSized $ map typeof list
          if zeroSized then
            return [C.Int 32 number, C.Null $ ptr i8]
          else do
            let genCons expr = toConstant <$> genVal True [] [] expr
            args <- sequence $ map genCons list
            global <- staticAlloc args
            if isConstant then
              return ()
            else do
              let rcPtr = LLVM.ConstantOperand $ C.GetElementPtr False global [C.Int 32 0, C.Int 32 0]
              rc <- load rcPtr 0 `named` "static.rc"
              newRc <- addNUW rc (lcint 32 1) `named` "static.newRc"
              store rcPtr 0 newRc
            return [C.Int 32 number, C.BitCast global $ ptr i8]
          where
            number = getVariantId variant variants
      return $ LLVM.ConstantOperand $ C.Struct Nothing False v
    Func xs expr -> do
      closureData <- lift (getStaticClosureData xs expr)
      if length (getParameters closureData) == length app then
        genStaticCall app env closureData
      else do
        genClosureForData env closureData >>= genApp ty app

unit :: Operand
unit = LLVM.ConstantOperand (C.Struct Nothing False [])

genExpr :: [Operand] -> Env (Typed Operand) -> Typed Expr -> FallibleBuilder Operand
genExpr app env (expr ::: ty) =
  case expr of
    Val v ->
      lift $ genVal False app env (v ::: ty)
    App a b -> do
      arg <- genExpr [] env b `named` "app.arg"
      genExpr (arg:app) env a
    Id name ->
      lift $ case lookup name env of
        Just (x ::: _) -> genApp ty app x
        Nothing -> do
          s <- lift get
          case evaluate (name ::: ty) $ getRunMap s of
            Left err -> do
              n <- gets getFunctionName
              error ("error evaluating " ++ show name ++ ": " ++ err ++ " (in " ++ n ++ ")\n"
                ++ "  current environment: " ++ show (map (show . fst) env))
              -- TODO proper error handling
            Right (val, runMap) -> do
              put $ s { getRunMap = runMap }
              genVal False app [] val `inVal` show name
    Op op a b -> do
      let aTy = typeof a
      let bTy = typeof b
      a <- genExpr [] env a `named` "lhs"
      b <- genExpr [] env b `named` "rhs"
      lift $ rcDec 1 a aTy
      lift $ rcDec 1 b bTy
      r <- lift $ genOp op a b
      lift $ genApp ty app r
    If (Val (Bool b) ::: _) t e ->
      if b then
        genExpr app env t
      else
        genExpr app env e
    If i t e -> do
      let thenScope = countLocals t localEnv
      let elseScope = countLocals e localEnv
      let diffScopeT = zipEnv minzdiff thenScope elseScope
      let diffScopeE = zipEnv minzdiff elseScope thenScope
      i <- genExpr [] env i `named` "if.cond"
      genIf i (genExpr app env t) (genExpr app env e) (map fromEnv diffScopeT) (map fromEnv diffScopeE)
    Let (name ::: ty) val expr -> do
      let inc = countOccurances name expr (-1)
      if inc == (-1) then
        genExpr app env expr
      else do
        val <- genExpr [] env val `named` (fromString $ show name) `inLet` (++ "." ++ show name)
        if inc /= 0 then
          lift $ rcInc inc val ty
        else
          return ()
        genExpr app ((name, val ::: ty):env) expr
    Match exprs cases -> mdo
      initialVals <- sequence $ for2 [0..] exprs $ \n expr ->
        (::: typeof expr) <$> genExpr [] env expr `named` fromString ("match.expr." ++ show n)
      let isRec = casesContainRec cases
      initialS <- get
      vals <-
        if isRec then mdo
          entryBlock <- currentBlock
          br matchBlock
          matchBlock <- block `named` "match.recurse"
          put $ initialS { getRecBrInfo = Just (matchBlock, []) }
          phis <- sequence $ for2 [0..] initialVals $ \n (v ::: ty) ->
            (::: ty) <$> (phi [(v, entryBlock)] `named` fromString ("match.rec." ++ show n))
          lift couldLoopForever
          return phis
        else
          return initialVals
      let
        modify = matchLocals cases localEnv
        genCases = map toGenCase cases
      phiCases <- lift $ genMatch app env modify vals genCases ok []

      ok <- block `named` "match.ok"
      if isRec then do
        finalS <- get
        put $ finalS { getRecBrInfo = getRecBrInfo initialS }
        case getRecBrInfo finalS of
          Just (targetBlock, startCases) ->
            lift $ updateBlockBranches targetBlock startCases
          Nothing -> error "forgotten rec info"
      else
        return ()
      if null phiCases then do
        unreachable
        mzero
      else
        phi phiCases
    Panic msg -> do
      if null msg then
        lift $ puts emptyPanic
      else
        lift $ puts msg
      lift $ exit 1
      unreachable
      mzero
    Rec args -> do
      let gen n expr = genExpr [] env expr `named` fromString ("rec.arg." ++ show n)
      vals <- sequence $ zipWith gen [0..] args
      blockName <- currentBlock
      s <- get
      case getRecBrInfo s of
        Just (targetBlock, branches) -> do
          br targetBlock
          put $ s { getRecBrInfo = Just (targetBlock, (blockName, vals) : branches) }
          mzero
        Nothing -> error "rec outside match"
    ICons name variant list -> do
      let
        genCons n expr = do
          genExpr [] env expr `named` fromString ("cons." ++ show variant ++ "." ++ show n)
      args <- sequence $ zipWith genCons [0..] list
      datas <- gets datas
      let DataDecl {..} = lookup' name datas
      lift $ case variants of
        [_] ->
          genStruct args
        (_:_)
          | all (isZeroSized . LLVM.typeOf) args ->
            genStruct [lcint 32 number, LLVM.ConstantOperand $ C.Null $ ptr i8]
          | otherwise -> do
            wordSize <- lift $ gets getWordSize
            (dataPtr, dataPtrI8) <- malloc $ LLVM.StructureType False (LLVM.IntegerType wordSize : map LLVM.typeOf args)
            rcPtr <- gep dataPtr [lcint 32 0, lcint 32 0] `named` "ptr.rc"
            store rcPtr 0 $ lcint wordSize 1
            let
              storeAtOffset n arg = do
                newPtr <- gep dataPtr [lcint 32 0, lcint 32 $ n+1] `named` fromString ("ptr." ++ variant ++ "." ++ show n)
                store newPtr 0 arg
            sequence_ $ zipWith storeAtOffset [0..] args
            genStruct [lcint 32 number, dataPtrI8]
          where
            number = getVariantId variant variants
  where
    localEnv = toLocalEnv env
    fromEnv (name, count) = (lookup' name env, count)

updateBlockBranches :: LLVM.Name -> [(LLVM.Name, [Operand])] -> Builder ()
updateBlockBranches targetBlock [] = error ("no cases in rec for block: " ++ show targetBlock)
updateBlockBranches targetBlock cases =
  liftIRState $ modify $ \s -> s { builderBlocks = SnocList $ updateAll $ unSnocList $ builderBlocks s }
  where
    len = length $ snd $ head cases
    updateAll [] = error ("cannot find target block: " ++ show targetBlock)
    updateAll (LLVM.BasicBlock name inst term : rest)
      | name == targetBlock =
        let
          iter _ [] = []
          iter n (named : rest)
            | n < len =
              case named of
                name LLVM.:= instruction ->
                  name LLVM.:= change instruction : iter (n+1) rest
                _ -> error "expected named phi"
            | otherwise = named : rest
            where
              change (LLVM.Phi t i m) = LLVM.Phi t (addAll i cases) m
              change _ = error "not enough phi instructions for recursion"
              addAll acc [] = acc
              addAll acc ((name, ops):rest) = addAll ((ops !! n, name):acc) rest
        in
          LLVM.BasicBlock name (iter 0 inst) term : rest
      | otherwise = LLVM.BasicBlock name inst term : updateAll rest

data GenCase = GenCase
  { casePats :: [Typed Pattern],
    caseExpr :: Typed Expr,
    caseEnv :: Env (Typed Operand),
    caseMod :: ModMap }

type ModMap = [(Typed Operand, ModEntry)]

data ModEntry = ModEntry
  { modDirect :: Maybe (C.Constant, Operand),
    modCount :: Int }

showMod :: ModMap -> String
showMod m = intercalate "\n  " $ for m $ \(o ::: ty, ModEntry {..}) ->
  (++ unpack (ppll o) ++ " : " ++ show ty ++ " by " ++ show modCount) $ case modDirect of
    Just (d, p) -> "direct (" ++ unpack (ppll d) ++ ", " ++ unpack (ppll p) ++ ") "
    Nothing -> "indirect "

toGenCase :: MatchCase -> GenCase
toGenCase (pats, expr) = GenCase
  { casePats = pats,
    caseExpr = expr,
    caseEnv = [],
    caseMod = [] }

addModEntry :: Int -> Typed Operand -> ModMap -> ModMap
addModEntry 0 _ m = m
addModEntry i o [] = [(o, entry)]
  where
    entry = ModEntry
      { modDirect = Nothing,
        modCount = i }
addModEntry i o ((k, v) : rest)
  | k == o = (k, v { modCount = modCount v + i }) : rest
  | otherwise = (k, v) : addModEntry i o rest

addModDirect :: Int -> Typed Operand -> C.Constant -> Operand -> ModMap -> ModMap
addModDirect i o d p m =
  case m of
    [] -> [(o, change 0)]
    (k, v) : rest
      | k == o -> (k, change $ modCount v) : rest
      | otherwise -> (k, v) : addModDirect i o d p rest
  where
    change v = ModEntry
      { modDirect = Just (d, p),
        modCount = v + i }

genMatch :: [Operand]
         -> Env (Typed Operand)
         -> Env Int
         -> [Typed Operand]
         -> [GenCase]
         -> LLVM.Name
         -> [(Operand, LLVM.Name)]
         -> Builder [(Operand, LLVM.Name)]
genMatch app env modify = gen Nothing
  where
    gen :: Maybe LLVM.Name
        -> [Typed Operand]
        -> [GenCase]
        -> LLVM.Name
        -> [(Operand, LLVM.Name)]
        -> Builder [(Operand, LLVM.Name)]
    gen err _ [] _ bs = do
      case err of
        Just b -> br b
        Nothing -> unreachable
      return bs
    gen err [] (GenCase { casePats = [], .. } : cases) ok bs = do
      let
        exprLocals = drop (length caseEnv) $ countLocalsWithRec modify caseExpr $ toLocalEnv (caseEnv ++ env)
        updates = zipEnv (-) exprLocals modify
        update [] m = m
        update ((name, n):rest) m
          | n == 0 = update rest m
          | otherwise =
            let o = lookup' name env in
            update rest $ addModEntry n o m
        mods = update updates caseMod
      wordSize <- gets getWordSize
      let isize = LLVM.IntegerType wordSize
      sequence_ $ for mods $ \(o ::: ty, ModEntry {..}) ->
        if modCount > 0 then
          case modDirect of
            Just (C.Null _, _) -> return ()
            Just (_, dataPtr) ->
              incPtr modCount dataPtr
            Nothing ->
              rcInc modCount o ty
        else
          return ()
      sequence_ $ for mods $ \(o ::: ty, ModEntry {..}) ->
        if modCount < 0 then
          case modDirect of
            Just (C.Null _, _) -> return ()
            Just (direct, dataPtr) -> do
              cast <- bitcast dataPtr (ptr isize) `named` "rc.cast"
              llvmFastCall (LLVM.ConstantOperand direct) [(cast, []), (lcint wordSize $ toInteger (-modCount), [])]
              return ()
            Nothing ->
              rcDec (-modCount) o ty
        else
          return ()
      m <- runMaybeT (genExpr app (caseEnv ++ env) caseExpr) `named` "match.res"
      case m of
        Just res -> do
          name <- currentBlock
          br ok
          return ((res, name):bs)
        Nothing ->
          return bs
    gen err (allV@((tv@(v ::: vty)):vs)) (allCases@(GenCase { casePats = (p ::: _):_ } : _)) ok bs = case p of
        PAny binding -> do
          let
            collectAny (GenCase { casePats = (PAny binding ::: _) : ps, .. } : cases) =
              let
                (a, r) = collectAny cases
                newCase =
                  case binding of
                    Nothing -> GenCase
                      { casePats = ps,
                        caseMod = addModEntry (-1) tv caseMod,
                        .. }
                    Just name ->
                      let count = countOccurances name caseExpr 0 in
                      GenCase
                        { casePats = ps,
                          caseEnv = (name, tv) : caseEnv,
                          caseMod = addModEntry (count-1) tv caseMod,
                          .. }
              in
                (newCase : a, r)
            collectAny other = ([], other)
            (cases, rest) = collectAny allCases
          if null rest then
            gen err vs cases ok bs
          else mdo
            blocks <- gen (Just cont) vs cases ok bs
            cont <- block `named` "match.cont"
            gen err allV rest ok blocks
        PNat _ -> mdo
          let
            collectNat (GenCase { casePats = (PNat n ::: _) : ps, .. } : cases) =
              let (m, r) = collectNat cases in
              (Map.insertWith (++) n [GenCase { casePats = ps, .. }] m, r)
            collectNat other = (Map.empty, other)
            (cases, rest) = collectNat allCases
          switch v def branches

          (def, blocks) <-
            if null rest then
              case err of
                Just b -> return (b, bs)
                Nothing -> do
                  def <- block `named` "match.impossible.def"
                  unreachable
                  return (def, bs)
            else do
              def <- block `named` "match.def"
              blocks <- gen err allV rest ok bs
              return (def, blocks)

          let
            natBranches [] bs = return ([], bs)
            natBranches ((n, cs):rest) bs = do
              name <- block `named` fromString ("match.nat." ++ show n)
              blocks <- gen (Just def) vs cs ok bs
              (branches, blocks') <- natBranches rest blocks
              return ((C.Int 64 $ toInteger n, name):branches, blocks')
          (branches, blocks') <- natBranches (Map.toList cases) blocks
          return blocks'
        PBool _ -> mdo
          let
            collectBool (GenCase { casePats = (PBool b ::: _) : ps, .. } : cases) =
              let
                (t, f, r) = collectBool cases
                newCase = GenCase { casePats = ps, .. }
              in
                if b then
                  (newCase : t, f, r)
                else
                  (t, newCase : f, r)
            collectBool other = ([], [], other)
            (t, f, rest) = collectBool allCases
          condBr v thenBlock elseBlock

          thenBlock <- block `named` "match.then"
          blocks <- gen cont vs t ok bs

          elseBlock <- block `named` "match.else"
          blocks' <- gen cont vs f ok blocks

          (cont, blocks'') <-
            if null rest then
              return (err, blocks')
            else mdo
              cont <- block `named` "match.cont"
              blocks'' <- gen err allV rest ok blocks'
              return (Just cont, blocks'')
          return blocks''
        PCons _ _ -> do
          variants <- lift $ getDataVariants $ vty
          case variants of
            [(name, types)] -> do
              let
                collectCons (GenCase { casePats = (PCons _ l ::: _) : ps, .. } : cases) =
                  let (a, r) = collectCons cases in
                  (GenCase { casePats = l ++ ps, .. } : a, r)
                collectCons other = ([], other)
                (cases, rest) = collectCons allCases
              values <- buildTyped types $ buildExtract v
              if null rest then
                gen err (values ++ vs) cases ok bs
              else mdo
                blocks <- gen (Just cont) (values ++ vs) cases ok bs
                cont <- block `named` "match.cont"
                gen err allV rest ok blocks
            (_:_) -> mdo
              let
                collectCons (GenCase { casePats = (PCons n l ::: _) : ps, .. } : cases) =
                  let
                    insert (la, ma) (lb, mb) = (la ++ lb, zipWith (&&) ma mb)
                    (m, r) = collectCons cases
                    isAny (PAny Nothing ::: _) = True
                    isAny (PAny (Just name) ::: _) = countOccurances name caseExpr 0 == 0
                    isAny _ = False
                    anyMap = map isAny l
                  in
                    (Map.insertWith insert (find n) ([GenCase { casePats = l ++ ps, .. }], anyMap) m, r)
                collectCons other = (Map.empty, other)
                find = go 0 variants
                go n ((x, _):xs) name
                  | x == name = n
                  | otherwise = go (n+1) xs name
                (cases, rest) = collectCons allCases
              magic <- extractValue v [0] `named` "match.magic"
              dataPtr <- extractValue v [1] `named` "match.ptr"
              switch magic def branches

              (def, blocks) <-
                if null rest then
                  case err of
                    Just b -> return (b, bs)
                    Nothing -> do
                      def <- block `named` "match.impossible.def"
                      unreachable
                      return (def, bs)
                else do
                  def <- block `named` "match.def"
                  blocks <- gen err allV rest ok bs
                  return (def, blocks)

              let
                consBranches [] bs = return ([], bs)
                consBranches ((n, (cs, anyMap)):rest) bs = do
                  name <- block `named` fromString ("match.cons." ++ show n)
                  let types = snd $ variants !! n
                  wordSize <- gets getWordSize
                  let isize = LLVM.IntegerType wordSize
                  let
                    eliminate [] rest = rest
                    eliminate (True:xs) (_:ys) = eliminate xs ys
                    eliminate (_:xs) (y:ys) = y : eliminate xs ys
                    newTypes = eliminate anyMap types
                  newValues <-
                    if null newTypes then
                      return []
                    else do
                      lltypes <- lift $ sequence $ map genTy newTypes
                      let ty = ptr (LLVM.StructureType False (isize : lltypes))
                      castPtr <- bitcast dataPtr ty `named` fromString ("match.ptr." ++ show n)
                      buildTyped types $ buildGep castPtr
                  decPtr <- lift $ rcPtrDestructorOf types
                  let
                    addMods [] m = m
                    addMods (v:vs) m = addMods vs $ addModEntry 1 v m
                    updateCase GenCase { .. } = GenCase
                      { casePats = eliminate anyMap casePats,
                        caseMod = addModDirect (-1) tv decPtr dataPtr $ addMods newValues caseMod,
                        .. }
                    updatedCases = map updateCase cs
                  blocks <- gen (Just def) (newValues ++ vs) updatedCases ok bs
                  (branches, blocks') <- consBranches rest blocks
                  return ((C.Int 32 $ toInteger n, name):branches, blocks')
              (branches, blocks') <- consBranches (Map.toList cases) blocks
              return blocks'

getVariantId :: String -> [(String, a)] -> Integer
getVariantId name = go 0
 where
   go acc ((n, _):ns)
     | n == name = acc
     | otherwise = go (acc+1) ns

toLocalEnv :: Env (Typed Operand) -> Env Int
toLocalEnv = map (\(x, _) -> (x, 0))

genStaticCall :: [Operand] -> Env (Typed Operand) -> ClosureData -> Builder Operand
genStaticCall args env closureData =
  let
    freeNames = getFreeVars closureData
    frees = for freeNames $ \(name ::: _) ->
      case lookup name env of
        Nothing -> error ("missing free variable: " ++ show name)
        Just (x ::: _) -> (x, [])
  in
    llvmFastCall (getFunc closureData) (frees ++ map (\x -> (x, [])) args)

genApp :: Type -> [Operand] -> Operand -> Builder Operand
genApp _  [] val = return val
genApp (TFunc _ (TFunc _ _)) [arg] closure =
  genCallClosure closure arg
genApp (TFunc _ ty) [arg] closure = do
  rty <- lift $ genTy ty
  genCallClosureNF rty closure arg
genApp (TFunc _ ty) (arg:rest) closure =
  genCallClosure closure arg `named` "partial" >>= genApp ty rest

genIf :: Operand
      -> FallibleBuilder Operand
      -> FallibleBuilder Operand
      -> [(Typed Operand, Int)]
      -> [(Typed Operand, Int)]
      -> FallibleBuilder Operand
genIf i t e diffT diffE = mdo
  condBr i thenBlock elseBlock
  thenBlock <- block `named` "if.then"
  lift $ sequence_ $ map addDiff diffT
  thenList <-lift $ do
    m <- runMaybeT t `named` "if.then.res"
    case m of
      Just res -> do
        resBlock <- currentBlock
        br endBlock
        return [(res, resBlock)]
      Nothing -> return []
  elseBlock <- block `named` "if.else"
  lift $ sequence_ $ map addDiff diffE
  elseList <- lift $ do
    m <- runMaybeT e `named` "if.else.res"
    case m of
      Just res -> do
        resBlock <- currentBlock
        br endBlock
        return ((res, resBlock):thenList)
      Nothing -> return thenList
  endBlock <- block `named` "if.end"
  if null elseList then do
    unreachable
    mzero
  else
    phi elseList
  where
    addDiff (o ::: ty, n)
      | n > 0 = rcInc n o ty
      | n < 0 = rcDec (-n) o ty
      | otherwise = return ()

genTy :: Type -> BuilderState LLVM.Type
genTy = go []
  where
    go l (TApp a b) = go (b:l) a
    go [_, _] TArrow = return funcTy
    go [] TUnit = return unitTy
    go [] TNat = return i64
    go [] TBool = return i1
    go l (TId name) = genDataTy name l

isRc :: Type -> BuilderState Bool
isRc = go []
  where
    go l (TApp a b) = go (b:l) a
    go [_, _] TArrow = return True
    go [] TUnit = return False
    go [] TNat = return False
    go [] TBool = return False
    go l (TId name) = do
      datas <- gets datas
      let DataDecl {..} = lookup' name datas
      case variants of
        [(_, types)] -> anyRc $ for types $ typeReplace typeParams l
        (_:_) -> return True

tyFmt :: LLVM.Type -> String
tyFmt (LLVM.IntegerType 64) = "%llu"
tyFmt (LLVM.IntegerType _) = "%u"
tyFmt (LLVM.PointerType _ _) = "%p"
tyFmt (LLVM.StructureType False []) = "{}"
tyFmt (LLVM.StructureType False list) = "{" ++ intercalate ", " (map tyFmt list) ++ "}"

isZeroSized :: LLVM.Type -> Bool
isZeroSized (LLVM.StructureType _ list) = all isZeroSized list
isZeroSized (LLVM.ArrayType 0 _) = True
isZeroSized (LLVM.ArrayType _ a) = isZeroSized a
isZeroSized _ = False

anyRc :: [Type] -> BuilderState Bool
anyRc [] = return False
anyRc (t:ts) = do
  rc <- isRc t
  if rc then
    return True
  else
    anyRc ts

allZeroSized :: [Type] -> BuilderState Bool
allZeroSized [] = return True
allZeroSized (t:ts) = do
  z <- isZeroSized <$> genTy t
  if z then
    allZeroSized ts
  else
    return False

genDataTy :: Name -> [Type] -> BuilderState LLVM.Type
genDataTy name args = do
  datas <- gets datas
  let DataDecl {..} = lookup' name datas
  case variants of
    [(_, types)] -> do
      let tr = typeReplace typeParams args
      LLVM.StructureType False <$> sequence (map (genTy . tr) types)
    (_:_) ->
      return tyVariant

tyVariant :: LLVM.Type
tyVariant = LLVM.StructureType False [i32, ptr i8]

getDataVariants :: Type -> BuilderState (Env [Type])
getDataVariants = go []
  where
    go :: [Type] -> Type -> BuilderState (Env [Type])
    go l (TApp a b) = go (b:l) a
    go l (TId name) = do
      datas <- gets datas
      let DataDecl {..} = lookup' name datas
      let tr = typeReplace typeParams l
      let updateVariant (n, t) = (name.|.n, map tr t)
      return $ map updateVariant variants

typeReplace :: [String] -> [Type] -> Type -> Type
typeReplace typeParams args = tr
  where
    typeSubstitutions = zip typeParams args
    tr (TVar v) = lookup' v typeSubstitutions
    tr (TApp a b) = TApp (tr a) (tr b)
    tr other = other

unitTy :: LLVM.Type
unitTy = LLVM.StructureType False []

funcTy :: LLVM.Type
funcTy = LLVM.StructureType False [ptr voidFuncTy, i32, ptr i8]

voidFuncTy :: LLVM.Type
voidFuncTy = LLVM.FunctionType void [] False

destructorTy :: LLVM.Type
destructorTy = LLVM.FunctionType void [ptr i8] False

modifierTy :: LLVM.Type -> LLVM.Type
modifierTy isize = LLVM.FunctionType void [ptr isize, isize] False

printx :: Operand -> Type -> Builder ()
printx o = go []
  where
    go l (TApp a b) = go (b:l) a
    go [_, _] TArrow = printf "<func>" []
    go [] TUnit = printf "unit" []
    go [] TNat = printf "%llu" [o]
    go [] TBool = mdo
      condBr o thenBlock elseBlock
      thenBlock <- block `named` "print.then"
      printf "true" []
      br endBlock
      elseBlock <- block `named` "print.else"
      printf "false" []
      br endBlock
      endBlock <- block `named` "print.end"
      return ()
    go l (TId name) = do
      datas <- gets datas
      let DataDecl {..} = lookup' name datas
      let tr = typeReplace typeParams l
      case variants of
        [(name, [])] ->
          printf name []
        [(name, types)] -> do
          printf ("(" ++ name) []
          sequence_ $ for2 [0..] types $ \n ty -> do
            val <- buildExtract o n
            printf " " []
            printx val (tr ty)
          printf ")" []
        (_:_) -> do
          printer <- lift $ getPrinter $ for variants $ \(name, types) -> (name, map tr types)
          llvmFastCall (LLVM.ConstantOperand printer) [(o, [])]
          return ()
          where
            getPrinter variants = do
              s <- get
              let
                printers = getReprPrinters s
                isize = LLVM.IntegerType (getWordSize s)
              case Map.lookup variants printers of
                Nothing -> mdo
                  put $ s { getReprPrinters = Map.insert variants printer printers }
                  let
                    body [v] = mdo
                      block `named` "entry"
                      magic <- extractValue v [0] `named` "match.magic"
                      dataPtr <- extractValue v [1] `named` "match.ptr"
                      switch magic def branches

                      branches <- sequence $ for2 [0..] variants $ \n (name, types) -> do
                        caseBlock <- block `named` fromString name
                        if null types then
                          printf name []
                        else do
                          lltypes <- lift $ sequence $ map (genTy . tr) types
                          castPtr <- bitcast dataPtr (ptr (LLVM.StructureType False (isize : lltypes)))
                          printf ("(" ++ name) []
                          sequence_ $ for2 [0..] types $ \n ty -> do
                            val <- buildGep castPtr n
                            printf " " []
                            printx val (tr ty)
                          printf ")" []
                        return (C.Int 32 n, caseBlock)

                      def <- block `named` "err"
                      unreachable
                  printer <-
                    llvmConstFn $ newFn
                      { fnName = "repr." ++ show (Map.size printers) ++ ".",
                        fnLinkage = L.Private,
                        fnCC = CC.Fast,
                        fnRetTy = void,
                        fnParams = [(tyVariant, ParameterName "variant")],
                        fnBody = Just body }
                  return printer
                Just printer -> return printer

rcInc :: Int -> Operand -> Type -> Builder ()
rcInc i o = go []
  where
    go l (TApp a b) = go (b:l) a
    go [_, _] TArrow = do
      dataPtr <- extractValue o [2] `named` "func.data.ptr"
      incPtr i dataPtr
    go [] TUnit = return ()
    go [] TNat = return ()
    go [] TBool = return ()
    go l (TId name) = do
      datas <- gets datas
      let DataDecl {..} = lookup' name datas
      let tr = typeReplace typeParams l
      case variants of
        [(_, types)] ->
          incDecAll (rcInc i) (buildExtract o) (return ()) $ map tr types
        (_:_) -> do
          p <- extractValue o [1] `named` "rc.ptr"
          incPtr i p

rcDec :: Int -> Operand -> Type -> Builder ()
rcDec i o = go []
  where
    go l (TApp a b) = go (b:l) a
    go [_, _] TArrow = fnDec i o
    go [] TUnit = return ()
    go [] TNat = return ()
    go [] TBool = return ()
    go l (TId name) = do
      datas <- gets datas
      let DataDecl {..} = lookup' name datas
      let tr = typeReplace typeParams l
      case variants of
        [(_, types)] ->
          incDecAll (rcDec i) (buildExtract o) (return ()) $ map tr types
        (_:_) -> do
          arr <- lift $ rcDataArrayOf $ map (map tr . snd) variants
          caller <- lift rcCaller
          wordSize <- lift $ gets getWordSize
          llvmFastCall caller [(arr, []), (o, []), (lcint wordSize $ toInteger i, [])]
          return ()
    rcCaller = do
      s <- get
      case getPtrDestructorCaller s of
        Nothing -> do
          wordSize <- gets getWordSize
          let isize = LLVM.IntegerType wordSize
          let arrty = ptr $ ptr $ modifierTy isize
          let
            body [arr, o, i] = mdo
              block `named` "entry"
              p <- extractValue o [1] `named` "rc.ptr"
              isnull <- icmp ICMP.EQ p (LLVM.ConstantOperand $ C.Null (ptr i8)) `named` "rc.null"
              condBr isnull nullBlock callBlock

              callBlock <- block `named` "call"
              n <- extractValue o [0] `named` "rc.magic"
              rcPtr <- bitcast p (ptr isize) `named` "rc.ptr.cast"
              modPtr <- gep arr [n] `named` "func.ptr"
              func <- load modPtr 0 `named` "func"
              llvmFastCall func [(rcPtr, []), (i, [])]
              retVoid

              nullBlock <- block `named` "null"
              retVoid
          destructor <-
            llvmFn $ newFn
              { fnName = "rc.dec",
                fnLinkage = L.Private,
                fnCC = CC.Fast,
                fnRetTy = void,
                fnParams = [(arrty, "array"), (tyVariant, "data"), (isize, "dec")],
                fnBody = Just body }
          put $ s { getPtrDestructorCaller = Just destructor }
          return destructor
        Just destructor -> return destructor
    rcDataArrayOf variants = do
      s <- get
      let arrays = getDataArrays s
      case Map.lookup variants arrays of
        Nothing -> mdo
          put $ s { getDataArrays = Map.insert variants carr arrays }
          entries <- sequence $ map rcPtrDestructorOf variants
          wordSize <- gets getWordSize
          let isize = LLVM.IntegerType wordSize
          let arrty = ptr $ modifierTy isize
          arr <-
            llvmGlobal $ newGlobal
              { globalName = "rc.arr." ++ show (Map.size arrays),
                globalLinkage = L.Private,
                globalUnnamedAddress = True,
                globalConstant = True,
                globalType = LLVM.ArrayType (fromIntegral $ length variants) arrty,
                globalInitializer = Just (C.Array arrty entries) }
          let carr = LLVM.ConstantOperand (C.GetElementPtr False arr [C.Int 32 0, C.Int 32 0])
          return carr
        Just arr -> return arr

rcPtrDestructorOf :: [Type] -> BuilderState C.Constant
rcPtrDestructorOf types' = do
  zeroSized <- allZeroSized types'
  s <- get
  let isize = LLVM.IntegerType $ getWordSize s
  if zeroSized then
    return $ C.Null $ ptr $ modifierTy isize
  else do
    rc <- anyRc types'
    let destructors = getPtrDestructors s
    let types = if rc then types' else []
    case Map.lookup types destructors of
      Nothing -> mdo
        put $ s { getPtrDestructors = Map.insert types destructor destructors }
        let
          body [rcPtr, i] = mdo
            block `named` "entry"
            rcval <- load rcPtr 0 `named` "rc"
            newRc <- subNUW rcval i `named` "new.rc"
            zero <- icmp ICMP.EQ newRc (lcint 32 0) `named` "zero"
            condBr zero destroy keep

            destroy <- block `named` "destroy"
            let free = callFree rcPtr
            if rc then do
              ts <- lift $ sequence $ map genTy types
              o <- bitcast rcPtr (ptr $ LLVM.StructureType False (isize : ts)) `named` "ptr.cast"
              incDecAll (rcDec 1) (buildGep o) free types
            else free
            retVoid

            keep <- block `named` "keep"
            store rcPtr 0 newRc
            retVoid
        destructor <-
          llvmConstFn $ newFn
            { fnName = "rc.dec." ++ show (Map.size destructors) ++ ".",
              fnLinkage = L.Private,
              fnCC = CC.Fast,
              fnRetTy = void,
              fnParams = [(ptr isize, ParameterName "rc.ptr"), (isize, ParameterName "mod")],
              fnBody = Just body }
        return destructor
      Just destructor -> return destructor

incDecAll :: (Operand -> Type -> Builder ())
          -> (Integer -> Builder Operand)
          -> Builder ()
          -> [Type]
          -> Builder ()
incDecAll op extract middle types = do
  ops <- getValues 0 types
  middle
  sequence_ ops
  where
    getValues _ [] = return []
    getValues n (t:ts) = do
      rc <- lift $ isRc t
      if rc then do
        v <- extract n
        rest <- getValues (n+1) ts
        return (op v t : rest)
      else
        getValues (n+1) ts

buildExtract :: Operand -> Integer -> Builder Operand
buildExtract o n = extractValue o [fromIntegral n] `named` fromString ("i." ++ show n)

buildGep :: Operand -> Integer -> Builder Operand
buildGep o n = do
  ptr <- gep o [lcint 32 0, lcint 32 (n+1)] `named` fromString ("i.ptr." ++ show n)
  load ptr 0 `named` fromString ("i." ++ show n)

buildTyped :: [Type] -> (Integer -> Builder Operand) -> Builder [Typed Operand]
buildTyped types f = go 0 types
  where
    go _ [] = return []
    go n (t:ts) = do
      v <- f n
      r <- go (n+1) ts
      return ((v ::: t) : r)

incPtr :: Int -> Operand -> Builder ()
incPtr i dataPtr = do
  s <- lift get
  let wordSize = getWordSize s
  incrementer <- case getInc s of
    Nothing -> do
      incrementer <-
        lift $ llvmFn $ newFn
          { fnName = "rc.inc",
            fnLinkage = L.Private,
            fnCC = CC.Fast,
            fnRetTy = void,
            fnParams = [(ptr i8, ParameterName "ptr"), (LLVM.IntegerType wordSize, ParameterName "inc")],
            fnBody = Just body }
      lift $ modify $ \s -> s { getInc = Just incrementer }
      return incrementer
    Just incrementer -> return incrementer
  llvmFastCall incrementer [(dataPtr, []), (lcint wordSize $ toInteger i, [])]
  return ()
  where
    body :: [Operand] -> Builder ()
    body [dataPtr, inc] = mdo
      block `named` "entry"
      isnull <- icmp ICMP.EQ dataPtr (LLVM.ConstantOperand $ C.Null (ptr i8)) `named` "isnull"
      condBr isnull nullBlock incBlock

      incBlock <- block `named` "inc"
      wordSize <- lift $ gets getWordSize
      rcPtr <- bitcast dataPtr (ptr $ LLVM.IntegerType wordSize) `named` "rc.ptr"
      rc <- load rcPtr 0 `named` "rc"
      newRc <- addNUW rc inc `named` "rc.new"
      store rcPtr 0 newRc
      retVoid

      nullBlock <- block `named` "null"
      retVoid

fnDec :: Int -> Operand -> Builder ()
fnDec i closure = do
  s <- lift get
  let wordSize = getWordSize s
  decrementer <- case getFnDec s of
    Nothing -> do
      decrementer <-
        lift $ llvmFn $ newFn
          { fnName = "fn.dec",
            fnLinkage = L.Private,
            fnCC = CC.Fast,
            fnRetTy = void,
            fnParams = [(funcTy, ParameterName "closure"), (LLVM.IntegerType wordSize, ParameterName "dec")],
            fnBody = Just body }
      lift $ modify $ \s -> s { getFnDec = Just decrementer }
      return decrementer
    Just decrementer -> return decrementer
  llvmFastCall decrementer [(closure, []), (lcint wordSize $ toInteger i, [])]
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
      newRc <- subNUW rc inc `named` "rc.new"
      zero <- icmp ICMP.EQ newRc (lcint 32 0) `named` "rc.zero"
      condBr zero destroy keep

      destroy <- block `named` "destroy"
      funcPtr <- extractValue closure [0] `named` "func.ptr"
      arity <- extractValue closure [1] `named` "arity"
      destructorList <- bitcast funcPtr (ptr $ ptr destructorTy) `named` "destructors"
      destructorPtr <- gep destructorList [arity] `named` "destructor.ptr"
      destructor <- load destructorPtr 0 `named` "destructor"
      llvmFastCall destructor [(dataPtr, [])]
      retVoid

      keep <- block `named` "keep"
      store rcPtr 0 newRc
      retVoid

      done <- block `named` "done"
      retVoid

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
        Match exprs cases -> do
          sequence_ $ for exprs $ deps env
          sequence_ $ for cases $ \(pats, expr) ->
            deps (map fst (allPatternNames pats) ++ env) expr
        Rec args ->
          sequence_ $ for args $ deps env
        ICons name variant list ->
          sequence_ $ for list $ deps env
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
  returnType <- genTy $ typeof expr
  codegen <- get
  let
    combinedArgs = free ++ params
    freeNames = map valof free
    isFree name = name `elem` freeNames
    body args = do
      block `named` "entry"
      couldLoopForever
      let localScope = countLocals expr localEnv
      sequence_ $ map localInc localScope
      m <- runMaybeT (genExpr [] env expr `named` "ret")
      case m of
        Just res -> ret res
        Nothing -> return ()
      where
        env = zipWith (\p a -> (valof p, a ::: typeof p)) combinedArgs args
        localEnv = toLocalEnv env
        localInc (name, inc)
          | isFree name = rcInc inc o ty
          | inc == 0    = rcDec 1 o ty
          | inc == 1    = return ()
          | otherwise   = rcInc (inc-1) o ty
          where
            (o ::: ty) = lookup' name env
    anons = anonymousFunctions codegen
    currentValue = getFunctionName codegen
    len = length anons
    paramType (name ::: ty) = do
      gen <- genTy ty
      return (gen, fromString $ show name)
    nameBase = currentValue ++ "." ++ show len ++ "."
  put (codegen { anonymousFunctions = result : anons })
  funcParams <- sequence $ map paramType combinedArgs
  func <-
    llvmFn $ newFn
      { fnName = "func." ++ nameBase,
        fnLinkage = L.Private,
        fnCC = CC.Fast,
        fnRetTy = returnType,
        fnParams = funcParams,
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
        lltypes <- lift $ sequence $ map (genTy . typeof) free
        let structTy = LLVM.StructureType False (isize : lltypes)
        castPtr <- bitcast freePtr (ptr structTy) `named` "free.cast"
        let
          loadFree n = do
            varPtr <- gep castPtr [lcint 32 0, lcint 32 n] `named` "free.ptr"
            load varPtr 0 `named` "free"
        sequence $ map loadFree [1 .. toInteger (length free)]
      res <- llvmFastCall func (map (\x -> (x, [])) (loadedFrees ++ args)) `named` "forward"
      ret res
      where
        iter p a []     = return (a, p)
        iter p a (x:xs) = do
          ty <- lift $ genTy $ typeof x
          cast <- bitcast p (ptr $ LLVM.StructureType False [isize, ty, ptr i8]) `named` "data.cast"
          paramPtr <- gep cast [lcint 32 0, lcint 32 1] `named` "data.param.ptr"
          param <- load paramPtr 0 `named` "data.param"
          rcInc 1 param (typeof x)
          nextPtr <- gep cast [lcint 32 0, lcint 32 2] `named` "data.next.ptr"
          next <- load nextPtr 0 `named` "data.next"
          iter next (param:a) xs
  lastparam <- paramType $ last params
  fwd <-
    llvmFn $ newFn
      { fnName = "fwd." ++ nameBase,
        fnLinkage = L.Private,
        fnCC = CC.Fast,
        fnPrefix =
          if null destructors then
            Nothing
          else Just $ C.Array
            (ptr $ LLVM.FunctionType void [ptr i8] False)
            (reverse destructors),
        fnRetTy = returnType,
        fnParams = [(ptr i8, "data.ptr"), lastparam],
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
buildDestructorNA frees = do
  rc <- anyRc frees
  if not rc then
    toConstant <$> genFree
  else do
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
      lltypes <- lift $ sequence $ map genTy frees
      castPtr <- bitcast dataPtr (ptr (LLVM.StructureType False (isize : lltypes)))
      sequence_ $ zipWith (gen castPtr) frees [1..]
      callFree dataPtr
      retVoid
    gen castPtr ty n = do
      rc <- lift $ isRc ty
      if rc then do
        ptr <- gep castPtr [lcint 32 0, lcint 32 n] `named` "ptr"
        val <- load ptr 0 `named` "val"
        rcDec 1 val ty
      else return ()

buildDestructor :: [Type] -> [Type] -> BuilderState C.Constant
buildDestructor [] frees = buildDestructorNA frees
buildDestructor (args@(t:ts)) frees = do
  rc <- isRc t
  if null ts && null frees && not rc then
    toConstant <$> genFree
  else do
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
      ty <- lift $ genTy t
      castPtr <- bitcast dataPtr (ptr (LLVM.StructureType False [isize, ty, ptr isize])) `named` "cast.ptr"
      rc <- lift $ isRc t
      if rc then do
        ptr <- gep castPtr [lcint 32 0, lcint 32 1] `named` "ptr"
        val <- load ptr 0 `named` "val"
        rcDec 1 val t
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
          llvmFastCall (LLVM.ConstantOperand nextDestructor) [(cast, [])]
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
        fnCC = CC.Fast,
        fnRetTy = void,
        fnParams = [(ptr i8, "data.ptr")],
        fnBody = Just body }
  let c = toConstant destructor
  modify (\s -> s { getDestructors = Map.insert label c (getDestructors s) })
  return c

genClosureForData :: Env (Typed Operand) -> ClosureData -> Builder Operand
genClosureForData env closureData = do
  wordSize <- lift (gets getWordSize)
  let frees = getFreeVars closureData
  lltypes <- lift $ sequence $ map (genTy . typeof) frees
  let
    isize = LLVM.IntegerType wordSize
    params = getParameters closureData
    storedType = isize : lltypes
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
          { fnName = "caller." ++ show index ++ ".",
            fnLinkage = L.Private,
            fnCC = CC.Fast,
            fnRetTy = retty,
            fnParams = [(funcTy, ParameterName "closure"), (argty, ParameterName "arg")],
            fnBody = Just body }
      lift $ modify $ \s -> s { getCallers = Map.insert key caller m }
      return caller
    Just caller -> return caller
  llvmFastCall caller [(closure, []), (arg, [])]

genCallClosureNF :: LLVM.Type -> Operand -> Operand -> Builder Operand
genCallClosureNF retType =
  genCaller (Just retType) $ \[closure, arg] -> do
    block `named` "entry"
    funcPtr <- extractValue closure [0] `named` "func.ptr"
    dataPtr <- extractValue closure [2] `named` "data.ptr"
    let funcTy = LLVM.FunctionType retType [ptr i8, LLVM.typeOf arg] False
    castFunc <- bitcast funcPtr (ptr funcTy) `named` "func.cast"
    res <- llvmFastCall castFunc [(dataPtr, []), (arg, [])] `named` "res"
    fnDec 1 closure
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
    thenRes <- llvmFastCall castFunc [(dataPtr, []), (arg, [])] `named` "res.sat"
    fnDec 1 closure
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
  puts <- case getPuts s of
    Nothing -> do
      puts <-
        lift $ llvmFn $ newFn
          { fnName = "puts",
            fnRetTy = i32,
            fnParams = [(ptr i8, NoParameterName)] }
      lift $ put $ s { getPuts = Just puts }
      return puts
    Just puts -> return puts
  (count, str) <- emitString string
  call puts [(str, [])] `named` (fromString ("_" ++ show count))
  return ()

printf :: String -> [Operand] -> Builder ()
printf fmt args = do
  s <- lift get
  let wordSize = getWordSize s
  printf <- case getPrintf s of
    Nothing -> do
      printf <-
        lift $ llvmFn $ newFn
          { fnVarargs = True,
            fnRetTy = i32,
            fnParams = [(ptr i8, "fmt")],
            fnName = "printf" }
      lift $ put $ s { getPrintf = Just printf }
      return printf
    Just printf -> return printf
  (count, str) <- emitString fmt
  call printf ((str, []) : map (\x -> (x, [])) args) `named` (fromString ("_" ++ show count))
  return ()

emitString :: String -> Builder (Int, Operand)
emitString string = lift $ do
  s <- get
  let m = getStrings s
  case Map.lookup string m of
    Nothing -> do
      let count = Map.size m
      global <- llvmGlobal $ newGlobal
          { globalName = "str." ++ show count,
            globalLinkage = L.Private,
            globalUnnamedAddress = True,
            globalConstant = True,
            globalType = LLVM.ArrayType (fromIntegral (length asciiString)) i8,
            globalInitializer = Just (C.Array i8 asciiString) }
      let o = (count, LLVM.ConstantOperand $ C.BitCast global (ptr i8))
      put $ s { getStrings = Map.insert string o m }
      return o
    Just o -> return o
  where
    asciiString = map charToByte (string ++ "\0")
    charToByte ch = C.Int 8 (toInteger (fromEnum ch))

staticAlloc :: [C.Constant] -> Builder C.Constant
staticAlloc values = lift $ do
  s <- get
  let wordSize = getWordSize s
  let m = getStaticAllocs s
  case Map.lookup values m of
    Nothing -> do
      global <- llvmGlobal $ newGlobal
          { globalName = "global." ++ show (Map.size m),
            globalLinkage = L.Private,
            globalUnnamedAddress = True,
            globalConstant = False,
            globalType = LLVM.StructureType False (LLVM.IntegerType wordSize : map LLVM.typeOf values),
            globalInitializer = Just (C.Struct Nothing False (C.Int wordSize 1 : values)) }
      put $ s { getStaticAllocs = Map.insert values global m }
      return global
    Just global ->
      return global

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

exit :: Integer -> Builder ()
exit code = do
  s <- lift get
  exit <- case getExit s of
    Nothing -> do
      exit <-
        lift $ llvmFn $ newFn
          { fnName = "exit",
            fnRetTy = void,
            fnParams = [(i32, "code")],
            fnAttrs = [FnAttr.Cold, FnAttr.NoReturn, FnAttr.NoUnwind] }
      lift $ put $ s { getExit = Just exit }
      return exit
    Just exit ->
      return exit
  call exit [(lcint 32 code, [])]
  return ()

-- prevents llvm from treating infinite loops as undefined behavior
couldLoopForever :: Builder ()
couldLoopForever = do
  s <- lift get
  sideEffect <- case getSideEffect s of
    Nothing -> do
      sideEffect <-
        lift $ llvmFn $ newFn
          { fnName = "llvm.sideeffect",
            fnRetTy = void,
            fnParams = [],
            fnAttrs = [FnAttr.InaccessibleMemOnly, FnAttr.NoUnwind] }
      lift $ put $ s { getSideEffect = Just sideEffect }
      return sideEffect
    Just sideEffect ->
      return sideEffect
  call sideEffect []
  return ()

llvmGlobal :: GlobalHelper -> BuilderState C.Constant
llvmGlobal GlobalHelper {..} = do
  let llname = fromString globalName
  emitDefn $ LLVM.GlobalDefinition (LLVM.GlobalVariable
    llname
    (if debugMode then L.External else globalLinkage)
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
llvmFn f = LLVM.ConstantOperand <$> llvmConstFn f

llvmConstFn :: FunctionHelper -> BuilderState C.Constant
llvmConstFn FunctionHelper {..} = do
  (params, blocks) <- runIRBuilderT emptyIRBuilder $ do
    params <- sequence $ for fnParams $ \(t, x) -> case x of
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
    (if debugMode then L.External else fnLinkage)
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
  return $ C.GlobalReference ty llname

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

llvmFastCall :: Operand -> [(Operand, [ParamAttr.ParameterAttribute])] -> Builder Operand
llvmFastCall func args =
  let
    instr = LLVM.Call
      { LLVM.tailCallKind = if debugMode then Nothing else Just (LLVM.Tail),
        LLVM.callingConvention = CC.Fast,
        LLVM.returnAttributes = [],
        LLVM.function = Right func,
        LLVM.arguments = args,
        LLVM.functionAttributes = [],
        LLVM.metadata = [] }
  in
    case LLVM.typeOf func of
        LLVM.PointerType (LLVM.FunctionType r _ _) _ -> case r of
          LLVM.VoidType -> emitInstrVoid instr >> (pure (LLVM.ConstantOperand (C.Undef void)))
          _ -> emitInstr r instr
        _ -> error "function call expected function pointer"

addNUW :: Operand -> Operand -> Builder Operand
addNUW a b = emitInstr (LLVM.typeOf a) $ LLVM.Add False True a b []

subNUW :: Operand -> Operand -> Builder Operand
subNUW a b = emitInstr (LLVM.typeOf a) $ LLVM.Sub False True a b []
