{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}

module Compile (testCompile) where

import AST

import qualified LLVM.AST as LLVM
import LLVM.AST (Operand)
import LLVM.AST.IntegerPredicate as ICMP
import LLVM.AST.AddrSpace
import LLVM.IRBuilder.Constant
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Instruction as INST
import LLVM.IRBuilder.Monad

import LLVM.Pretty

import Data.Maybe
import Data.String
import Data.Text.Lazy (unpack)

type Builder = IRBuilderT ModuleBuilder

testCompile :: Env (Typed Expr) -> IO ()
testCompile env =
  putStrLn
  $ unlines
  $ map (unpack . ppll)
  $ execModuleBuilder emptyModuleBuilder
  $ genAllVals env

genAllVals :: Env (Typed Expr) -> ModuleBuilder (Env Operand)
genAllVals env = sequence $ map genValFunc env

genValFunc :: (Name, Typed Expr) -> ModuleBuilder (Name, Operand)
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
    Id name -> return $ fromJust $ lookup name env
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
    other -> error ("not yet implemented: code gen for " ++ show other)

genTy :: Type -> LLVM.Type
genTy (TId "Nat") = LLVM.IntegerType 64
genTy (TId "Bool") = LLVM.IntegerType 1
genTy (TFunc _ _) = funcTy

funcTy :: LLVM.Type
funcTy = LLVM.StructureType False [pointer infoTy, pointer (LLVM.IntegerType 8)]

infoTy :: LLVM.Type
infoTy = LLVM.StructureType False [pointer (LLVM.FunctionType LLVM.VoidType [] False), pointer destructorTy]

destructorTy :: LLVM.Type
destructorTy = LLVM.FunctionType LLVM.VoidType [pointer (LLVM.IntegerType 8)] False

pointer :: LLVM.Type -> LLVM.Type
pointer ty = LLVM.PointerType ty (AddrSpace 0)

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
