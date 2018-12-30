{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module Verify where

import AST

import Data.List

data VPattern
  = VAny
  | VCons Name [VPattern]
  deriving (Eq, Ord)

instance Show VPattern where
  show VAny = "_"
  show (VCons n []) = show n
  show (VCons n pats) = "(" ++ intercalate " " (show n : map show pats) ++ ")"

defaultVPats :: Int -> [VPattern]
defaultVPats n = replicate n VAny

iter :: [a] -> b -> (a -> b -> Either e b) -> Either e b
iter [] r _ = Right r
iter (x:xs) r f =
  case f x r of
    Right v -> iter xs v f
    other -> other

verifyData :: Env DataDecl -> Either String ()
verifyData datas = sequence_ $ map ver datas
  where
    ver (_, DataDecl { variants }) =
      sequence_ $ for variants $ \(_, types) ->
        sequence_ $ map (verifyTy datas) types

verifyTy :: Env DataDecl -> Type -> Either String ()
verifyTy datas = ver []
  where
    ver l (TApp a b) = ver [] b >> ver (b:l) a
    ver [_, _] TArrow = Right ()
    ver l TArrow = Left ("function type expects 2 type parameters, found " ++ show (length l))
    ver [] TUnit = Right ()
    ver l TUnit = genericMissing (show TUnit) (length l)
    ver [] TNat = Right ()
    ver l TNat = genericMissing (show TNat) (length l)
    ver [] TBool = Right ()
    ver l TBool = genericMissing (show TBool) (length l)
    ver l (TId name) =
      case lookup name datas of
        Nothing ->
          Left ("cannot find type named `" ++ show name ++ "`")
        Just DataDecl { typeParams }
          | len == expected -> Right ()
          | expected == 0 ->
            genericMissing (show name) len
          | len > expected ->
            Left (show name ++ " was given too many type parameters (expected " ++ show expected ++ ", found " ++ show len ++ ")")
          | len == 0 ->
            Left (show name ++ " wasn't given any type parameters (expected " ++ show expected ++ ")")
          | otherwise ->
            Left (show name ++ " wasn't given enough type parameters (expected " ++ show expected ++ ", found " ++ show len ++ ")")
          where
            len = length l
            expected = length typeParams
    ver _ _ = Right () -- currently difficult to verify type variables
    genericMissing name len =
      Left (name ++ " expects no type parameters, but was provided with " ++ show len)

verifyExpr :: Env DataDecl -> Typed Expr -> Either String ()
verifyExpr datas = ver
  where
    ver (expr ::: ty) = do
      verifyTy datas ty
      case expr of
        Val (Func _ expr) -> ver expr
        Op _ a b -> ver a >> ver b
        App a b -> ver a >> ver b
        If i t e -> ver i >> ver t >> ver e
        Let _ val expr -> ver val >> ver expr
        Match xs cases -> do
          sequence_ $ map ver xs
          let defs = defaultVPats $ length xs
          result <-
            iter cases [defs] $ \(pats, expr) vs -> do
              ver expr
              let vs' = concat $ map (go pats) vs
              if vs' == vs then
                Left ("unreachable pattern: " ++ intercalate " " (map show pats))
              else
                Right vs'
          if null result then
            Right ()
          else
            Left ("pattern match is missing cases:\n" ++ unlines (map (("  "++) . intercalate " " . map show) result))
        ICons _ _ xs -> sequence_ $ map ver xs
        _ -> Right ()
    enumerate :: Type -> [(Name, [VPattern])]
    enumerate (TApp a _) = enumerate a
    enumerate TNat = [(Name ["0"], []), (Name ["1 +"], [VAny])]
    enumerate TBool = [(Name ["false"], []), (Name ["true"], [])]
    enumerate (TId name) =
      let DataDecl {..} = lookup' name datas in
      for variants $ \
        (name, types) -> (name, defaultVPats $ length types)
    go :: [Typed Pattern] -> [VPattern] -> [[VPattern]]
    go [] [] = []
    go ((PAny _ ::: _) : ps) (v:vs) = map (v:) $ go ps vs
    go ((PNat 0 ::: t) : ps) vs = go (((PCons (Name ["0"]) []) ::: t) : ps) vs
    go ((PNat n ::: t) : ps) vs = go (((PCons (Name ["1 +"]) [PNat (n-1) ::: t]) ::: t) : ps) vs
    go ((PBool False ::: t) : ps) vs = go (((PCons (Name ["false"]) []) ::: t) : ps) vs
    go ((PBool True ::: t) : ps) vs = go (((PCons (Name ["true"]) []) ::: t) : ps) vs
    go ((PCons n xs ::: ty) : ps) (v:vs) =
      case v of
        VAny -> concat $ map try $ enumerate ty
        VCons name cs -> try (name, cs)
      where
        try :: (Name, [VPattern]) -> [[VPattern]]
        try (name, cs)
          | name == n =
            case (map (VCons name) $ go xs cs, go ps vs) of
              ([], r) -> map (VCons name cs :) r
              (c, []) -> map (: vs) c
              (c, r) -> (:) <$> c <*> r
          | otherwise = [VCons name cs : vs]
    go _ vs = [vs]
