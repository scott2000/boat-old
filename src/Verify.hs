{-# LANGUAGE RecordWildCards #-}
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

verifyExpr :: Env DataDecl -> Typed Expr -> Either String ()
verifyExpr datas = ver
  where
    ver (expr ::: _) =
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
