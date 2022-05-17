module Expr where

import ExprC

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  | Int Int
  | Add Expr Expr
  | Mul Expr Expr
  | Pair Expr Expr
  | Fst Expr
  | Snd Expr
  deriving (Eq, Show)

toC :: Expr -> ExprC
toC = go []
  where
    lookupC :: String -> [String] -> ExprC
    lookupC name names =
      case names of
        [] -> undefined
        name' : rest ->
          if name == name'
            then SndC
            else ComposeC (lookupC name rest) FstC

    go :: [String] -> Expr -> ExprC
    go names expr =
      case expr of
        Var name -> lookupC name names
        Lam name body -> AbsC $ go (name : names) body
        App f x -> ComposeC AppC $ PairC (go names f) (go names x)
        Pair a b -> PairC (go names a) (go names b)
        Fst a -> ComposeC FstC (go names a)
        Snd a -> ComposeC SndC (go names a)
        Int i -> IntC i
        Add a b -> ComposeC AddC $ PairC (go names a) (go names b)
        Mul a b -> ComposeC MulC $ PairC (go names a) (go names b)