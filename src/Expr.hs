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
  | Prj Expr Int
  deriving (Eq, Show)

toC :: Expr -> ExprC
toC = go []
  where
    lookupC :: String -> [String] -> Int
    lookupC name names =
      case names of
        [] -> undefined
        name' : rest ->
          if name == name'
            then length rest
            else lookupC name rest

    go :: [String] -> Expr -> ExprC
    go names expr =
      case expr of
        Var name -> PrjC $ lookupC name names
        Lam name body -> AbsC $ go (names <> [name]) body
        App f x -> ComposeC AppC $ ProductC [go names f, go names x]
        Pair a b -> ProductC [go names a, go names b]
        Prj a ix -> ComposeC (PrjC ix) (go names a)
        Int i -> IntC i
        Add a b -> ComposeC AddC $ ProductC [go names a, go names b]
        Mul a b -> ComposeC MulC $ ProductC [go names a, go names b]