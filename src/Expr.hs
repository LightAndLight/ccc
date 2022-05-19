module Expr where

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