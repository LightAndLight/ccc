module ExprC where

import Data.List (intercalate)

data ExprC
  = IdC
  | ComposeC ExprC ExprC
  | ProductC [ExprC]
  | PrjC Int
  | AbsC ExprC
  | AppC
  | IntC Int
  | AddC
  | MulC
  deriving (Eq, Show)

showC :: ExprC -> String
showC expr =
  case expr of
    IdC -> "id"
    ComposeC f g ->
      showC g <> " > " <> showC f
    ProductC ps ->
      "pair("
        <> intercalate ", " (showC <$> ps)
        <> ")"
    PrjC i ->
      "prj[" <> show i <> "]"
    AbsC body ->
      "abs(" <> showC body <> ")"
    AppC -> "app"
    IntC i -> show i
    AddC -> "add"
    MulC -> "mul"
