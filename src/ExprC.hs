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

optimise :: ExprC -> ExprC
optimise expr =
  case expr of
    ComposeC f g ->
      case (optimise f, optimise g) of
        (IdC, g') -> g'
        (f', IdC) -> f'
        (f', g') -> ComposeC f' g'
    ProductC fs ->
      let fs' = optimise <$> fs
          prjs = PrjC <$> reverse [0 .. length fs - 1]
       in if fs' == prjs
            then IdC
            else case fs' of
              ComposeC g x : fs''
                | all (\f'' -> case f'' of ComposeC _ x' -> x == x'; _ -> False) fs' ->
                    optimise $ ComposeC (ProductC $ g : fmap (\(ComposeC g' _) -> g') fs'') x
              _ -> ProductC fs'
    AbsC body -> AbsC $ optimise body
    PrjC {} -> expr
    IntC {} -> expr
    IdC -> expr
    AppC -> expr
    AddC -> expr
    MulC -> expr
