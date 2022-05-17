module ExprC where

data ExprC
  = IdC
  | ComposeC ExprC ExprC
  | TermC
  | PairC ExprC ExprC
  | FstC
  | SndC
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
    TermC -> "term"
    PairC a b ->
      "pair("
        <> showC a
        <> ", "
        <> showC b
        <> ")"
    FstC ->
      "fst"
    SndC ->
      "snd"
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
    PairC a b ->
      case (optimise a, optimise b) of
        (FstC, SndC) -> IdC
        (ComposeC a' x, ComposeC b' x')
          | x == x' ->
              optimise $ ComposeC (PairC a' b') x
        (a', b') -> PairC a' b'
    AbsC body -> AbsC $ optimise body
    TermC -> expr
    FstC -> expr
    SndC -> expr
    IntC {} -> expr
    IdC -> expr
    AppC -> expr
    AddC -> expr
    MulC -> expr