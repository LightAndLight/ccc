module ExprC where

import Expr (Expr (..))

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
        -- left association
        (f', ComposeC g' h') -> optimise $ ComposeC (ComposeC f' g') h'
        -- beta reduction
        (AppC, PairC (AbsC body) g') -> optimise $ ComposeC body (PairC IdC g')
        (ComposeC x AppC, PairC (AbsC body) g') -> optimise $ ComposeC x (ComposeC body (PairC IdC g'))
        -- product fst beta
        (FstC, PairC a _) -> a
        (ComposeC g' FstC, PairC a _) -> optimise $ ComposeC g' a
        -- product snd beta
        (SndC, PairC _ b) -> b
        (ComposeC g' SndC, PairC _ b) -> optimise $ ComposeC g' b
        -- no more optimisations
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

fromExpr :: Expr -> ExprC
fromExpr = go []
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