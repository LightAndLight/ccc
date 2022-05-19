{-# LANGUAGE OverloadedLists #-}

module Linear where

import Control.Applicative ((<|>))
import Data.List (findIndex)
import Data.Semigroup (Semigroup (sconcat))

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  | Int Int
  | Add Expr Expr
  | Mul Expr Expr
  | Pair Expr Expr
  | LetPair String String Expr Expr
  | With Expr Expr
  | Fst Expr
  | Snd Expr
  deriving (Eq, Show)

data ExprC
  = IdC
  | ComposeC ExprC ExprC
  | -- forgetl : I x A -> A
    ForgetlC
  | -- forgetr : A x I -> A
    ForgetrC
  | -- unforgetl : A -> I x A
    UnforgetlC
  | -- unforgetr : A -> A x I
    UnforgetrC
  | -- swap : A x B -> B x A
    SwapC
  | {-
    f : A -> A'
    g : B -> B'
    ---------------------------
    par(f, g) : A x B -> A' x B'
    -}
    ParC ExprC ExprC
  | {-
    f : X x A -> B
    --------------------------
    abs(f) : X -> A => B
    -}
    AbsC ExprC
  | -- app : (A => B) x A -> B
    AppC
  | IntC Int
  | AddC
  | MulC
  | {-
    f : X -> A
    g : X -> B
    -----------------
    pair(f, g) : X -> A & B
    -}
    PairC ExprC ExprC
  | -- fst : A & B -> A
    FstC
  | -- snd : A & B -> A
    SndC
  | AssoclC
  | AssocrC
  deriving (Eq, Show)

showC :: ExprC -> String
showC expr =
  case expr of
    IdC -> "id"
    ComposeC f g ->
      showC g <> " > " <> showC f
    ParC a b ->
      "par("
        <> showC a
        <> ", "
        <> showC b
        <> ")"
    AbsC body ->
      "abs(" <> showC body <> ")"
    AppC -> "app"
    ForgetlC -> "forgetl"
    UnforgetlC -> "unforgetl"
    ForgetrC -> "forgetr"
    UnforgetrC -> "unforgetr"
    SwapC -> "swap"
    PairC a b -> "pair(" <> showC a <> ", " <> showC b <> ")"
    FstC -> "fst"
    SndC -> "snd"
    IntC i -> show i
    AddC -> "add"
    MulC -> "mul"

data RearrangeError
  = NotInScope String
  | UnusedVariable String
  deriving (Show)

data Path = Here | L Path | R Path

data Ctx = I | N String | Ctx :*: Ctx

swapC :: Path -> Path -> Ctx -> (ExprC, Ctx)
swapC Here Here ctx = (IdC, ctx)
swapC Here _ _ = error "here"
swapC _ Here _ = error "here"
swapC (L path) (L path') ctx =
  let l :*: r = ctx
      (swapping, l') = swapC path path' l
   in (ParC swapping IdC, l' :*: r)
swapC (L Here) (R Here) ctx =
  let l :*: r = ctx in (SwapC, r :*: l)
swapC (L Here) (R (L path')) ctx =
  let l :*: (m :*: r) = ctx
      (swapping, l' :*: m') = swapC (L Here) (R path') (l :*: m)
   in ( ComposeC AssocrC $ ComposeC (ParC swapping IdC) AssoclC,
        l' :*: (m' :*: r)
      )
swapC (L Here) (R (R path')) ctx =
  let l :*: (m :*: r) = ctx
      (swapping, l' :*: r') = swapC (L Here) (R path') (l :*: r)
   in (ComposeC SwapC $ ComposeC AssocrC $ ComposeC (ParC swapping IdC) $ ComposeC AssoclC SwapC, l' :*: (m :*: r'))
swapC (L (L path)) (R path') ctx =
  let (l :*: m) :*: r = ctx
      (swapping, l' :*: r') = swapC (L path) (R path') (l :*: r)
   in (ComposeC SwapC $ ComposeC AssoclC $ ComposeC (ParC IdC swapping) $ ComposeC AssocrC SwapC, (l' :*: m) :*: r')
swapC (L (R path)) (R path') ctx =
  let (l :*: m) :*: r = ctx
      (swapping, m' :*: r') = swapC (L path) (R path') (m :*: r)
   in (ComposeC AssoclC $ ComposeC (ParC IdC swapping) AssocrC, (l :*: m') :*: r')
swapC (R path) (L path') ctx =
  let l :*: r = ctx
      (swapping, r' :*: l') = swapC (L path') (R path) (r :*: l)
   in (ComposeC SwapC (ComposeC swapping SwapC), l' :*: r')
swapC (R path) (R path') ctx =
  let l :*: r = ctx
      (swapping, r') = swapC path path' r
   in (ParC IdC swapping, l :*: r')

getPath :: String -> Ctx -> Maybe Path
getPath name I =
  Nothing
getPath name (N n) =
  if name == n then Just Here else Nothing
getPath name (l :*: r) =
  (L <$> getPath name l) <|> (R <$> getPath name r)

rearrangeC :: Ctx -> Ctx -> Either RearrangeError ExprC
rearrangeC a b = go a (Here, b)
  where
    go I (path, I) =
      pure IdC
    go (N l) (path, I) =
      Left $ UnusedVariable l
    go (l :*: r) (path, I) = do
      l' <- go l (path, I)
      r' <- go r (path, I)
      pure $ ComposeC ForgetlC (ParC l' r')
    go from (toPath, N n) =
      case getPath n from of
        Nothing -> Left $ NotInScope n
        Just fromPath ->
          let (swapping, from') = swapC fromPath toPath from
           in pure swapping
    go from (path, l :*: r) = _

{-

rearrangeC _ I I = Right IdC
rearrangeC _ (N l) I = Left $ UnusedVariable l
rearrangeC path items (N l) =
  case findPath l items of
    Nothing -> Left $ NotInScope l
    Just ix ->
      let (swapping, l' : items') = swapC 0 ix items
       in if ix /= 0 && l /= l'
            then error $ "ix : " <> show ix <> ", items: " <> show items
            else
              ComposeC
                <$> (ParC <$> pure IdC <*> rearrangeC items' rs)
                <*> pure swapping
-}

fromExpr :: Expr -> ExprC
fromExpr = go []
  where
    contextOf :: Expr -> Ctx
    contextOf expr =
      case expr of
        Var name -> [name]
        Lam _ body -> let ctx = init $ contextOf body in ctx
        App f x -> contextOf f <> contextOf x
        Pair a b -> contextOf a <> contextOf b
        LetPair _ _ value body ->
          let ctx1 = contextOf value
              ctx2 = init $ init $ contextOf body
           in ctx1 <> ctx2
        With a b ->
          let actx = contextOf a
              bctx = contextOf b
           in if actx == bctx then actx else error $ show actx <> " is not " <> show bctx
        Fst a ->
          contextOf a
        Snd a ->
          contextOf a
        Int _ ->
          []
        Add a b ->
          contextOf a <> contextOf b
        Mul a b ->
          contextOf a <> contextOf b

    splitC ::
      Ctx ->
      -- X -> X_1 x X_2
      Expr ->
      Expr ->
      (Ctx, Ctx, ExprC)
    splitC ctx l r =
      let lctx = contextOf l
          rctx = contextOf r
       in case rearrangeC ctx (lctx <> rctx) of
            Right ctx' -> (lctx, rctx, ctx')
            Left err -> error $ show err

    go ctx expr =
      case expr of
        Var name ->
          case rearrangeC ctx [name] of
            Right rearrange -> rearrange
            Left err -> error $ show err
        Lam name body ->
          AbsC (go (ctx <> [name]) body)
        App f x ->
          let (ctx1, ctx2, split) = splitC ctx f x
           in ComposeC AppC $ ComposeC (ParC (go ctx1 f) (go ctx2 x)) split
        Pair a b ->
          let (ctx1, ctx2, split) = splitC ctx a b
           in ComposeC (ParC (go ctx1 a) (go ctx2 b)) split
        LetPair lname rname value body ->
          undefined
        With a b ->
          PairC (go ctx a) (go ctx b)
        Fst a ->
          ComposeC FstC (go ctx a)
        Snd a ->
          ComposeC SndC (go ctx a)
        Int i ->
          let [] = ctx in IntC i
        Add a b ->
          let (ctx1, ctx2, split) = splitC ctx a b
           in ComposeC AddC $ ComposeC (ParC (go ctx1 a) (go ctx2 b)) split
        Mul a b ->
          let (ctx1, ctx2, split) = splitC ctx a b
           in ComposeC MulC $ ComposeC (ParC (go ctx1 a) (go ctx2 b)) split

optimise :: ExprC -> ExprC
optimise expr =
  case expr of
    ComposeC f g ->
      case (optimise f, optimise g) of
        (IdC, g') -> g'
        (f', IdC) -> f'
        -- left association
        (f', ComposeC g' h') -> optimise $ ComposeC (ComposeC f' g') h'
        -- no more optimisations
        (f', g') -> ComposeC f' g'
    ParC a b ->
      case (optimise a, optimise b) of
        (IdC, IdC) -> IdC
        (a', b') -> ParC a' b'
    PairC a b ->
      case (optimise a, optimise b) of
        (a', b') -> PairC a' b'
    AbsC body -> AbsC $ optimise body
    FstC -> expr
    SndC -> expr
    IntC {} -> expr
    IdC -> expr
    AppC -> expr
    AddC -> expr
    MulC -> expr
    ForgetlC -> expr
    ForgetrC -> expr
    UnforgetlC -> expr
    UnforgetrC -> expr
    SwapC -> expr