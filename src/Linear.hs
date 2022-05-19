{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedLists #-}

module Linear where

import Control.Applicative ((<|>))
import Data.List (findIndex)
import Data.Semigroup (Semigroup (sconcat))
import Debug.Trace (traceShow)
import GHC.Stack (HasCallStack)

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
  deriving (Show)

(|>) :: Path -> Path -> Path
(|>) Here a = a
(|>) (L path) a = L (path |> a)
(|>) (R path) a = R (path |> a)

data Ctx = I | N String | Ctx :*: Ctx
  deriving (Eq, Show)

swapC :: HasCallStack => Path -> Path -> Ctx -> (ExprC, Ctx)
swapC Here Here ctx = (IdC, ctx)
swapC Here r _ = error $ "swapC: Here, " <> show r
swapC l Here _ = error $ "swapC: " <> show l <> ", Here"
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
rearrangeC a b = snd <$> go a (Here, b)
  where
    go :: HasCallStack => Ctx -> (Path, Ctx) -> Either RearrangeError (Ctx, ExprC)
    go I (path, I) =
      pure (I, IdC)
    go (N l) (path, I) =
      Left $ UnusedVariable l
    go (l :*: r) (path, I) = do
      (lctx, l') <- go l (path, I)
      (rctx, r') <- go r (path, I)
      pure (lctx :*: rctx, ComposeC ForgetlC (ParC l' r'))
    go from (toPath, N n) =
      case getPath n from of
        Nothing -> Left $ NotInScope n
        Just fromPath ->
          let !_ = traceShow (fromPath, toPath) ()
              (swapping, from') = swapC fromPath toPath from
           in pure (from', swapping)
    go from (path, l :*: r) = do
      (from', l') <- go from (path |> L Here, l)
      (from'', r') <- go from' (path |> R Here, r)
      pure (from'', ComposeC r' l')

fromExpr :: Expr -> ExprC
fromExpr = go I
  where
    contextOf :: Expr -> Ctx
    contextOf expr =
      case expr of
        Var name -> N name
        Lam _ body -> let ctx :*: N _ = contextOf body in ctx
        App f x -> contextOf f :*: contextOf x
        Pair a b -> contextOf a :*: contextOf b
        LetPair _ _ value body ->
          let ctx1 = contextOf value
              (ctx2 :*: N _) :*: N _ = contextOf body
           in ctx1 :*: ctx2
        With a b ->
          let actx = contextOf a
              bctx = contextOf b
           in if actx == bctx then actx else error $ show actx <> " is not " <> show bctx
        Fst a ->
          contextOf a
        Snd a ->
          contextOf a
        Int _ ->
          I
        Add a b ->
          contextOf a :*: contextOf b
        Mul a b ->
          contextOf a :*: contextOf b

    splitC ::
      Ctx ->
      -- X -> X_1 x X_2
      Expr ->
      Expr ->
      (Ctx, Ctx, ExprC)
    splitC ctx l r =
      let lctx = contextOf l
          rctx = contextOf r
          !_ = traceShow ("splitC", ctx, l, r) ()
       in case rearrangeC ctx (lctx :*: rctx) of
            Right ctx' -> (lctx, rctx, ctx')
            Left err -> error $ show err

    go ctx expr =
      case expr of
        Var name ->
          let !_ = traceShow ("var", ctx, name) ()
           in case rearrangeC ctx (N name) of
                Right rearrange -> rearrange
                Left err -> error $ show err
        Lam name body ->
          AbsC (go (ctx :*: N name) body)
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
          let I = ctx in IntC i
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
        (SwapC, SwapC) -> IdC
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