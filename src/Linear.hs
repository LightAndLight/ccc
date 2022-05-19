{-# LANGUAGE OverloadedLists #-}

module Linear where

import Control.Applicative ((<|>))
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
  | -- assocl : A x (B x C) -> (A x B) x C
    AssoclC
  | -- assocr : (A x B) x C -> A x (B x C)
    AssocrC
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
    AssoclC -> "assocl"
    AssocrC -> "assocr"
    PairC a b -> "pair(" <> showC a <> ", " <> showC b <> ")"
    FstC -> "fst"
    SndC -> "snd"
    IntC i -> show i
    AddC -> "add"
    MulC -> "mul"

data Ctx
  = I
  | N String
  | Ctx :* Ctx
  deriving (Eq, Show)

data RearrangeError
  = NotInScope String
  | UnusedVariable String
  deriving (Show)

fromExpr :: Expr -> ExprC
fromExpr = go I
  where
    contextOf :: Expr -> Ctx
    contextOf expr =
      case expr of
        Var name -> N name
        Lam _ body -> let ctx :* N _ = contextOf body in ctx
        App f x -> contextOf f :* contextOf x
        Pair a b -> contextOf a :* contextOf b
        LetPair _ _ value body ->
          let ctx1 = contextOf value
              (ctx2 :* N _) :* N _ = contextOf body
           in ctx1 :* ctx2
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
          contextOf a :* contextOf b
        Mul a b ->
          contextOf a :* contextOf b

    rearrangeC :: Ctx -> Ctx -> Either RearrangeError ExprC
    rearrangeC I I =
      pure IdC
    rearrangeC I (N name) =
      Left $ NotInScope name
    rearrangeC I (l :* r) =
      -- A x B <- I
      ComposeC
        <$>
        -- A x B <- I x I
        ( ParC
            <$>
            -- A <- I
            (rearrangeC I l)
            <*>
            -- B <- I
            (rearrangeC I r)
        )
        <*>
        -- I x I <- I
        pure UnforgetlC
    rearrangeC (N name) I =
      Left $ UnusedVariable name
    rearrangeC (N name) (N name') =
      if name == name'
        then pure IdC
        else Left $ NotInScope name'
    rearrangeC (N name) (l :* r) =
      -- A x B <- X
      ComposeC
        -- A x B <- I x X
        <$> rearrangeC (I :* N name) (l :* r)
        -- I x X <- X
        <*> pure UnforgetlC
    rearrangeC (l :* r) I =
      -- I <- A x B
      ComposeC
        <$>
        -- I <- I x I
        pure ForgetlC
        <*>
        -- I x I <- A x B
        ( ParC
            <$>
            -- I <- A
            (rearrangeC l I)
            <*>
            -- I <- B
            (rearrangeC r I)
        )
    rearrangeC (l :* r) (N name) =
      -- X <- A x B
      ComposeC
        -- X <- I x X
        <$> pure ForgetlC
        -- I x X <- A x B
        <*> rearrangeC (l :* r) (I :* N name)
    rearrangeC (l :* (m :* r)) ((l' :* m') :* r') =
      -- (A' x B') x C' <- A x (B x C)
      ComposeC
        -- (A' x B') x C' <- A x (B x C)
        <$> rearrangeC ((l :* m) :* r) ((l' :* m') :* r')
        -- (A x B) x C <- A x (B x C)
        <*> pure AssoclC
    rearrangeC ((l :* m) :* r) (l' :* (m' :* r')) =
      -- A' x (B' x C') <- (A x B) x C
      ComposeC
        <$> rearrangeC (l :* (m :* r)) (l' :* (m' :* r'))
        -- A x (B x C) <- (A x B) x C
        <*> pure AssocrC
    rearrangeC (l :* r) (l' :* r') =
      -- A' x B' <- A x B
      sconcat
        [ -- A' x B' <- A x B
          ParC
            -- A' <- A
            <$> rearrangeC l l'
              -- B' <- B
              <*> rearrangeC r r',
          ComposeC
            -- A' x B' <- B x A
            <$> ( ParC
                    -- A' <- B
                    <$> rearrangeC r l'
                      -- B' <- A
                      <*> rearrangeC l r'
                )
            -- B x A <- A x B
            <*> pure SwapC
        ]

    splitC ::
      Ctx ->
      -- X -> X_1 x X_2
      Expr ->
      Expr ->
      (Ctx, Ctx, ExprC)
    splitC ctx l r =
      let lctx = contextOf l
          rctx = contextOf r
       in case rearrangeC ctx (lctx :* rctx) of
            Right ctx' -> (lctx, rctx, ctx')
            Left err -> error $ show err

    reduceC :: String -> Ctx -> (Ctx, ExprC)
    reduceC name ctx =
      case ctx of
        N name' -> (N name', IdC)
        I -> (I, IdC)
        l :* r ->
          let (lctx, l') = reduceC name l
              (rctx, r') = reduceC name r
              h = ParC l' r'
              f x =
                case lctx of
                  I -> ComposeC ForgetlC x
                  _ -> x
              g x =
                case rctx of
                  I -> ComposeC ForgetrC x
                  _ -> x
              ctx' =
                case (lctx, rctx) of
                  (I, _) -> rctx
                  (_, I) -> lctx
                  _ -> error $ "ctx' isn't singleton: " <> show ctx
           in (ctx', f (g h))

    go ctx expr =
      case expr of
        Var name ->
          case rearrangeC ctx (N name) of
            Right rearrange -> rearrange
            Left err -> error $ show err
        {-

        let (N _, reduce) = reduceC name ctx
         in reduce
              -}
        Lam name body ->
          AbsC (go (ctx :* N name) body)
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
    AssoclC -> expr
    AssocrC -> expr
    SwapC -> expr