{-# LANGUAGE OverloadedLists #-}

module Unrestricted where

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  | Int Int
  | Add Expr Expr
  | Mul Expr Expr
  | Pair Expr Expr
  | LetPair String String Expr Expr
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
  | TermC
  | DupC
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
    IntC i -> show i
    AddC -> "add"
    MulC -> "mul"
    TermC -> "term"
    DupC -> "dup"

data Error
  = NotInScope String
  deriving (Show)

usedIn :: String -> [String] -> Either Error (Bool, [String], ExprC)
usedIn _ [] =
  pure (False, [], ComposeC ForgetrC $ ParC IdC TermC)
usedIn name (name' : ctx) =
  if name == name'
    then pure (True, ctx, IdC)
    else do
      (used, ctx', arrow) <- usedIn name ctx
      pure
        ( used,
          name' : ctx',
          ComposeC (ParC arrow IdC)
            . ComposeC AssoclC
            . ComposeC (ParC IdC SwapC)
            $ AssocrC
        )

merge :: [String] -> [String] -> Either Error ([String], ExprC)
merge lctx [] = pure (lctx, UnforgetrC)
merge lctx (name : rctx) = do
  (used, lctx', reassocl) <- usedIn name lctx
  if used
    then do
      (ctx, split) <- merge lctx' rctx
      pure
        ( name : ctx,
          ComposeC AssocrC
            . ComposeC
              ( ParC
                  ( ComposeC (ParC reassocl IdC)
                      . ComposeC AssoclC
                      . ComposeC (ParC IdC SwapC)
                      $ AssocrC
                  )
                  IdC
              )
            . ComposeC AssoclC
            $ ParC split DupC
        )
    else do
      (ctx, split) <- merge lctx rctx
      pure (name : ctx, ComposeC AssocrC (ParC split IdC))

fromExpr :: Expr -> Either Error ExprC
fromExpr = fmap snd . go []
  where
    go :: [String] -> Expr -> Either Error ([String], ExprC)
    go names expr =
      case expr of
        Var name ->
          if name `elem` names
            then pure ([name], ForgetlC)
            else Left $ NotInScope name
        Lam name body -> do
          (ctx, body') <- go (name : names) body
          (_, ctx', reassoc) <- usedIn name ctx
          pure (ctx', AbsC $ ComposeC body' reassoc)
        App f x -> do
          (lctx, f') <- go names f
          (rctx, x') <- go names x
          (ctx, split) <- merge lctx rctx
          pure (ctx, ComposeC AppC $ ComposeC (ParC f' x') split)
        Int n -> pure ([], IntC n)
        Add a b -> do
          (lctx, a') <- go names a
          (rctx, b') <- go names b
          (ctx, split) <- merge lctx rctx
          pure (ctx, ComposeC AddC $ ComposeC (ParC a' b') split)
        Mul a b -> do
          (lctx, a') <- go names a
          (rctx, b') <- go names b
          (ctx, split) <- merge lctx rctx
          pure (ctx, ComposeC MulC $ ComposeC (ParC a' b') split)
        Pair a b -> do
          (lctx, a') <- go names a
          (rctx, b') <- go names b
          (ctx, split) <- merge lctx rctx
          pure (ctx, ComposeC (ParC a' b') split)
        LetPair lname rname value body -> do
          (valueCtx, value') <- go names value
          (bodyCtx, body') <- go (rname : lname : names) body
          (_, bodyCtx', reassocr) <- usedIn rname bodyCtx
          (_, bodyCtx'', reassocl) <- usedIn lname bodyCtx'
          (ctx, split) <- merge valueCtx bodyCtx''
          pure
            ( ctx,
              ComposeC body'
                . ComposeC reassocr
                . ComposeC (ParC (ComposeC reassocl SwapC) IdC)
                . ComposeC AssoclC
                . ComposeC (ParC IdC SwapC)
                . ComposeC AssocrC
                . ComposeC (ParC value' IdC)
                $ split
            )

optimise :: ExprC -> ExprC
optimise expr =
  case expr of
    IdC -> IdC
    ComposeC f g ->
      case (optimise f, optimise g) of
        (f', ComposeC g' h') ->
          optimise $ ComposeC (ComposeC f' g') h'
        (IdC, g') -> g'
        (f', IdC) -> f'
        (ParC a b, ParC a' b') ->
          optimise $ ParC (ComposeC a a') (ComposeC b b')
        (ComposeC f' (ParC a b), ParC a' b') ->
          optimise $ ComposeC f' (ParC (ComposeC a a') (ComposeC b b'))
        (SwapC, SwapC) -> IdC
        (UnforgetlC, ForgetlC) -> IdC
        (ForgetlC, UnforgetlC) -> IdC
        (UnforgetrC, ForgetrC) -> IdC
        (ForgetrC, UnforgetrC) -> IdC
        (ForgetlC, SwapC) -> ForgetrC
        (ForgetrC, SwapC) -> ForgetlC
        (AssocrC, ParC UnforgetrC IdC) ->
          optimise $ ParC IdC UnforgetlC
        (ComposeC AssocrC (ParC (ParC f' g') h'), AssoclC) ->
          optimise $ ParC f' (ParC g' h')
        (ComposeC (ComposeC x AssocrC) (ParC (ParC f' g') h'), AssoclC) ->
          optimise $ ComposeC x (ParC f' (ParC g' h'))
        (f', g') -> ComposeC f' g'
    ForgetlC -> ForgetlC
    ForgetrC -> ForgetrC
    UnforgetlC -> UnforgetlC
    UnforgetrC -> UnforgetrC
    AssoclC -> AssoclC
    AssocrC -> AssocrC
    SwapC -> SwapC
    ParC f g ->
      case (optimise f, optimise g) of
        (IdC, IdC) -> IdC
        (f', g') -> ParC f' g'
    AbsC body ->
      AbsC (optimise body)
    AppC -> AppC
    IntC n -> IntC n
    AddC -> AddC
    MulC -> MulC
    TermC -> TermC
    DupC -> DupC