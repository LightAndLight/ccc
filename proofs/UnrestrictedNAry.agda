module UnrestrictedNAry where

open import Data.Nat using (ℕ; suc)

module Bwd where
  data Bwd (a : Set) : Set where
    ◆ : Bwd a
    _,_ : Bwd a → a → Bwd a

  open import Data.String using (String; _==_)
  open import Data.Bool using (Bool; false; true; _∨_)

  _∈_ : String → Bwd String → Bool
  a ∈ ◆ = false
  a ∈ (as , a') = (a == a') ∨ (a ∈ as)

module Ty where
  data Ty : Set where
    _⊗_ : Ty → Ty → Ty
    I : Ty
    _⊸_ : Ty → Ty → Ty

  infixr 25 _⊸_
  infixl 30 _⊗_

  infix 4 _≟_

  open import Relation.Nullary using (Dec)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Data.Bool using (true; false)
  open import Data.Product using (_×_; _,_)

  ⊗-eq : ∀{a b a' b'} → (a ⊗ b) ≡ (a' ⊗ b') → (a ≡ a') × (b ≡ b')
  ⊗-eq _≡_.refl = _≡_.refl , _≡_.refl

  ⊸-eq : ∀{a b a' b'} → (a ⊸ b) ≡ (a' ⊸ b') → (a ≡ a') × (b ≡ b')
  ⊸-eq _≡_.refl = _≡_.refl , _≡_.refl

  _≟_ : (a b : Ty) → Dec (a ≡ b)
  a ⊗ b ≟ a' ⊗ b' with (a ≟ a')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = false Relation.Nullary.because
                                                                   Relation.Nullary.ofⁿ λ z → ¬p (Data.Product.proj₁ (⊗-eq z))
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl with (b ≟ b')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = false Relation.Nullary.because Relation.Nullary.ofⁿ λ z → ¬p (Data.Product.proj₂ (⊗-eq z))
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl = true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl
  a ⊗ b ≟ I = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  a ⊗ b ≟ c ⊸ c₁ = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  I ≟ a ⊗ a₁ = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  I ≟ I = true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl
  I ≟ a ⊸ a₁ = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  a ⊸ b ≟ c ⊗ c₁ = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  a ⊸ b ≟ I = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  a ⊸ b ≟ a' ⊸ b' with (a ≟ a')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = false Relation.Nullary.because
                                                                   Relation.Nullary.ofⁿ (λ z → ¬p (Data.Product.proj₁ (⊸-eq z)))
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl with (b ≟ b')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = false Relation.Nullary.because
                                                                   Relation.Nullary.ofⁿ (λ z → ¬p (Data.Product.proj₂ (⊸-eq z)))
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl = true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl

module Ctx where
  open Ty using (Ty)
  open import Data.Product using (_×_)
  open import Data.String using (String)

  data Ctx : ℕ → Set where
    ◆ : Ctx 0
    _,_ : ∀{n} → Ctx n → String × Ty → Ctx (suc n)

  infixl 20 _,_

  [_] : String × Ty → Ctx 1
  [ a ] = ◆ , a

  data Index : ∀{n} → Ctx n → Set where
    zero : ∀{n} {as : Ctx n} {a} → Index (as , a)
    suc : ∀{n} {as : Ctx n} {a} → Index as → Index (as , a)

  open import Data.Nat using (_+_)

  delete : ∀{n} → (ctx : Ctx (1 + n)) → Index ctx → Ctx n
  delete (ctx , ty) zero = ctx
  delete (ctx , ty) (suc ix) with ctx
  ... | ctx' , ty' = delete (ctx' , ty') ix , ty

  dup : ∀{n} → (ctx : Ctx n) → Index ctx → Ctx (1 + n)
  dup (ctx , ty) zero = ctx , ty , ty
  dup (ctx , ty) (suc ix) = dup ctx ix , ty

  swapZero : ∀{n} → (ctx : Ctx n) → Index ctx → Ctx n
  swapZero (ctx , item) zero = ctx , item
  swapZero (ctx , item) (suc ix) with (swapZero ctx ix)
  ... | ctx' , item' = ctx' , item , item'

  swap : ∀{n} → (ctx : Ctx n) → Index ctx → Index ctx → Ctx n
  swap (ctx , item) zero to = swapZero (ctx , item) to
  swap (ctx , item) (suc from) zero = swapZero (ctx , item) (suc from)
  swap (ctx , item) (suc from) (suc to) = swap ctx from to , item

  _++_ : ∀{m n} → Ctx m → Ctx n → Ctx (m + n)
  _++_ = {!!}

module Arr where
  open import Data.Product using (_×_) renaming (_,_ to pair)
  open import Data.String using (String)
  open Ctx using (Ctx; [_]; ◆; _,_)
  open Ty using (Ty; _⊸_)
  open Bwd using (Bwd)

  size : Ty → ℕ
  size (a Ty.⊗ _) = suc (size a)
  size Ty.I = 0
  size (ty ⊸ ty₁) = 1

  toCtx : (ty : Ty) → Ctx (size ty)
  toCtx (a Ty.⊗ b) =  toCtx a , pair {!!} b
  toCtx Ty.I = ◆
  toCtx (a ⊸ b) = [ pair {!!} (a ⊸ b) ]

  fromCtx : ∀{n} → Ctx n → Ty
  fromCtx ◆ = Ty.I
  fromCtx (ctx , pair _ ty) = (fromCtx ctx) Ty.⊗ ty

  data Arr : ∀{m n} → Ctx m → Ctx n → Set where
    id : ∀{n} {a : Ctx n} → Arr a a
    _∘_ : ∀{m n o} {a : Ctx m} {b : Ctx n} {c : Ctx o} → Arr b c → Arr a b → Arr a c

    _∥_ : ∀{m n} {a : Ctx m} {a' : Ctx n} {b b'} → Arr a a' → Arr [ b ] [ b' ] → Arr (a , b) (a' , b')

    abs : ∀{n} {ctx : Ctx n} {a b} {name name' name''} → Arr (ctx , (pair name a)) [ (pair name' b) ] → Arr ctx [ pair name'' (a ⊸ b) ]
    app : ∀{a b} {name name' name''} → Arr ( ◆ , pair name (a ⊸ b) , pair name' a ) [ pair name'' b ]

    unitr : ∀{n} {x : Ctx n} → (name : String) → Arr x (x , pair name Ty.I)
    pack :
      ∀{n} {x : Ctx n} {a b} {namea nameb} →
      (name : String) →
      Arr (x , pair namea a , pair nameb b) (x , pair name (a Ty.⊗ b))
    unpack : ∀{name} {n} {ctx : Ctx n} → Arr [ pair name (fromCtx ctx) ] ctx

    swap : ∀{n} {ctx : Ctx n} → (from : Ctx.Index ctx) → (to : Ctx.Index ctx) → Arr ctx (Ctx.swap ctx from to)

    drop : ∀{n} {ctx : Ctx (suc n)} → (ix : Ctx.Index ctx) → Arr ctx (Ctx.delete ctx ix)
    dup : ∀{n} {ctx : Ctx n} → (ix : Ctx.Index ctx) → Arr ctx (Ctx.dup ctx ix)

  infixl 20 _∘_
  infixl 20 _∥_

module Expr where
  open import Data.String using (String)
  open Ty using (Ty; _⊸_)

  data Expr : Ty → Set where
    Var : String → (a : Ty) → Expr a
    Lam : ∀{b} → String → (a : Ty) → Expr b → Expr (a ⊸ b)
    App : ∀{a b} → Expr (a ⊸ b) → Expr a → Expr b

module Either where
  data Either (a b : Set) : Set where
    left : a → Either a b
    right : b → Either a b

  _>>=_ : ∀{e a b} → Either e a → (a → Either e b) → Either e b
  left e >>= f = left e
  right a >>= f = f a

  infix 20 _>>=_

module UsedIn where
  open Arr
  open Ctx using (Ctx; ◆; _,_)
  open Ty using (Ty)
  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Product using () renaming (_,_ to pair)
  open import Data.String using (String; _≟_)
  import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (refl)

  record UsedIn {n} (name : String) (a : Ty) (ctx : Ctx n) : Set where
    constructor MkUsedIn
    field
      used : Bool
      {n'} : ℕ
      ctx' : Ctx n'
      arrow : Arr (ctx' , pair name a) ctx

  usedIn : ∀{n} → (name : String) → (a : Ty) → (ctx : Ctx n) → UsedIn name a ctx
  usedIn name a ◆ = MkUsedIn false ◆ (drop Ctx.Index.zero)
  usedIn name a (ctx , pair name' a') with (name ≟ name')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬name≡name =
    let (MkUsedIn used ctx' arrow) = usedIn name a ctx in
    MkUsedIn
      used
      (ctx' , pair name' a')
      ((arrow ∥ id) ∘ swap (Ctx.Index.suc Ctx.Index.zero) Ctx.Index.zero)
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ refl with (a Ty.≟ a')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬a≡a =
    let (MkUsedIn used ctx' arrow) = usedIn name a ctx in
    MkUsedIn
      used
      (ctx' , pair name' a')
      ((arrow ∥ id) ∘ swap (Ctx.Index.suc Ctx.Index.zero) Ctx.Index.zero)
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ refl = MkUsedIn true ctx id

module Merge where
  open Ctx using (Ctx; _,_)
  open Arr
  open import Data.Product using () renaming (_,_ to pair)
  open import Data.Bool using (if_then_else_)

  record Merge {m n} (ctxl : Ctx m) (ctxr : Ctx n) : Set where
    constructor MkMerge
    field
      {n'} : ℕ
      ctx : Ctx n'
      arrow : Arr ctx (ctxl , pair {!!} (fromCtx ctxr))

  merge : ∀{m n} → (ctxl : Ctx m) → (ctxr : Ctx n) → Merge ctxl ctxr
  merge ctxl Ctx.◆ = MkMerge ctxl (unitr {!!})
  merge ctxl (ctxr , pair name ty) = 
    let (UsedIn.MkUsedIn used ctxl' reassoc) = UsedIn.usedIn name ty ctxl in
    if used
    then (
      let (MkMerge ctx arrow) = merge ctxl' ctxr in
      MkMerge
        (ctx , pair name ty)
        ( reassoc ∥ id ∘
          -- lctx , a, Tensor (rctx , a)
          swap (Ctx.Index.zero) (Ctx.Index.suc Ctx.Index.zero) ∘
          -- lctx , Tensor (rctx , a) , a
          (pack {!!} ∥ id) ∘
          -- lctx , Tensor rctx , a , a
          dup Ctx.Index.zero ∘
          -- lctx , Tensor rctx , a
          (arrow ∥ id)
          -- x , a
        )
    )
    else
      let (MkMerge ctx arrow) = merge ctxl ctxr in
      MkMerge
        (ctx , pair name ty)
        (pack {!!} ∘ (arrow ∥ id))

open Ty using (Ty)
open Ctx using (Ctx; [_])
open Arr
open import Data.Product using () renaming (_,′_ to pair)
open import Data.String using (String)

record FromExpr (a : Ty) : Set where
  constructor MkFromExpr
  field
    {n} : ℕ
    ctx : Ctx n
    name : String
    arrow : Arr ctx [ pair name a ]

open import Data.String using (String)
open import Data.Bool using (if_then_else_)

data Error : Set where
  NotInScope : String → Error

open Bwd using (Bwd; _,_)
open Expr using (Expr)
open Either using (Either; left; right; _>>=_)

fromExpr : ∀{b} → Bwd String → Expr b → Either Error (FromExpr b)
fromExpr scope (Expr.Var name a) =
  if name Bwd.∈ scope
  then right (MkFromExpr [ pair name a ] name id)
  else left (NotInScope name)
fromExpr scope (Expr.Lam name a body) = do
  (MkFromExpr ctx name body') ← fromExpr (scope , name) body
  let (UsedIn.MkUsedIn used ctx' reassoc) = UsedIn.usedIn name a ctx
  right (MkFromExpr ctx' {!!} (abs (body' ∘ reassoc)))
fromExpr scope (Expr.App f x) = do
  (MkFromExpr fctx fname f') <- fromExpr scope f
  (MkFromExpr xctx xname x') <- fromExpr scope x
  let (Merge.MkMerge ctx split) = Merge.merge fctx xctx
  right (MkFromExpr ctx {!!} (app ∘ (f' ∥ (x' ∘ unpack)) ∘ split))
