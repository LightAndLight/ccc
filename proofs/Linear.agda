open import Data.Bool
open import Data.String
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality

_>>=_ : ∀{a x y : Set} → a ⊎ x → (x → a ⊎ y) → a ⊎ y
inl x >>= f = inl x
inr y >>= f = f y

data Ty : Set where
  I : Ty
  _⊗_ : Ty → Ty → Ty
  _⊸_ : Ty → Ty → Ty

eqTy : (a : Ty) → (b : Ty) → Maybe (a ≡ b)
eqTy I I = just refl
eqTy I (b ⊗ b₁) = nothing
eqTy I (b ⊸ b₁) = nothing
eqTy (a ⊗ a₁) I = nothing
eqTy (a ⊗ a₁) (b ⊗ b₁) with (eqTy a b)
... | just refl with (eqTy a₁ b₁)
... | just refl = just refl
... | nothing = nothing
eqTy (a ⊗ a₁) (b ⊗ b₁) | nothing = nothing
eqTy (a ⊗ a₁) (b ⊸ b₁) = nothing
eqTy (a ⊸ a₁) I = nothing
eqTy (a ⊸ a₁) (b ⊗ b₁) = nothing
eqTy (a ⊸ a₁) (b ⊸ b₁) with (eqTy a b)
... | just refl with (eqTy a₁ b₁)
... | just refl = just refl
... | nothing = nothing
eqTy (a ⊸ a₁) (b ⊸ b₁) | nothing = {!!}

data Arr : Ty → Ty → Set where
  id : ∀{a} → Arr a a
  _∘_ : ∀{a b c} → Arr b c → Arr a b → Arr a c
  abs : ∀{x a b} → Arr (x ⊗ a) b → Arr x (a ⊸ b)
  app : ∀{a b} → Arr ((a ⊸ b) ⊗ a) b
  ⟨_⊗_⟩ : ∀{a a' b b'} → Arr a a' → Arr b b' → Arr (a ⊗ b) (a' ⊗ b')
  swap : ∀{a b} → Arr (a ⊗ b) (b ⊗ a)
  assocl : ∀{a b c} → Arr (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c)
  assocr : ∀{a b c} → Arr ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))
  unitl : ∀{a} → Arr a (I ⊗ a)
  unitl⁻¹ : ∀{a} → Arr (I ⊗ a) a
  unitr : ∀{a} → Arr a (a ⊗ I)
  unitr⁻¹ : ∀{a} → Arr (a ⊗ I) a

infixl 20 _∘_

module Ctx where
  data Ctx : Ty → Set where
    ◆ : Ctx I
    _,_ : ∀{a b} → Ctx a → String → Ctx (a ⊗ b)

  infixl 20 _,_

  _∈_ : ∀{a} → String → Ctx a → Bool
  name ∈ ◆ = false
  name ∈ (ctx , name') = (name == name') ∨ (name ∈ ctx)

open Ctx using (Ctx; ◆; _,_)

data Expr : Ty → Set where
  Var : String → (a : Ty) → Expr a
  Lam : ∀{b} → String → (a : Ty) → Expr b → Expr (a ⊸ b)
  App : ∀{a b} → Expr (a ⊸ b) → Expr a → Expr b
  LetPair : ∀{r} → String → (a : Ty) → String → (b : Ty) → Expr (a ⊗ b) → Expr r → Expr r

data Error : Set where
  NotInScope : String → Error
  UnusedVariable : String → Error
  DuplicateUse : String → Error
  TypeMismatch : String → (a b : Ty) → Error

case_of_ : ∀{a b : Set} → a → (a → b) → b
case_of_ x f = f x

record Compiled (b : Ty) : Set where
  constructor MkCompiled
  field
    inTy : Ty
    env : Ctx inTy
    arr : Arr inTy b

record UsedIn (a x' : Ty) : Set where
  constructor MkUsedIn
  field
    x : Ty
    ctx : Ctx x
    arr : Arr (x ⊗ a) x'

usedIn : ∀{y} → String → (a : Ty) → Ctx y → Error ⊎ (UsedIn a y)
usedIn name a ◆ = inl (UnusedVariable name)
usedIn {y = x ⊗ y} name a (ctx , name') =
  if name == name'
  then (
    case eqTy a y of λ{
      nothing → inl (TypeMismatch name a y);
      (just refl) → inr (MkUsedIn _ ctx id)
    }
  )
  else do
    (MkUsedIn _ ctx' arr) ← usedIn name a ctx
    inr (MkUsedIn _ (ctx' , name') (⟨ arr ⊗ id ⟩ ∘ assocl ∘ ⟨ id ⊗ swap ⟩ ∘ assocr))

record Merge (a b : Ty) : Set where
  constructor MkMerge
  field
    x : Ty
    ctx : Ctx x
    arr : Arr x (a ⊗ b)

merge : ∀{a b} → Ctx a → Ctx b → Error ⊎ Merge a b
merge ctxl ◆ = inr (MkMerge _ ctxl unitr)
merge ctxl (ctxr , name) =
  if name Ctx.∈ ctxl
  then inl (DuplicateUse name)
  else do
    (MkMerge _ ctx arr) ← merge ctxl ctxr
    inr (MkMerge _ (ctx , name) (assocr ∘ ⟨ arr ⊗ id ⟩))

module Scope where
  data Scope : Set where
    ◆ : Scope
    _,_ : Scope → String → Scope

  _∈_ : String → Scope → Bool
  name ∈ ◆ = false
  name ∈ (scope , name') = (name == name') ∨ (name ∈ scope)

open Scope using (Scope; ◆; _,_)

compile : ∀{b} → Scope → Expr b → Error ⊎ Compiled b
compile scope (Var name ty) =
  if name Scope.∈ scope
  then inr (MkCompiled (I ⊗ ty) (◆ , name) unitl⁻¹)
  else inl (NotInScope name)
compile scope (Lam name ty expr) = do
  (MkCompiled y ctx body') ← compile (scope , name) expr
  (MkUsedIn _ ctx' reassoc) ← usedIn name ty ctx
  inr (MkCompiled _ ctx' (abs (body' ∘ reassoc)))
compile scope (App f x) = do
  (MkCompiled _ ctxl f') ← compile scope f
  (MkCompiled _ ctxr x') ← compile scope x
  (MkMerge _ ctx split) ← merge ctxl ctxr
  inr (MkCompiled _ ctx (app ∘ ⟨ f' ⊗ x' ⟩ ∘ split))
compile scope (LetPair lname a rname b value body) = do
  (MkCompiled _ valueCtx value') ← compile scope value
  (MkCompiled _ bodyCtx body') ← compile ((scope , lname) , rname) body
  (MkUsedIn _ bodyCtx' reassocr) ← usedIn rname b bodyCtx
  (MkUsedIn _ bodyCtx'' reassocl) ← usedIn lname a bodyCtx'
  (MkMerge _ ctx split) ← merge valueCtx bodyCtx''
  inr
    (MkCompiled
      _
      ctx
      (
        body' ∘
        reassocr ∘
        ⟨ (reassocl ∘ swap) ⊗ id ⟩ ∘
        assocl ∘
        ⟨ id ⊗ swap ⟩ ∘
        assocr ∘
        ⟨ value' ⊗ id ⟩ ∘
        split
      )
    )

test1 : ∀{a b} → Arr (a ⊗ b) (a ⊗ (I ⊗ b))
test1 =
  -- (a ⊗ (I ⊗ b))
  assocr ∘
  -- ((a ⊗ I) ⊗ b)
  ⟨ unitr ⊗ id ⟩
  -- (a ⊗ b)

test2 : ∀{a b} → Arr (a ⊗ b) (a ⊗ (I ⊗ b))
test2 =
  -- (a ⊗ (I ⊗ b))
  ⟨ id ⊗ unitl ⟩
  -- (a ⊗ b)

test3 :
  ∀{a a' b b' c c'} →
  Arr a a' →
  Arr b b' →
  Arr c c' →
  Arr (a ⊗ (b ⊗ c)) (a' ⊗ (b' ⊗ c'))
test3 f g h = assocr ∘ ⟨ ⟨ f ⊗ g ⟩ ⊗ h ⟩ ∘ assocl

test4 :
  ∀{a a' b b' c c'} →
  Arr a a' →
  Arr b b' →
  Arr c c' →
  Arr (a ⊗ (b ⊗ c)) (a' ⊗ (b' ⊗ c'))
test4 f g h = ⟨ f ⊗ ⟨ g ⊗ h ⟩ ⟩

test5 : ∀{a b} → Arr ((I ⊗ a) ⊗ b) (a ⊗ (I ⊗ b))
test5 = ⟨ unitl⁻¹ ⊗ unitl ⟩

optimise : ∀{a b} → Arr a b → Maybe (Arr a b)
optimise (unitl⁻¹ ∘ swap) = just unitr⁻¹
optimise (unitr⁻¹ ∘ swap) = just unitl⁻¹
optimise (assocr ∘ ⟨ unitr ⊗ id ⟩) = just ⟨ id ⊗ unitl ⟩
optimise (assocr ∘ ⟨ ⟨ f ⊗ g ⟩ ⊗ h ⟩ ∘ assocl) = just ⟨ f ⊗ ⟨ g ⊗ h ⟩ ⟩
optimise (x ∘ assocr ∘ ⟨ ⟨ f ⊗ g ⟩ ⊗ h ⟩ ∘ assocl) = just (x ∘ ⟨ f ⊗ ⟨ g ⊗ h ⟩ ⟩)
optimise _ = nothing
