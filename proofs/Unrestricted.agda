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
eqTy (a ⊸ a₁) (b ⊸ b₁) | nothing = nothing

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
  term : ∀{a} → Arr a I
  dup : ∀{a} → Arr a (a ⊗ a)

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

open import Data.Product using (_×_)

usedIn : ∀{y} → String → (a : Ty) → Ctx y → Error ⊎ (Bool × UsedIn a y)
usedIn name a ◆ =
  -- this is what changes when we upgrade from linear to affine.
  -- instead of throwing an error when we need to turn a singleton context into an empty context,
  -- we zero out the element of the singleton context using `term`
  inr (false Data.Product., MkUsedIn _ ◆ (unitr⁻¹ ∘ ⟨ id ⊗ term ⟩))
usedIn {y = x ⊗ y} name a (ctx , name') =
  if name == name'
  then (
    case eqTy a y of λ{
      nothing → inl (TypeMismatch name a y);
      (just refl) → inr (true Data.Product., MkUsedIn _ ctx id)
    }
  )
  else do
    (used Data.Product., MkUsedIn _ ctx' arr) ← usedIn name a ctx
    inr (used Data.Product., MkUsedIn _ (ctx' , name') (⟨ arr ⊗ id ⟩ ∘ assocl ∘ ⟨ id ⊗ swap ⟩ ∘ assocr))

record Merge (a b : Ty) : Set where
  constructor MkMerge
  field
    x : Ty
    ctx : Ctx x
    arr : Arr x (a ⊗ b)

merge : ∀{a b} → Ctx a → Ctx b → Error ⊎ Merge a b
merge ctxl ◆ = inr (MkMerge _ ctxl unitr)
merge {a} {b = x ⊗ y} ctxl (ctxr , name) = do
  (used Data.Product., res) ← usedIn name y ctxl
  if used
    then (do
      -- upgrading linear to unrestricted.
      -- instead of throwing an error when we find a duplicate use,
      -- duplicate the argument and "send" it down to the left side
      let (MkUsedIn _ ctxl' arrl) = res
      (MkMerge _ ctx arr) ← merge ctxl' ctxr
      inr
        (MkMerge
          _
          (ctx , name)
          (
            assocr ∘
            ⟨ ⟨ arrl ⊗ id ⟩ ∘ assocl ∘ ⟨ id ⊗ swap ⟩ ∘ assocr ⊗ id ⟩ ∘
            assocl ∘
            ⟨ arr ⊗ dup ⟩
          )))
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
  (_ Data.Product., MkUsedIn _ ctx' reassoc) ← usedIn name ty ctx
  inr (MkCompiled _ ctx' (abs (body' ∘ reassoc)))
compile scope (App f x) = do
  (MkCompiled _ ctxl f') ← compile scope f
  (MkCompiled _ ctxr x') ← compile scope x
  (MkMerge _ ctx split) ← merge ctxl ctxr
  inr (MkCompiled _ ctx (app ∘ ⟨ f' ⊗ x' ⟩ ∘ split))
compile scope (LetPair lname a rname b value body) = do
  (MkCompiled _ valueCtx value') ← compile scope value
  (MkCompiled _ bodyCtx body') ← compile ((scope , lname) , rname) body
  (_ Data.Product., MkUsedIn _ bodyCtx' reassocr) ← usedIn rname b bodyCtx
  (_ Data.Product., MkUsedIn _ bodyCtx'' reassocl) ← usedIn lname a bodyCtx'
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

test : ∀{a b} → Arr (I ⊗ a) b → Maybe (Arr (I ⊗ a) b)
test (⟨ unitl⁻¹ ⊗ unitl⁻¹ ⟩ ∘ assocr ∘ ⟨ (assocl ∘ ⟨ id ⊗ swap ⟩ ∘ assocr) ⊗ id ⟩ ∘ assocl ∘ ⟨ unitr ⊗ dup ⟩) = just {!!}
test _ = nothing

test1 : ∀{a b} → Arr a b → Maybe (Arr a b)
test1 (⟨ ⟨ f ⊗ g ⟩ ⊗ h ⟩ ∘ assocl) = just (assocl ∘ ⟨ f ⊗ ⟨ g ⊗ h ⟩ ⟩)
test1 _ = nothing
