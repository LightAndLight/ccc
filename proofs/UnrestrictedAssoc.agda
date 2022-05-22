module UnrestrictedAssoc where

open import Data.Nat using (ℕ; suc)

module Names where
  open import Data.Product using (_×_; _,_)
  open import Data.String using (String)

  data Name : Set where
    User : String → Name
    Generated : ℕ → Name

  record Names (a : Set) : Set where
    constructor MkNames
    field
      value : ℕ → ℕ × a

  fresh : Names Name
  fresh = MkNames λ n → suc n , (Generated n)

  pure : ∀{a} → a → Names a
  pure a = MkNames λ n → n , a

  _>>=_ : ∀{a b} → Names a → (a → Names b) → Names b
  _>>=_ (MkNames ma) f =
    MkNames λ n →
    let (n' , a) = ma n in
    let (MkNames mb) = f a in
    mb n'

  open import Relation.Nullary using (Dec)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Data.Bool using (Bool)

  User-≡ : ∀{a b} → User a ≡ User b → a ≡ b
  User-≡ _≡_.refl = _≡_.refl

  Generated-≡ : ∀{a b} → Generated a ≡ Generated b → a ≡ b
  Generated-≡ _≡_.refl = _≡_.refl

  _≟_ : (a b : Name) → Dec (a ≡ b)
  User x ≟ User y with (x Data.String.≟ y)
  ... | Bool.false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = Bool.false Relation.Nullary.because Relation.Nullary.ofⁿ λ z → ¬p (User-≡ z)
  ... | Bool.true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl = Bool.true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl
  User x ≟ Generated x₁ = Bool.false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  Generated x ≟ User x₁ = Bool.false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
  Generated x ≟ Generated y with (x Data.Nat.≟ y)
  ... | Bool.false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = Bool.false Relation.Nullary.because Relation.Nullary.ofⁿ (λ z → ¬p (Generated-≡ z))
  ... | Bool.true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl = Bool.true Relation.Nullary.because Relation.Nullary.ofʸ _≡_.refl

module Bwd where
  data Bwd (a : Set) : Set where
    ◆ : Bwd a
    _,_ : Bwd a → a → Bwd a

  open import Data.String using (String; _==_)
  open import Data.Bool using (Bool; false; true; _∨_)

  data Index {a : Set} : Bwd a → a → Set where
    zero : ∀{as x} → Index (as , x) x
    suc : ∀{as x y} → Index as x → Index (as , y) x

  get : ∀{a x} → (xs : Bwd a) → Index xs x → a
  get (xs , x) zero = x
  get (xs , x) (suc ix) = get xs ix

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
  open Names using (Name)

  data Ctx : ℕ → Set where
    ◆ : Ctx 0
    _,_ : ∀{n} → Ctx n → Name × Ty → Ctx (suc n)

  infixl 20 _,_

  [_] : Name × Ty → Ctx 1
  [ a ] = ◆ , a

  data Index : ∀{n} → Ctx n → Set where
    zero : ∀{n} {as : Ctx n} {a} → Index (as , a)
    suc : ∀{n} {as : Ctx n} {a} → Index as → Index (as , a)

  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-comm)

  _++_ : ∀{m n} → Ctx m → Ctx n → Ctx (m + n)
  _++_ {m} a ◆ rewrite (+-comm m 0) = a
  _++_ {m} {n = suc n} a (b , x)
    rewrite (+-comm m (suc n))
    rewrite (+-comm n m) = (a ++ b) , x

module Arr where
  open import Data.Product using (_×_) renaming (_,_ to pair)
  open import Data.String using (String)
  open Ctx using (Ctx; [_]; ◆; _,_)
  open Ty using (Ty; _⊸_)
  open Bwd using (Bwd)
  open Names using (Name)

  fromCtx : ∀{n} → Ctx n → Ty
  fromCtx ◆ = Ty.I
  fromCtx (ctx , pair _ ty) = (fromCtx ctx) Ty.⊗ ty

  data Arr : ∀{m n} → Ctx m → Ctx n → Set where
    id : ∀{n} {a : Ctx n} → Arr a a
    _∘_ : ∀{m n o} {a : Ctx m} {b : Ctx n} {c : Ctx o} → Arr b c → Arr a b → Arr a c

    _∥_ : ∀{m n} {a : Ctx m} {a' : Ctx n} {b b'} → Arr a a' → Arr [ b ] [ b' ] → Arr (a , b) (a' , b')

    abs :
      ∀{n} {ctx : Ctx n} {a b} {name name' name''} →
      Arr (ctx , (pair name a)) [ (pair name' b) ] →
      Arr ctx [ pair name'' (a ⊸ b) ]
    app :
      ∀{a b} {name name' name''} →
      Arr ( ◆ , pair name (a ⊸ b) , pair name' a ) [ pair name'' b ]

    unit :
      ∀{n} {x : Ctx n} →
      (name : Name) →
      Arr x (x , pair name Ty.I)
    pack :
      ∀{n} {x : Ctx n} {a b} {namea nameb} →
      (name : Name) →
      Arr (x , pair namea a , pair nameb b) (x , pair name (a Ty.⊗ b))
    unpack :
      ∀{n} {x : Ctx n} {name} {a b} →
      (aname bname : Name) →
      Arr ( x , pair name (a Ty.⊗ b) ) ( x , pair aname a , pair bname b )

    swap : ∀{n} {ctx : Ctx n} {a b} → Arr (ctx , a , b) (ctx , b , a)
    drop : ∀{n} {ctx : Ctx n} {x} → Arr (ctx , x) ctx
    dup : ∀{n} {ctx : Ctx n} {x} → Arr (ctx , x) (ctx , x , x)

  infixl 20 _∘_
  infixl 20 _∥_

module Expr where
  open import Data.String using (String)
  open Ty using (Ty; _⊸_)
  open Bwd using (Bwd; _,_; Index)

  data Expr : Bwd Ty → Ty → Set where
    Var : ∀{ctx} → String → (a : Ty) → Index ctx a → Expr ctx a
    Lam : ∀{ctx} {b} → String → (a : Ty) → Expr (ctx , a) b → Expr ctx (a ⊸ b)
    App : ∀{ctx} {a b} → Expr ctx (a ⊸ b) → Expr ctx a → Expr ctx b

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
  open import Data.String using (String)
  import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (refl)
  open Names using (Name; _≟_)

  record UsedIn {n} (name : Name) (a : Ty) (ctx : Ctx n) : Set where
    constructor MkUsedIn
    field
      used : Bool
      {n'} : ℕ
      ctx' : Ctx n'
      arrow : Arr (ctx' , pair name a) ctx

  usedIn : ∀{n} → (name : Name) → (a : Ty) → (ctx : Ctx n) → UsedIn name a ctx
  usedIn name a ◆ = MkUsedIn false ◆ drop
  usedIn name a (ctx , pair name' a') with (name ≟ name')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬name≡name =
    let (MkUsedIn used ctx' arrow) = usedIn name a ctx in
    MkUsedIn
      used
      (ctx' , pair name' a')
      ((arrow ∥ id) ∘ swap)
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ refl with (a Ty.≟ a')
  ... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬a≡a =
    let (MkUsedIn used ctx' arrow) = usedIn name a ctx in
    MkUsedIn
      used
      (ctx' , pair name' a')
      ((arrow ∥ id) ∘ swap)
  ... | true Relation.Nullary.because Relation.Nullary.ofʸ refl = MkUsedIn true ctx id

module Merge where
  open Ctx using (Ctx; _,_)
  open Arr
  open import Data.Product using () renaming (_,_ to pair)
  open import Data.Bool using (if_then_else_)
  open import Data.String using (String)
  open Names using (Name; Names; fresh; _>>=_; pure)

  record Merge {m n} (ctxl : Ctx m) (ctxr : Ctx n) : Set where
    constructor MkMerge
    field
      {n'} : ℕ
      ctx : Ctx n'
      {name} : Name
      arrow : Arr ctx (ctxl , pair name (fromCtx ctxr))

  merge : ∀{m n} → (ctxl : Ctx m) → (ctxr : Ctx n) → Names (Merge ctxl ctxr)
  merge ctxl Ctx.◆ = do
    name ← fresh
    pure (MkMerge ctxl (unit name))
  merge ctxl (ctxr , pair name ty) =
    let (UsedIn.MkUsedIn used ctxl' reassoc) = UsedIn.usedIn name ty ctxl in
    if used
    then (do
      (MkMerge ctx arrow) ← merge ctxl' ctxr
      name' ← fresh
      pure (MkMerge
        (ctx , pair name ty)
        ( reassoc ∥ id ∘
          -- lctx , a, Tensor (rctx , a)
          swap ∘
          -- lctx , Tensor (rctx , a) , a
          (pack name ∥ id) ∘
          -- lctx , Tensor rctx , a , a
          dup ∘
          -- lctx , Tensor rctx , a
          (arrow ∥ id)
          -- x , a
        ))
    )
    else do
      (MkMerge ctx arrow) ← merge ctxl ctxr
      name' ← fresh
      pure (MkMerge
        (ctx , pair name ty)
        (pack name' ∘ (arrow ∥ id)))

open Ty using (Ty)
open Ctx using (Ctx; [_])
open Arr
open import Data.Product using () renaming (_,_ to pair)
open import Data.String using (String)
open Names using (Name)

record FromExpr (a : Ty) : Set where
  constructor MkFromExpr
  field
    {n} : ℕ
    ctx : Ctx n
    name : Name
    arrow : Arr ctx [ pair name a ]

open import Data.String using (String)
open import Data.Bool using (if_then_else_)

open Bwd using (Bwd; _,_)
open Expr using (Expr)
open import Data.Nat.Properties using (+-comm)
open Names using (Names; _>>=_; pure; fresh)

mkUnpacks :
  ∀{n} {name} →
  (ctx : Ctx n) →
  Names (Arr [ pair name (fromCtx ctx) ] ctx)
mkUnpacks Ctx.◆ = pure drop
mkUnpacks (ctx Ctx., pair name ty) = do
  name' ← fresh
  rest ← mkUnpacks ctx
  pure (rest ∥ id ∘ unpack name' name)

fromExpr : ∀{b} → (ctx : Bwd Ty) → Expr ctx b → Names (FromExpr b)
fromExpr scope (Expr.Var name ty index) =
  pure (MkFromExpr
    [ pair (Name.User name) ty ]
    (Name.User name)
    id)
fromExpr scope (Expr.Lam name a body) = do
  (MkFromExpr ctx name body') ← fromExpr (scope , a) body
  let (UsedIn.MkUsedIn used ctx' reassoc) = UsedIn.usedIn name a ctx
  name' ← fresh
  pure (MkFromExpr ctx' name' (abs (body' ∘ reassoc)))
fromExpr scope (Expr.App f x) = do
  (MkFromExpr fctx fname f') ← fromExpr scope f
  (MkFromExpr xctx xname x') ← fromExpr scope x
  (Merge.MkMerge ctx split) ← Merge.merge fctx xctx
  unpacks ← mkUnpacks xctx
  name' ← fresh
  pure (MkFromExpr ctx name' (app ∘ (f' ∥ (x' ∘ unpacks)) ∘ split))
