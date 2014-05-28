{- The base language; simply typed lambda calculus with nats, addition, sums and products -}
module MultiBase where
open import Lib
open import CtxExtension

data Type : Set where
  Num : Type
  Fun : Type → Type → Type
  Code : Type → Type

Ctx = List (Type × ℕ)

-- according to "An Idealized MetaML: Simpler and More Expressive", without box and run
data Exp (Γ : Ctx) : ℕ → Type → Set where
  EVar : ∀ {n m τ} → (τ , m) ∈ Γ → m ≤ n → Exp Γ n τ
  ECst : ∀ {n} → ℕ → Exp Γ n Num
  EAdd : ∀ {n} → Exp Γ n Num → Exp Γ n Num → Exp Γ n Num
  ELam : ∀ {n τ τ'} → Exp ((τ , n) ∷ Γ) n τ' → Exp Γ n (Fun τ τ')
  EApp : ∀ {n τ τ'} → Exp Γ n (Fun τ τ') → Exp Γ n τ → Exp Γ n τ'
  EBrk : ∀ {n τ} → Exp Γ (suc n) τ → Exp Γ n (Code τ)
  EEsc : ∀ {n τ} → Exp Γ n (Code τ) → Exp Γ (suc n) τ

TInt : Ctx → Type × ℕ → Set
TInt Γ (Num , 0) = ℕ
TInt Γ (Fun τ₁ τ₂ , 0) = ∀ {Γ'} → Γ ↝ Γ' → TInt Γ' (τ₁ , 0) → TInt Γ' (τ₂ , 0)
TInt Γ (Code τ , i) = Exp Γ i τ
TInt Γ (Num , suc i) = Exp Γ i Num
TInt Γ (Fun τ₁ τ₂ , suc i) = Exp Γ i (Fun τ₁ τ₂)

lem-tint-1 : ∀ Γ τ → TInt Γ (τ , 1) ≡ Exp Γ zero τ
lem-tint-1 Γ Num = refl
lem-tint-1 Γ (Fun τ τ₁) = refl
lem-tint-1 Γ (Code τ) = {!!}


data Env (Γ : Ctx) : Ctx → Set where 
  [] : Env Γ []
  _∷_ : ∀ {τ Δ} → TInt Γ τ → Env Γ Δ → Env Γ (τ ∷ Δ)

lookup : ∀ {Γ Δ α} → α ∈ Δ → Env Γ Δ → TInt Γ α
lookup hd (v ∷ _) = v 
lookup (tl x) (_ ∷ ρ) = lookup x ρ

ev : ∀ { Γ Δ τ } → (i : ℕ) → Exp Δ i τ → Env Γ Δ → TInt Γ (τ , i)
ev zero (EVar x z≤n) ρ = lookup x ρ
ev zero (ECst n) ρ = n
ev zero (EAdd e₁ e₂) ρ = ev zero e₁ ρ + ev zero e₂ ρ
ev zero (ELam e) ρ = λ Γ↝Γ' → λ y → ev 0 e {!!}
ev zero (EApp e₁ e₂) ρ = ev 0 e₁ ρ refl (ev 0 e₂ ρ)
ev {τ = Code τ} zero (EBrk e) ρ = ev {τ = {!!}} 1 {!e!} ρ
ev (suc i) (EVar x p) ρ = {!!}
ev (suc i) (ECst x) ρ = ECst x
ev (suc i) (EAdd e e₁) ρ = EAdd (ev (suc i) e ρ) (ev (suc i) e₁ ρ)
ev (suc i) (ELam e) ρ = {!!}
ev (suc i) (EApp e e₁) ρ = {!!}
ev (suc i) (EBrk e) ρ = {!!}
ev (suc i) (EEsc e) ρ = {!!}

{-
  ERec : ∀ {τ} → Exp Γ Num → Exp Γ τ → Exp Γ (Fun τ τ) → Exp Γ τ


lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → TInt τ
lookupE hd (x ∷ ρ) = x
lookupE (tl v) (_ ∷ ρ) = lookupE v ρ

natrec : ∀ { t : Set } → ℕ → t → (t → t) → t
natrec zero v0 vs = v0
natrec (suc n) v0 vs = vs (natrec n v0 vs)

ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
ev (EVar v) ρ = lookupE v ρ
ev (ECst x) ρ = x
ev (ESuc e) ρ = suc (ev e ρ)
ev (ERec e e0 es) ρ = natrec (ev e ρ) (ev e0 ρ) (ev es ρ)
ev (EAdd e f) ρ = ev e ρ + ev f ρ
ev (ELam e) ρ = λ x → ev e (x ∷ ρ)
ev (EApp e f) ρ = ev e ρ (ev f ρ)
ev (EPair e f) ρ = ev e ρ , ev f ρ
ev (EFst e) ρ = proj₁ (ev e ρ)
ev (ESnd e) ρ = proj₂ (ev e ρ)
ev (EInl e) ρ = inj₁ (ev e ρ)
ev (EInr e) ρ = inj₂ (ev e ρ)
ev (ECase e e₁ e₂) ρ with ev e ρ
... | inj₁ v = ev e₁ (v ∷ ρ)
... | inj₂ v = ev e₂ (v ∷ ρ)
-}
