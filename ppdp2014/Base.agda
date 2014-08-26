module Base where
open import Lib


data Type : Set where
  Num : Type
  Fun : Type → Type → Type

Ctx = List Type


data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ Num
  EAdd : Exp Γ Num → Exp Γ Num → Exp Γ Num
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ') → Exp Γ τ → Exp Γ τ'


TInt : Type → Set
TInt Num = ℕ
TInt (Fun τ₁ τ₂) = TInt τ₁ → TInt τ₂


EnvSimple : Set
EnvSimple = List (∃ λ α → TInt α)


data Env : Ctx → Set where 
  [] : Env []
  _∷_ : ∀ {τ Γ} → TInt τ → Env Γ → Env (τ ∷ Γ)


lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → TInt τ
lookupE hd (x ∷ ρ) = x
lookupE (tl v) (_ ∷ ρ) = lookupE v ρ


ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
ev (EVar v) ρ = lookupE v ρ
ev (ECst x) ρ = x
ev (EAdd e f) ρ = ev e ρ + ev f ρ
ev (ELam e) ρ = λ x → ev e (x ∷ ρ)
ev (EApp e f) ρ = ev e ρ (ev f ρ)



