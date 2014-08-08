module BaseFull where
open import Lib

data Type : Set where
  Num : Type
  Fun : Type → Type → Type


  Prd : Type → Type → Type
  Sum : Type → Type → Type


Ctx = List Type

data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ Num
  EAdd : Exp Γ Num → Exp Γ Num → Exp Γ Num
  ESuc : Exp Γ Num → Exp Γ Num
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ') → Exp Γ τ → Exp Γ τ'


  EPair : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (Prd τ τ')
  EFst  : ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ
  ESnd  : ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ'
  EInl  : ∀ {τ τ'} → Exp Γ τ → Exp Γ (Sum τ τ')
  EInr  : ∀ {τ τ'} → Exp Γ τ' → Exp Γ (Sum τ τ')
  ECase : ∀ {τ τ' τ''} → Exp Γ (Sum τ τ') →
          Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''


  ERec  : ∀ {τ} → Exp Γ Num →


          Exp Γ τ → Exp Γ (Fun Num (Fun τ τ)) → Exp Γ τ


TInt : Type → Set
TInt Num = ℕ
TInt (Fun τ₁ τ₂) = TInt τ₁ → TInt τ₂


TInt (Prd τ₁ τ₂) = TInt τ₁ × TInt τ₂
TInt (Sum τ₁ τ₂) = TInt τ₁ ⊎ TInt τ₂


data Env : Ctx → Set where 
  [] : Env []
  _∷_ : ∀ {τ Γ} → TInt τ → Env Γ → Env (τ ∷ Γ)

lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → TInt τ
lookupE hd (x ∷ ρ) = x
lookupE (tl v) (_ ∷ ρ) = lookupE v ρ


natrec : ∀ {t : Set} → ℕ → t → (ℕ → (t → t)) → t
natrec zero v₀ vₛ = v₀
natrec (suc n) v₀ vₛ = vₛ n (natrec n v₀ vₛ)


ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
ev (EVar v) ρ = lookupE v ρ
ev (ECst x) ρ = x
ev (ESuc e) ρ = suc (ev e ρ)
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


ev (ERec eₙ e₀ eₛ) ρ = natrec (ev eₙ ρ) (ev e₀ ρ) (ev eₛ ρ)



