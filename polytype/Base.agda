{- The base language; simply typed lambda calculus with nats, addition, sums and products -}
module Base where
open import Lib

data Type : ℕ →  Set where
  Num : ∀ {n} → Type n
  Fun : ∀ {n} → Type n → Type n → Type n
  All : ∀ {n} → Type (suc n) → Type n
  Var : ∀ {n} → Fin n → Type n

Ctx : ℕ →  Set 
Ctx n = List (Type n)

-- data Ctx : ℕ → Set where
--   [] : ∀ {n} → Ctx n
--   <<_ : ∀ {n} → Ctx (suc n) → Ctx n
--   _::_ : ∀ {n} → Type n → Ctx n → Ctx n

-- data InCtx : {n : ℕ} → Type n → Ctx n → Set where
--   InTyVar : InCtx

data Exp {n : ℕ} (Γ : Ctx n) : Type n → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  

{-  
Ctx = List Type

data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ Num
  ESuc : Exp Γ Num → Exp Γ Num
  ERec : ∀ {τ} → Exp Γ Num → Exp Γ τ → Exp Γ (Fun τ τ) → Exp Γ τ
  EAdd : Exp Γ Num → Exp Γ Num → Exp Γ Num
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ') → Exp Γ τ → Exp Γ τ'
  EPair : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (Prd τ τ')
  EFst :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ
  ESnd :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ'
  EInl :  ∀ {τ τ'} → Exp Γ τ → Exp Γ (Sum τ τ')
  EInr :  ∀ {τ τ'} → Exp Γ τ' → Exp Γ (Sum τ τ')
  ECase : ∀ {τ τ' τ''} → Exp Γ (Sum τ τ') →
          Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''
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
