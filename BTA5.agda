-------------------------------------------------------
--extended with
--a)pairs and sums
--b)liftable types [Liftable]
--c)lifting constructor [↑] for terms of liftable types
-------------------------------------------------------
module BTA5 where

open import Lib 
open Auxiliaries
open TwoLevelTypes-Simp-PS
open TwoLevelTerms-Simp-PS

----------------------------------------------------------
--[ATInt] as the interpreter for the types of the 
--target languages. It generates
--a)the base type [Type] if the input type is dynamic;
--b)the Agda types [ℕ], [→], [,], [inj₁], and [inj₂] if 
--  the input type is static.
-----------------------------------------------------------
ATInt : Ctx → AType → Set
ATInt Γ (SNum) = ℕ
ATInt Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (ATInt Γ' α₁ → ATInt Γ' α₂)
ATInt Γ (D σ) = Exp Γ σ
ATInt Γ (SPrd α₁ α₂) = (ATInt Γ α₁) × (ATInt Γ α₂)
ATInt Γ (SSum α₁ α₂) = (ATInt Γ α₁) ⊎ (ATInt Γ α₂)


-----------------------------------------------------------
--[int↑] weakens the typing context [Γ] of the target term.
-----------------------------------------------------------
int↑ : ∀ {Γ Γ'} α → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α 
int↑ SNum p v = v
int↑ (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
int↑ (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v
int↑ (SPrd α₁ α₂) Γ↝Γ' (v₁ , v₂) = (int↑ α₁ Γ↝Γ' v₁) , (int↑ α₂ Γ↝Γ' v₂)
int↑ (SSum α₁ α₂) Γ↝Γ' (inj₁ v) = inj₁ (int↑ α₁ Γ↝Γ' v)
int↑ (SSum α₁ α₂) Γ↝Γ' (inj₂ v) = inj₂ (int↑ α₂ Γ↝Γ' v)


------------------------------------------------------------
--[AEnv] as the environment storing the "target values"
--of all free variable occurrences in the source expression.
------------------------------------------------------------ 
data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  _∷_ : ∀ {Δ} {α : AType} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

----------------------------------------------------------
--[env↑] weakens the typing context [Γ] of the environment
----------------------------------------------------------
env↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ Γ↝Γ' [] = []
env↑ Γ↝Γ' (_∷_ {α = α} x env) = _∷_ {α = α} (int↑ α Γ↝Γ' x) (env↑ Γ↝Γ' env)

-----------------------------------------------------------
--[consD] extends the environment with a base type variable
-----------------------------------------------------------  
consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
consD σ env = (_∷_ {α = D σ} (EVar hd) (env↑ (extend {τ = σ} refl) env))

-----------------------------------------------------------------------
--[lookup] get from the environment the corresponding "target value" of 
--a given free variable in the source expression.
----------------------------------------------------------------------- 
lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → ATInt Γ α
lookup [] ()
lookup {α} (x ∷ aenv) hd = x
lookup {α} (x ∷ aenv) (tl {.α} {y} id) = lookup aenv id
  
------------------------------------------------------   
--[lift] helper function for evaluating liftable terms
------------------------------------------------------
mutual 
  lift : ∀ {Γ α} → Liftable α → ATInt Γ α → (Exp Γ (typeof α))
  lift (D τ) v = v
  lift SCst v = ECst v
  lift (SSum ty ty₁) (inj₁ a) = EInl (lift ty a)
  lift (SSum ty ty₁) (inj₂ b) = EInr (lift ty₁ b)
  lift (SPrd ty ty₁) (ffst , ssnd) = EPair (lift ty ffst) (lift ty₁ ssnd)
  lift {Γ} (SFun {α₁} ty₁ ty₂) v = ELam
                                      ((λ x → lift ty₂ (v (extend {τ = typeof α₁} refl) x))
                                       (embed ty₁ (EVar {Γ = typeof α₁ ∷ Γ} hd)))

  embed : ∀ {Γ α} → Liftable⁻ α → Exp Γ (typeof α) → (ATInt Γ α)
  embed (D τ) e = e
  embed (SPrd ty ty₁) e = embed ty (EFst e) , embed ty₁ (ESnd e)
  embed {Γ} (SFun {α} ty₁ ty₂) e = 
    λ Γ↝Γ' v₁ → embed ty₂ (EApp (exp↑ Γ↝Γ' e) (lift ty₁ v₁))

------------------------------------------------------------------------
--[pe] upon receiving a two-level expression [AExp] and an environment
--gives back the corresponding partially evaluated result where all 
--static parts of the expression are computed over their meta-level(Agda)
--projections while the static parts being merely translated to the base
--language 
------------------------------------------------------------------------
pe : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → ATInt Γ α
pe (Var x) env = lookup env x
pe (SCst x) env = x
pe (SAdd e e₁) env = pe e env + pe e₁ env
pe (SLam {α} e) env = λ Γ↝Γ' → λ y → pe e (_∷_ {α = α} y (env↑ Γ↝Γ' env))
pe (SApp e e₁) env = pe e env refl (pe e₁ env)
pe (DCst x) env = ECst x
pe (DAdd e e₁) env = EAdd (pe e env) (pe e₁ env)
pe (DLam {σ} e) env = ELam (pe e (consD σ env))
pe (DApp e e₁) env = EApp (pe e env) (pe e₁ env)
pe {Γ = Γ} (SPair e e₁) env = pe {Γ = Γ} e env , pe {Γ = Γ} e₁ env
pe {α = SSum α₁ α₂} {Γ = Γ} (SInl e) env = inj₁ (pe {α = α₁} {Γ = Γ} e env)
pe {α = SSum α₁ α₂} {Γ = Γ} (SInr e) env = inj₂ (pe {α = α₂} {Γ = Γ} e env)
pe {Γ = Γ} (SFst e) env = proj₁ (pe {Γ = Γ} e env)
pe {Γ = Γ} (SSnd e) env = proj₂ (pe {Γ = Γ} e env)
pe {Γ = Γ} (SCase e e₁ e₂) env with pe {Γ = Γ} e env
pe {Γ = Γ} (SCase {α₁ = α} e e₁ e₂) env | inj₁ y = (λ Γ↝Γ' → λ y → pe e₁ (_∷_ {α = α} y (env↑ Γ↝Γ' env))) refl y
pe {Γ = Γ} (SCase {α₂ = α} e e₁ e₂) env | inj₂ y = (λ Γ↝Γ' → λ y → pe e₂ (_∷_ {α = α} y (env↑ Γ↝Γ' env))) refl y
pe (DPair e e₁) env = EPair (pe e env) (pe e₁ env)
pe (DInl e) env = EInl (pe e env)
pe (DInr e) env = EInr (pe e env)
pe (DFst e) env = EFst (pe e env)
pe (DSnd e) env = ESnd (pe e env)
pe (DCase {σ₁} {σ₂} e e₁ e₂) env = ECase (pe e env) (pe e₁ (consD σ₁ env)) (pe e₂ (consD σ₂ env))
pe (↑ x e) env = lift x (pe e env) 

