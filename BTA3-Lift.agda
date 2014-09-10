---------------------------------------------------------------
--partial evaluation of a two-level typed lambda calculus
--extended with: 
--a)lifting constructor [Lift] of terms of static integer types
---------------------------------------------------------------
module BTA3-Lift where

open import Lib
open Auxiliaries
open TwoLevelTypes-Simp
open TwoLevelTerms-Simp-Lift



----------------------------------------------------------
--[ATInt] as the interpreter for the types of the 
--target languages. It generates
--a)the base type [Type] if the input type is dynamic;
--b)the Agda types [ℕ] and [→] if the input type is static.
----------------------------------------------------------- 
ATInt : Ctx → AType → Set
ATInt Γ (SNum) = ℕ
ATInt Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (ATInt Γ' α₁ → ATInt Γ' α₂)
ATInt Γ (D σ) = Exp Γ σ
  

-----------------------------------------------------------
--[int↑] weakens the typing context [Γ] of the target term.
-----------------------------------------------------------
int↑ : ∀ {Γ Γ'} α → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α 
int↑ SNum p v = v
int↑ (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
int↑ (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v

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
env↑ Γ↝Γ' (_∷_ {α = α} x env) =  (int↑ α Γ↝Γ' x) ∷ (env↑ Γ↝Γ' env)
  
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
lookup ( v ∷ env) hd =  v 
lookup (v ∷ env) (tl x) = lookup env x
  

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
pe (SAdd e₁ e₂) env = pe e₁ env + pe e₂ env
pe (SLam {α} e) env = λ Γ↝Γ' → λ y → pe e (y ∷ (env↑ Γ↝Γ' env)) 
pe (SApp e₁ e₂) env = ((pe e₁ env) refl) (pe e₂ env)
pe (DCst x) env = ECst x
pe (DAdd e e₁) env = EAdd (pe e env) (pe e₁ env)
pe (DLam {σ} {α₂} e) env = ELam (pe  e (consD α₂ env))
pe (DApp e e₁) env = EApp (pe e env) (pe e₁ env)
pe (Lift e) env = ECst (pe e env) 