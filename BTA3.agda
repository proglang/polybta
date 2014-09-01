------------------------------------------------------
--an alternative two-level typed lambda calculus where
--well-formedness restriction is incorporated into the 
--types
------------------------------------------------------
--summary of the file:
--a)the well-formedness restriction over two-level types
--  [AType] is incorporated into the typing system by 
--  specifying all dynamic types as [D type] where [type : Type]
--  ,reflecting the notion that all sub-types of a dynamic types
--  are themselves dynamic types;
--b)the corresponding expressions are divied syntactically w.r.t.
--  their type annotations;
--c)both the source language and the base language are extended with
--  additions.
module BTA3 where
open import Lib
open Auxiliaries
open TwoLevelTypes-Simp
open TwoLevelTerms-Simp

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
int↑ : ∀ {α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α 
int↑ {SNum} p v = v
int↑ {SFun x x₁} Γ↝Γ' v = λ Γ'↝Γ'' → v (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
int↑ {D x₁} Γ↝Γ' v = elevate (refl Γ↝Γ') v

------------------------------------------------------------
--[AEnv] as the environment storing the "target values"
--of all free variable occurrences in the source expression.
------------------------------------------------------------ 
data AEnv : Ctx → ACtx → Set where
  []   :  ∀ {Γ} → AEnv Γ []
  _∷_  :  ∀ {Γ Δ} {α : AType} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

----------------------------------------------------------
--[env↑] weakens the typing context [Γ] of the environment
----------------------------------------------------------
env↑ : ∀ {Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ _ [] = []
env↑ Γ↝Γ' (_∷_ {α = α} x env) = (int↑ {α} Γ↝Γ' x) ∷ (env↑ Γ↝Γ' env) 

-----------------------------------------------------------------------
--[lookup] get from the environment the corresponding "target value" of 
--a given free variable in the source expression.
-----------------------------------------------------------------------
lookup : ∀ {Γ Δ α} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α
lookup () []
lookup hd (x ∷ env) = x
lookup (tl idx) (x ∷ env) = lookup idx env


------------------------------------------------------------------------
--[pe] upon receiving a two-level expression [AExp] and an environment
--gives back the corresponding partially evaluated result where all 
--static parts of the expression are computed over their meta-level(Agda)
--projections while the static parts being merely translated to the base
--language 
------------------------------------------------------------------------
pe : ∀ {α Δ Γ} → AEnv Γ Δ → AExp Δ α → ATInt Γ α
pe env (Var x) = lookup x env 
pe env (SCst x) = x
pe env (SAdd e₁ e₂) = pe env e₁ + pe env e₂ 
pe {SFun α₂ α₁} {Γ = Γ} env (SLam e) = λ {Γ'} (prf₁ : Γ ↝ Γ') (v : ATInt Γ' α₂) → pe (v ∷ (env↑ prf₁ env)) e 
pe env (SApp e₁ e₂) = ((pe env e₁) refl) (pe env e₂)
pe env (DCst x) = ECst x
pe env (DAdd e e₁) = EAdd (pe env e) (pe env e₁)
pe {D (Fun σ₁ σ₂)} {Γ = Γ} env (DLam e) = ELam (pe ((EVar hd) ∷ env↑ (σ₁ ↝-∷ Γ) env) e)
pe env (DApp e e₁) = EApp (pe env e) (pe env e₁)

module Examples where
  open import Relation.Binary.PropositionalEquality

  x : ∀ {α Δ} → AExp (α ∷ Δ) α
  x = Var hd
  y : ∀ {α₁ α Δ} → AExp (α₁ ∷ α ∷ Δ) α
  y = Var (tl hd)
  z : ∀ {α₁ α₂ α Δ} → AExp (α₁ ∷ α₂ ∷ α ∷ Δ) α
  z = Var (tl (tl hd))


  term1 : AExp [] (D (Fun Num (Fun Num Num)))
  term1 = DLam (SApp (SLam (DLam (SApp (SLam y) x)))
                     ((SLam (DAdd x y))))


  term2 : AExp [] (D (Fun Num (Fun Num Num)))
  term2 = DLam (SApp (SLam (DLam (SApp (SLam y) x)))
                     ((SLam (DLam {α₂ = Num} (DAdd y z)))))

  ex-pe-term1 : pe {D (Fun Num (Fun Num Num))} {[]} {[]} [] term1 ≡ ELam (ELam (EVar hd))
  ex-pe-term1 = refl

  ex-pe-term2 : pe {D (Fun Num (Fun Num Num))} {[]} {[]} [] term2  ≡ ELam (ELam (EVar hd))
  ex-pe-term2 = refl

