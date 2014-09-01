--------------------------------------------------------
-- partial evaluation of two-level typed lambda calculus
--------------------------------------------------------
--1)glossary 
--  a)source language: 
--    The language in which the input to the evaluator is written;
--  b)two-level types:
--    The system which types the source language. It consists of
--    the static types "S" and the dynamic types "D";
--  c)base language:
--    The language in which the output of the evaluator is written
--    when the source language is D;
--  d)base types:
--    The system which types the base language
--  e)meta language:
--    Agda syntax in which the output of the evaluator is written when 
--    the source language is S;
--  f)target languages:
--    meta language + base language
--2)summary of the file:
--  The source language,[AExp],containing expressions with parts marked either S or D  and the 
--  base language,[Exp],are specified. The partial evaluator,[pe],taking expressions in source 
--  language as input evaluates static sub-expressions by computing their meta-level projections. 
--  All dynamic sub-expressions,on the other hand are simply translated to the base language. 
--  Thus,the partial evaluator simply transforms a program to another by evaluating parts
--  of that program while keeping the others essentially unchanged.   

module BTA1 where

open import Lib 
open TwoLevelTypes
open Auxiliaries 
open TwoLevelTerms

-----------------------
--some remarks required 
-----------------------
-- stripping of contexts
residual : ACtx → Ctx
residual [] = []
residual (Ann S _ ∷ xs) = residual xs
residual (Ann D σ ∷ xs) = strip' σ ∷ residual xs
-----------------------
--some remarks required
-----------------------

----------------------------------------------------------
--[ATInt] as the interpreter for the types of the 
--target languages. It generates
--a)the base type [Type] if the input type is dynamic;
--b)the Agda types [ℕ] and [→] if the input type is static.
-----------------------------------------------------------
mutual 
  ATInt : Ctx → AType → Set
  ATInt Γ (Ann S σ) = ATInt' Γ σ
  ATInt Γ (Ann D σ) = Exp Γ (strip' σ)
  
  ATInt' : Ctx → SType → Set
  ATInt' Γ SNum = ℕ
  ATInt' Γ (SFun y y') = ∀ {Γ'} → Γ ↝ Γ' → ATInt Γ' y → ATInt Γ' y'

----------------------------------------------------------
--[int↑] weakens the typing context [Γ] of the target term.
----------------------------------------------------------
int↑ : ∀ { α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
int↑ refl e = e
int↑ {Ann S SNum} (extend Γ↝Γ') e = e
int↑ {Ann S (SFun x x₁)} {Γ} {τ ∷ Γ'} (extend {.Γ} {.Γ'} {.τ} Γ↝Γ') e = λ Γ'↝Γ'' x₂ → e ((Γ↝Γ' ⊕ (τ ↝-∷ Γ')) ⊕ Γ'↝Γ'') x₂
int↑ {Ann D x₁} {Γ} {τ ∷ Γ'} (extend {.Γ} {.Γ'} {.τ} Γ↝Γ') e = exp↑ (int↑ {Ann D x₁} Γ↝Γ' e)

------------------------------------------------------------
--[AEnv] as the environment storing the "target values"
--of all free variable occurrences in the source expression.
--Note,
--a)it is not necessary to have two constructors [envS] and 
--  [envD] for static and dynamic values respectively. For they
--  have different type annotations;
--b)in [BTA2.agda] the environment is simplified by having just
--  one constructor [env::] for all target values.
------------------------------------------------------------ 

data AEnv : Ctx → ACtx → Set where
  env[] :  ∀ {Γ} → AEnv Γ []
  envS:: : ∀ {Γ Δ} {α} →
           ATInt Γ α → 
           AEnv Γ Δ →
           AEnv Γ (α ∷ Δ)
  envD:: : ∀ {Γ Δ} →
           (σ : SType) →
           ATInt (strip' σ ∷ Γ) (Ann D σ) →
           AEnv Γ Δ →
           AEnv (strip' σ ∷ Γ) (Ann D σ ∷ Δ)
----------------------------------------------------------
--[env↑] weakens the typing context [Γ] of the environment
----------------------------------------------------------
env↑ : ∀ { Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ _ env[] = env[]
env↑ Γ↝Γ' (envS:: {α = α} x env) = envS:: (int↑ {α} Γ↝Γ' x) (env↑ Γ↝Γ' env)
env↑ Γ↝Γ' (envD:: {Γ} σ x env) = envS:: (int↑ {Ann D σ} Γ↝Γ' x) (env↑ ((strip' σ ↝-∷ Γ) ⊕ Γ↝Γ') env)


-----------------------------------------------------------------------
--[lookup] get from the environment the corresponding "target value" of 
--a given free variable in the source expression.
-----------------------------------------------------------------------
lookup : ∀ {Γ Δ α} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α
lookup () env[] 
lookup hd (envS:: x env) = x
lookup (tl idx) (envS:: x env) = lookup idx env 
lookup hd (envD:: σ x env) = x 
lookup {α = α} (tl idx) (envD:: {Γ} σ x env) = int↑ {α} ((strip' σ) ↝-∷ Γ) (lookup idx env)  


------------------------------------------------------------------------
--[pe] upon receiving a two-level expression [AExp] and an environment
--gives back the corresponding partially evaluated result where all 
--static parts of the expression are computed over their meta-level(Agda)
--projections while the static parts being merely translated to the base
--language 
------------------------------------------------------------------------
pe : ∀ {Δ Γ α} → AEnv Γ Δ → AExp Δ α → ATInt Γ α
pe env (Var idx) = lookup idx env
pe env (Cst S i) = i
pe env (Cst D i) = ECst i
pe {Γ = Γ} env (Lam {α₁} {α₂} S prf exp) = λ {Γ'} (prf₁ : Γ ↝ Γ') (v : ATInt Γ' α₂) →
                                                     pe (envS:: v (env↑ prf₁ env)) exp
pe env (Lam {α₁} {α₂} D (wf-fun _ _ prf-2 prf-1) e)
  with lem-IsDynamic-by-wf α₁ prf-1 | lem-IsDynamic-by-wf α₂ prf-2
pe {Γ = Γ} env (Lam {.(Ann D σ₁)} {.(Ann D σ₂)} D (wf-fun _ _ prf-1 prf-2) e)
  | is-dyn σ₁ | is-dyn σ₂ =
  ELam (pe (envD:: σ₂ (EVar hd) env) e)
pe {Γ = Γ} env (App S _ f e) = (pe env f (refl)) (pe env e)
pe env (App {α₁} {α₂} D (wf-fun _ _ prf-2 prf-1) f e)
  with lem-IsDynamic-by-wf α₁ prf-1 | lem-IsDynamic-by-wf α₂ prf-2
pe env (App {.(Ann D σ₁)}{.(Ann D σ₂)} D (wf-fun _ _ prf-2 prf-1) f e)
 | is-dyn σ₁ | is-dyn σ₂ =
 EApp (pe env f) (pe env e) 
