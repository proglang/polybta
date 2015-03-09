module PE-STLCfix-correctness where
open import PE-STLCfix
open import Lib
open Auxiliaries
open import Data.Maybe
open import Data.Empty

------------------
--some auxiliaries
------------------
stripα : AType → Type
stripα (D x) = x
stripα (SFun aty aty₁) = Fun (stripα aty) (stripα aty₁)
stripα SNum = Num

stripΔ : ACtx → Ctx
stripΔ = map stripα

strip-lookup : ∀ { α Δ} → α ∈ Δ → stripα α ∈ stripΔ Δ
strip-lookup hd = hd
strip-lookup (tl x) = tl (strip-lookup x)

-------------------------------------------------------
--[_⊢_↝_] Extending a base value environment according 
--to an extension of the corresponding type environment
-------------------------------------------------------
data _⊢_↝_ {Γ} : ∀ {Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
  refl   : ∀ env → refl ⊢ env ↝ env
  extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'}   →
             (v : Maybe (Int τ)) → (Γ↝Γ' ⊢  env ↝ env')   →
             extend Γ↝Γ' ⊢ env ↝ (v ∷ env')

-----------------------------------------------------
--equivalence relation between two evaluation results
-----------------------------------------------------
Equiv : ∀ {α Γ} {n : ℕ} → Env Γ → ATInt Γ α  → Maybe (Int (stripα α)) → Set
Equiv {D x} {n = n} env ae e = ev n ae env ≡ e
Equiv {SFun α α₁} {Γ} {n} env f f' with f'
... | just f'' = ∀ {Γ' env' Γ↝Γ'} →
                   Γ↝Γ' ⊢ env ↝ env' →
                   {x : ATInt Γ' α} →
                   {x'' : Maybe (Int (stripα α))} →
                   Equiv {α} {Γ'} {n} env' x x'' →
                   Equiv {α₁} {Γ'} {n} env' (f Γ↝Γ' x) (f'' x'')
... | nothing  = ⊥
Equiv {SNum}      env ae e = just ae ≡ e

--------------------------------------------------
--[Equiv-Env] equivalence between two environments
-------------------------------------------------- 
data Equiv-Env {Γ' : _} {n : ℕ} (env' : Env Γ') :
     ∀ {Δ} → let Γ = stripΔ Δ in
       AEnv Γ' Δ → Env Γ → Set where
  [] : Equiv-Env env' [] []
  cons : ∀ {α Δ} → let σ = stripα α
                       Γ = stripΔ Δ in
              {env : Env Γ} → {aenv : AEnv Γ' Δ} → 
              Equiv-Env {Γ'} {n} env' aenv env →
              (va : ATInt (Γ') α) → (v : Maybe (Int σ)) → 
              Equiv {α} {Γ'} {n} env' va v → 
              Equiv-Env env' (_∷_ {α = α} va (aenv)) (v ∷ env)


---------------------------
--strip off two-level terms
---------------------------
strip : ∀ {α Δ} → AExp Δ α → Exp (stripΔ Δ) (stripα α)
strip (Var x) = Var (strip-lookup x)
strip (SC x) = C x
strip (DC x) = C x
strip (SDspℕ e e₁ e₂) = Dspℕ (strip e) (strip e₁) (strip e₂)
strip (DDspℕ e e₁ e₂) = Dspℕ (strip e) (strip e₁) (strip e₂)
strip (SSuc e) = Suc (strip e)
strip (DSuc e) = Suc (strip e)
strip (SLam α₁ e) = Lam (stripα α₁) (strip e)
strip (DLam σ₁ e) = Lam σ₁ (strip e)
strip (SApp e e₁) = App (strip e) (strip e₁)
strip (DApp e e₁) = App (strip e) (strip e₁)
------------------------------------------------------------------------------------------------------------------
strip {α} {Δ} (SRec e e₁ e₂) =  App (App (App 
                                 (recursor {stripα α} {stripΔ Δ}) (strip e₁)) --function to be recursively applied 
                                 (strip e₂)) --number of recursive calls
                                 (strip e)   --default 
------------------------------------------------------------------------------------------------------------------
strip (DFix e) = Fix (strip e)

--------------------------------------------
--correctness proof of the partial evaluator
--------------------------------------------
pe-correct : ∀ { α Δ Γ' n} →
            (e : AExp Δ α) →
            (env' : Env Γ') →
            {aenv : AEnv Γ' Δ} → {env : Env (stripΔ Δ)} → 
            Equiv-Env {Γ'} {n} env' aenv env → 
            Equiv {α} {Γ'} {n} env' (pe e aenv) (ev n (strip e) env)
pe-correct = {!!}

