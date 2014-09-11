-----------------------------------------------------
--extended with liftable terms(higher order), pairs, 
--sums, iterators, and recursors.
-----------------------------------------------------
module PE-STLC-wft-full where
open import Lib
open Auxiliaries
open TwoLevelTerms-Simp-PSRI
open import Types
open two-level-types-simp-ps
open import Terms
open two-level-terms-simp-lift-psri

----------------------------------------------------------
--[ATInt] as the interpreter for the types of the 
--target languages. It generates
--a)the base type [Type] if the input type is dynamic;
--b)the Agda types [ℕ], [→], [,], [inj₁], and [inj₂] if 
--  the input type is static.
-----------------------------------------------------------
ATInt : Ctx → AType → Set
ATInt _ SNum          = ℕ
ATInt Γ (D σ)         = Exp Γ σ
ATInt Γ (SFun α₁ α₂)  =
  ∀ {Γ'} → Γ ↝ Γ' → ATInt Γ' α₁ → ATInt Γ' α₂
ATInt Γ (SPrd α₁ α₂) = ATInt Γ α₁ × ATInt Γ α₂
ATInt Γ (SSum α₁ α₂) = (ATInt Γ α₁) ⊎ (ATInt Γ α₂)

-----------------------------------------------------------
--[int↑] weakens the typing context [Γ] of the target term.
-----------------------------------------------------------
int↑ : ∀ { α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
int↑ refl v = v
int↑ {D τ} (extend Γ↝Γ') e = exp↑ (int↑ Γ↝Γ' e)
int↑ {SNum} _ v = v
int↑ {SFun α α₁} Γ↝Γ' f =
  λ Γ'↝Γ'' x → f (Γ↝Γ' ⊕ Γ'↝Γ'') x
int↑ {SPrd α α₁} Γ↝Γ' (proj₁ , proj₂) = int↑ Γ↝Γ' proj₁ , int↑ Γ↝Γ' proj₂
int↑ {SSum α α₁} Γ↝Γ' (inj₁ x) = inj₁ (int↑ Γ↝Γ' x)
int↑ {SSum α α₁} Γ↝Γ' (inj₂ y) = inj₂ (int↑ Γ↝Γ' y)

------------------------------------------------------------
--[AEnv] as the environment storing the "target values"
--of all free variable occurrences in the source expression.
------------------------------------------------------------ 
data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  _∷_ : ∀ {α Δ} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

----------------------------------------------------------
--[env↑] weakens the typing context [Γ] of the environment
----------------------------------------------------------
env↑ : ∀ { Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ _ [] = []
env↑ Γ↝Γ' (x ∷ ρ) = int↑ Γ↝Γ' x ∷ env↑ Γ↝Γ' ρ

-----------------------------------------------------------
--[consD] extends the environment with a base type variable
----------------------------------------------------------- 
consD : ∀ {τ Γ Δ} → AEnv Γ Δ → AEnv (τ ∷ Γ) (D τ ∷ Δ)
consD ρ = EVar hd ∷ env↑ (extend refl) ρ

-----------------------------------------------------------------------
--[lookup] get from the environment the corresponding "target value" of 
--a given free variable in the source expression.
----------------------------------------------------------------------- 
lookup : ∀ {Γ Δ α} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α
lookup hd (v ∷ _) = v 
lookup (tl x) (_ ∷ ρ) = lookup x ρ

------------------------------------------------------   
--[lift] helper function for evaluating liftable terms
------------------------------------------------------
mutual 
  lift : ∀ {Γ α} → Liftable α → ATInt Γ α → (Exp Γ (typeof α))
  lift (D τ) v = v
  lift SCst v = ECst v
  lift (SSum ty ty₁) (inj₁ a) = EInl (lift ty a)
  lift (SSum ty ty₁) (inj₂ b) = EInr (lift ty₁ b)
  lift (SPrd ty ty₁) (v1 , v2) = EPair (lift ty v1) (lift ty₁ v2)
  lift (SFun {α₁} ty₁ ty₂) f =
    ELam let x = (embed ty₁ (EVar hd)) in
         lift ty₂ (f (extend refl) x)

  embed : ∀ {Γ α} →
    Liftable⁻ α → Exp Γ (typeof α) → (ATInt Γ α)
  embed (D τ) e = e
  embed (SPrd ty ty₁) e = embed ty (EFst e) , embed ty₁ (ESnd e)
  embed {Γ} (SFun {α} ty₁ ty₂) e = 
    λ Γ↝Γ' v₁ → embed ty₂ (EApp (int↑ Γ↝Γ' e) (lift ty₁ v₁))


------------------------------------------------------------------------
--[pe] upon receiving a two-level expression [AExp] and an environment
--gives back the corresponding partially evaluated result where all 
--static parts of the expression are computed over their meta-level(Agda)
--projections while the static parts being merely translated to the base
--language 
------------------------------------------------------------------------
pe : ∀ { Γ Δ α } → AExp Δ α → AEnv Γ Δ → ATInt Γ α
pe (Var x) ρ       = lookup x ρ
pe (DLam e) ρ      = ELam (pe e (consD ρ))
pe (SApp f e) ρ    = (pe f ρ) refl (pe e ρ)
pe (SLam {α} e) ρ  = λ Γ↝Γ' x → pe e (x ∷ env↑ Γ↝Γ' ρ)
pe (DApp f e) ρ    = EApp (pe f ρ) (pe e ρ)
pe (SCst x) _      = x
pe (DCst x) _      = ECst x
pe (SSuc e) ρ      = suc (pe e ρ)
pe (DSuc e) ρ      = ESuc (pe e ρ)
pe (SIt e e₀ e₁) ρ = natit (pe e ρ) (pe e₀ ρ) (pe e₁ ρ refl)
pe (DIt e e₀ e₁) ρ = EIt (pe e ρ) (pe e₀ ρ) (pe e₁ ρ)
pe {Γ} (SRec v u n) ρ = natrec (pe n ρ) (pe v ρ) (λ n₁ → pe u ρ {Γ} refl n₁ {Γ} refl)
pe (DRec v u n) ρ = ERec (pe v ρ) (pe u ρ) (pe n ρ)
pe (SAdd e f) ρ    = (pe e ρ) + (pe f ρ) 
pe (DAdd e f) ρ    = EAdd (pe e ρ) (pe f ρ) 
pe (SPair e e₁) ρ = pe e ρ , pe e₁ ρ
pe (SInl e) ρ = inj₁ (pe e ρ)
pe (SInr e) ρ = inj₂ (pe e ρ)
pe (SFst e) ρ = proj₁ (pe e ρ)
pe (SSnd e) ρ = proj₂ (pe e ρ)
pe (SCase e e₁ e₂) ρ with pe e ρ
... | inj₁ v = pe e₁ (v ∷ ρ)
... | inj₂ v = pe e₂ (v ∷ ρ)
pe (DPair e e₁) ρ = EPair (pe e ρ) (pe e₁ ρ)
pe (DInl e) ρ = EInl (pe e ρ)
pe (DInr e) ρ = EInr (pe e ρ)
pe (DFst e) ρ = EFst (pe e ρ)
pe (DSnd e) ρ = ESnd (pe e ρ)
pe (DCase e e₁ e₂) ρ = ECase (pe e ρ) (pe e₁ (consD ρ)) (pe e₂ (consD ρ))
pe (Lift lftbl e) ρ = lift lftbl (pe e ρ)




