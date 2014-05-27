module TwoLevel where
open import Lib
open import Base

-- Annotated (two-level) types
data AType : Set where
  SNum : AType
  SFun : AType → AType → AType
  SPrd : AType → AType → AType
  SSum : AType → AType → AType
  D    : Type → AType

-- Meaning of annotated types
ATInt : (Type → Set) → AType → Set
ATInt var SNum = ℕ
ATInt var (SFun A B) = ATInt var A → ATInt var B
ATInt var (SPrd A B) = ATInt var A × ATInt var B
ATInt var (SSum A B) = ATInt var A ⊎ ATInt var B
ATInt var (D t) = exp var t

-- Annotated (two-level) terms
data aexp (var : AType → Set) : AType → Set where
  Var : ∀ {A} → var A → aexp var A
  SCst : ℕ → aexp var SNum
  SSuc : aexp var SNum → aexp var SNum
  SRec : ∀ {α} → aexp var SNum → aexp var α → aexp var (SFun α α) → aexp var α
  SAdd : aexp var SNum → aexp var SNum → aexp var SNum
  SLam : ∀ {A B} → (var A → aexp var B) → aexp var (SFun A B)
  SApp : ∀ {A B} → aexp var (SFun A B) → aexp var A → aexp var B
  SPair : ∀ {A B} → aexp var A → aexp var B → aexp var (SPrd A B)
  SFst : ∀ {A B} → aexp var (SPrd A B) → aexp var A
  SSnd : ∀ {A B} → aexp var (SPrd A B) → aexp var B
  SInl : ∀ {A B} → aexp var A → aexp var (SSum A B)
  SInr : ∀ {A B} → aexp var B → aexp var (SSum A B)
  SCase : ∀ {A B C} → aexp var (SSum A B) →
          (var A → aexp var C) → (var B → aexp var C) →
          aexp var C
  DCst : ℕ → aexp var (D Num)
  DSuc : aexp var (D Num) → aexp var (D Num)
  DRec : ∀ {σ} → aexp var (D Num) → aexp var (D σ) → aexp var (D (Fun σ σ)) → aexp var (D σ)
  DAdd : aexp var (D Num) → aexp var (D Num) → aexp var (D Num)
  DLam : ∀ {A B} → (var (D A) → aexp var (D B)) → aexp var (D (Fun A B))
  DApp : ∀ {A B} → aexp var (D (Fun A B)) → aexp var (D A) → aexp var (D B)
  DPair : ∀ {A B} → aexp var (D A) → aexp var (D B) → aexp var (D (Prd A B))
  DFst : ∀ {A B} → aexp var (D (Prd A B)) → aexp var (D A)
  DSnd : ∀ {A B} → aexp var (D (Prd A B)) → aexp var (D B)
  DInl : ∀ {A B} → aexp var (D A) → aexp var (D (Sum A B))
  DInr : ∀ {A B} → aexp var (D B) → aexp var (D (Sum A B))
  DCase : ∀ {A B C} → aexp var (D (Sum A B)) →
          (var (D A) → aexp var (D C)) → (var (D B) → aexp var (D C)) →
          aexp var (D C)
  Lift : aexp var SNum -> aexp var (D Num)

AExp : AType → Set₁
AExp A = ∀ {var} → aexp var A

-- partial evaluator
pe : ∀ {A var} → aexp (ATInt var) A → ATInt var A
pe (Var x) = x
pe (SCst x) = x
pe (SAdd e1 e2) = pe e1 + pe e2
pe (SSuc e) = suc (pe e)
pe (SRec e e₀ e₁) = natrec (pe e) (pe e₀) (pe e₁)
pe (SLam x) = λ v → pe (x v)
pe (SApp e1 e2) = (pe e1) (pe e2)
pe (SPair e1 e2) = (pe e1 , pe e2)
pe (SFst e) with pe e
... | (v1 , v2) = v1
pe (SSnd e) with pe e
... | (v1 , v2) = v2
pe (SInl e) = inj₁ (pe e)
pe (SInr e) = inj₂ (pe e)
pe (SCase e e1 e2) with pe e
... | inj₁ v = pe (e1 v)
... | inj₂ v = pe (e2 v)
pe (DCst x) = ECst x
pe (DSuc e) = ESuc (pe e)
pe (DRec e e₀ e₁) = ERec (pe e) (pe e₀) (pe e₁)
pe (DAdd e1 e2) = EAdd (pe e1) (pe e2)
pe {D (Fun A2 B)} {var} (DLam x) = ELam (λ v → pe (x (EVar v)))
pe (DApp e1 e2) = EApp (pe e1) (pe e2)
pe (DPair e1 e2) = EPair (pe e1) (pe e2)
pe (DFst e) = EFst (pe e)
pe (DSnd e) = ESnd (pe e)
pe (DInl e) = EInl (pe e)
pe (DInr e) = EInr (pe e)
pe (DCase e e1 e2) = ECase (pe e)
                       (λ v → pe (e1 (EVar v)))
                       (λ v → pe (e2 (EVar v)))
pe (Lift e) = ECst (pe e)

Pe : ∀ {var A} → AExp A → ATInt var A
Pe E = pe E

-- erasure of types
erase : AType → Type
erase SNum = Num
erase (SFun a1 a2) = Fun (erase a1) (erase a2)
erase (SPrd a1 a2) = Prd (erase a1) (erase a2)
erase (SSum a1 a2) = Sum (erase a1) (erase a2)
erase (D t) = t

-- erasure
residualize : ∀ {A var} → aexp (λ A → exp var (erase A)) A → exp var (erase A)
residualize (Var x) = x
residualize (SCst x) = ECst x
residualize (SSuc e) = ESuc (residualize e)
residualize (SRec e e0 es) = ERec (residualize e) (residualize e0) (residualize es)
residualize (SAdd e1 e2) = EAdd (residualize e1) (residualize e2)
residualize (SLam f) = ELam (λ x → residualize (f (EVar x)))
residualize (SApp e1 e2) = EApp (residualize e1) (residualize e2)
residualize (SPair e1 e2) = EPair (residualize e1) (residualize e2)
residualize (SFst e) = EFst (residualize e)
residualize (SSnd e) = ESnd (residualize e)
residualize (SInl e) = EInl (residualize e)
residualize (SInr e) = EInr (residualize e)
residualize (SCase e e1 e2) = ECase (residualize e)
                                    (λ x → residualize (e1 (EVar x)))
                                    (λ x → residualize (e2 (EVar x)))
residualize (DCst x) = ECst x
residualize (DSuc e) = ESuc (residualize e)
residualize (DRec e e0 es) = ERec (residualize e) (residualize e0) (residualize es)
residualize (DAdd e1 e2) = EAdd (residualize e1) (residualize e2)
residualize (DLam f) = ELam (λ x → residualize (f (EVar x)))
residualize (DApp e1 e2) = EApp (residualize e1) (residualize e2)
residualize (DPair e1 e2) = EPair (residualize e1) (residualize e2)
residualize (DFst e) = EFst (residualize e)
residualize (DSnd e) = ESnd (residualize e)
residualize (DInl e) = EInl (residualize e)
residualize (DInr e) = EInr (residualize e)
residualize (DCase e e1 e2) = ECase (residualize e)
                                    (λ x → residualize (e1 (EVar x)))
                                    (λ x → residualize (e2 (EVar x)))
residualize (Lift e) = residualize e

Residualize : ∀ {A} → AExp A → Exp (erase A)
Residualize T = residualize T
