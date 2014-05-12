module Base where
open import Lib

-- Types of residual terms (= types of dynamic terms)
data Type : Set where
  Num : Type
  Fun : Type → Type → Type
  Prd : Type → Type → Type
  Sum : Type → Type → Type

-- Residual terms
data exp (var : Type → Set) : Type → Set where
  EVar : ∀ {A} → var A → exp var A
  ECst : ℕ → exp var Num
  ESuc : exp var Num → exp var Num
  ERec : ∀ {τ} → exp var Num → exp var τ → exp var (Fun τ τ) → exp var τ
  EAdd : exp var Num → exp var Num → exp var Num
  ELam : ∀ {A B} → (var A → exp var B) → exp var (Fun A B)
  EApp : ∀ {A B} → exp var (Fun A B) → exp var A → exp var B
  EPair : ∀ {A B} → exp var A → exp var B → exp var (Prd A B)
  EFst : ∀ {A B} → exp var (Prd A B) → exp var A
  ESnd : ∀ {A B} → exp var (Prd A B) → exp var B
  EInl : ∀ {A B} → exp var A → exp var (Sum A B)
  EInr : ∀ {A B} → exp var B → exp var (Sum A B)
  ECase : ∀ {A B C} → exp var (Sum A B) →
          (var A → exp var C) → (var B → exp var C) →
          exp var C

Exp : Type → Set₁
Exp A = ∀ {var} → exp var A

-- Meaning of types
TInt : Type → Set
TInt Num = ℕ
TInt (Fun A B) = TInt A → TInt B
TInt (Prd A B) = TInt A × TInt B
TInt (Sum A B) = TInt A ⊎ TInt B

-- interpreter
natrec : ∀ { t : Set } → ℕ → t → (t → t) → t
natrec zero v0 vs = v0
natrec (suc n) v0 vs = vs (natrec n v0 vs)

ev : ∀ {A} → exp TInt A → TInt A
ev (EVar x) = x
ev (ECst x) = x
ev (ESuc x) = suc (ev x)
ev (ERec e e0 es) = natrec (ev e) (ev e0) (ev es)
ev (EAdd e1 e2) = ev e1 + ev e2
ev (ELam f) = λ v → ev (f v)
ev (EApp e1 e2) = (ev e1) (ev e2)
ev (EPair e1 e2) = (ev e1 , ev e2)
ev (EFst e) with ev e
... | (v1 , v2) = v1
ev (ESnd e) with ev e
... | (v1 , v2) = v2
ev (EInl e) = inj₁ (ev e)
ev (EInr e) = inj₂ (ev e)
ev (ECase e e1 e2) with ev e
... | inj₁ v = ev (e1 v)
... | inj₂ v = ev (e2 v)

Ev : ∀ {A} → Exp A → TInt A
Ev E = ev E
