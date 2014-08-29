--an alternative two-level typed lambda calculus where
--well-formedness restriction is incorporated into the 
--types
module BTA3 where

open import Data.Nat hiding (_<_)
open import Data.Bool
open import Data.List

open import Data.Nat.Properties

open import Relation.Nullary
open import Lib





data Type : Set where
  Num : Type
  Fun : Type → Type → Type


data AType : Set where
    SNum  : AType
    SFun  : AType → AType → AType
    D     : Type → AType

-- typed annotated expressions
ACtx = List AType



Ctx = List Type


≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl


≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n q = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)


≤-suc-right : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc-right z≤n = z≤n
≤-suc-right (s≤s p) = s≤s (≤-suc-right p)


≤-suc-left : ∀ {m n} → suc m ≤ n → m ≤ n
≤-suc-left (s≤s p) = ≤-suc-right p



↝-≤ : ∀ (Γ Γ' : Ctx) → Γ ↝ Γ' → length Γ ≤ length Γ'
↝-≤ .Γ' Γ' refl = ≤-refl
↝-≤ Γ .(τ ∷ Γ') (extend {.Γ} {Γ'} {τ} Γ↝Γ') = ≤-suc-right (↝-≤ Γ Γ' Γ↝Γ')

↝-no-left : ∀ Γ τ → ¬ (τ ∷ Γ) ↝ Γ
↝-no-left Γ τ p = 1+n≰n (↝-≤ (τ ∷ Γ) Γ p)



lem : ∀ {A : Set} (x y : A) (xs xs' : List A) → (x ∷ xs) ↝ xs' → xs ↝ (y ∷ xs')
lem x y xs .(x ∷ xs) refl = extend (extend refl)
lem x y xs .(x' ∷ xs') (extend {.(x ∷ xs)} {xs'} {x'} p) = extend (lem x x' xs xs' p)



-- Typed residula expressions
data Exp'' (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp'' Γ τ
  ECst : ℕ → Exp'' Γ Num
  EAdd : Exp'' Γ Num → Exp'' Γ Num -> Exp'' Γ Num
  ELam : ∀ {τ τ'} → Exp'' (τ ∷ Γ) τ' → Exp'' Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp'' Γ (Fun τ τ')  → Exp'' Γ τ → Exp'' Γ τ'


data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  SCst : ℕ → AExp Δ SNum
  SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
  SLam : ∀ {α₁ α₂}   → AExp (α₂ ∷ Δ) α₁ → AExp Δ (SFun α₂ α₁)
  SApp : ∀ {α₁ α₂}   → AExp Δ (SFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
  DCst : ℕ → AExp Δ (D Num)
  DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
  DLam : ∀ {α₁ α₂}   → AExp ((D α₂) ∷ Δ) (D α₁) → AExp Δ (D (Fun α₂ α₁))
  DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)

-- index Γ = nesting level of dynamic definitions / dynamic environment
Imp'' : Ctx → AType → Set
Imp'' Γ (SNum) = ℕ
Imp'' Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (Imp'' Γ' α₁ → Imp'' Γ' α₂)
Imp'' Γ (D σ) = Exp'' Γ σ


-- index = nesting level of dynamic definitions
data AEnv2 : Ctx → ACtx → Set where
  [] : AEnv2 [] []
  consS : ∀ {Γ Δ Γ'} → Γ ↝ Γ' → (α : AType) → Imp'' Γ' α → AEnv2 Γ Δ → AEnv2 Γ' (α ∷ Δ)
  consD : ∀ {Γ Δ} → (σ : Type) → Exp'' (σ ∷ Γ)  σ → AEnv2 Γ Δ → AEnv2 (σ ∷ Γ) (D σ ∷ Δ) 



elevate-var : ∀ {Γ Γ' : Ctx} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var refl x = x
elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)

elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
elevate-var2 (refl x) x₁ = elevate-var x x₁
elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)

elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp'' Γ τ → Exp'' Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (ECst x) = ECst x
elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)

lift2 : ∀ {Γ Γ'} α → Γ ↝ Γ' → Imp'' Γ α → Imp'' Γ' α 
lift2 SNum p v = v
lift2 (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (↝-trans Γ↝Γ' Γ'↝Γ'')
lift2 (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v

lookup2 : ∀ {α Δ Γ Γ'} → Γ ↝ Γ' → AEnv2 Γ Δ → α ∈ Δ → Imp'' Γ' α
lookup2 Γ↝Γ' (consS p α v env) hd = lift2 α Γ↝Γ' v
lookup2 Γ↝Γ' (consS p α₁ v env) (tl x) = lookup2 (↝-trans p Γ↝Γ') env x
lookup2 Γ↝Γ' (consD α v env) hd = lift2 (D α) Γ↝Γ' v
lookup2 refl (consD α₁ v env) (tl x) = lookup2 (extend refl) env x
lookup2 (extend Γ↝Γ') (consD α₁ v env) (tl x) = lookup2 (lem α₁ _ _ _ Γ↝Γ') env x

pe2 : ∀ {α Δ Γ} → AExp Δ α → AEnv2 Γ Δ → Imp'' Γ α
pe2 (Var x) env = lookup2 refl env x
pe2 (SCst x) env = x
pe2 (SAdd e₁ e₂) env = pe2 e₁ env + pe2 e₂ env
pe2 {SFun α₂ α₁} (SLam e) env = λ Γ↝Γ' → λ y → pe2 e (consS Γ↝Γ' α₂ y env)
pe2 (SApp e₁ e₂) env = ((pe2 e₁ env) refl) (pe2 e₂ env)
pe2 (DCst x) env = ECst x
pe2 (DAdd e e₁) env = EAdd (pe2 e env) (pe2 e₁ env)
pe2 {D (Fun σ₁ σ₂)} (DLam e) env = ELam (pe2 e (consD σ₁ (EVar hd) env))
pe2 (DApp e e₁) env = EApp (pe2 e env) (pe2 e₁ env)

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

  ex-pe-term1 : pe2 term1 [] ≡ ELam (ELam (EVar hd))
  ex-pe-term1 = refl

  ex-pe-term2 : pe2 term2 [] ≡ ELam (ELam (EVar hd))
  ex-pe-term2 = refl

