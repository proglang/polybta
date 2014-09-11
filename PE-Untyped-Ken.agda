----------------------
--Author: Kenichi Asai
----------------------
----------------------------------------------------
--an alternative way of specifying the base-language
--note:
--a)the base-language [Exp'] is specified as untyped 
--  while all variable occurrences are within scope,
--  e.g.  EVar (suc zero) : Exp' n            where
--        1)"untyped" in a sense that [Exp'] does not 
--          take base-type [Type] as its argument;
--        2)"in scope" in a sense that the "scope" 
--          argument [n] is always strictly greater
--          that "De Bruijn" index of the variable;
--        3)one instance of abstraction,
--          λ x → λ y → x as
--          ELam (ELam (EVar (suc zero))) ;
--        4)the λ-binder "lifts" the "typing scope" 
--          from [Exp n] to [Exp (1 + n)].
----------------------------------------------------

module PE-Untyped-Ken where
open import Data.Fin hiding (_≤_ ; pred; _+_)
open import Lib 
open TwoLevelTerms 
open TwoLevelTypes
open Auxiliaries
open import Types
open two-level-types
open import Terms
open two-level-terms

------------------------------------------
--base-language [Exp']:
--a)untyped;
--b)all variable occurrences are in scope.
------------------------------------------
data Exp' : ℕ → Set where
  EVar : ∀ {n} → Fin n → Exp' n
  ECst : ∀ {n} → ℕ → Exp' n
  ELam : ∀ {n} → Exp' (suc n) → Exp' n
  EApp : ∀ {n} → Exp' n → Exp' n → Exp' n


---------------------------------------
--module "Lemmas≡&≤"
--note:
--a)some lemmas regarding equalities
--  of additions;
--b)some lemmas regarding [≤] relation.
---------------------------------------
module Lemmas≡&≤ where 
  open import Data.Nat hiding (_<_)
  open import Data.Bool 
  open import Data.List 
  open import Data.Product 
  open import Function 
  open import Algebra.FunctionProperties using (Commutative; Identity; RightIdentity)
  open import Relation.Binary.PropositionalEquality as PropEq
       using (_≡_; _≢_; refl; sym; cong; cong₂)
  open PropEq.≡-Reasoning 
  open import Data.Nat.Properties public 
  
  m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
  m+1+n≡1+m+n zero    n = refl
  m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

  n+0≡n : ∀ n → n + 0 ≡ n
  n+0≡n zero    = refl
  n+0≡n (suc n) = cong suc $ n+0≡n n

  +-comm : ∀ m n → m + n ≡ n + m
  +-comm zero    n = sym (n+0≡n n)
  +-comm (suc m) n =
    begin
      suc m + n
    ≡⟨ refl ⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
      suc (n + m)
    ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ∎

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

open Lemmas≡&≤ public


-------------------------------------------
--module "Weakening-Ken"
--note:suppose [EVar m : Exp' n]
--     a)EVar m : Exp' n' ∀ n' ≥ n;
--     b)EVar (suc m) : Exp' (suc n);
--     c)EVar (raise n' m) : Exp' (n + n');
--     d)"weaking" can be interpreted as 
--       "whenever the scope is expanded the 
--       indeices of all (free) variable 
--       occurrences have to be lifted by a 
--       corresponding amount";
--     e)e.g.,
--       [EVar zero : Exp' 1] to 
--       [EVar (suc zero) : Exp' 2]. 
-------------------------------------------
module Weakening-Ken where
 
  exp↑≡suc : ∀ {m} {n} → Exp' (m + suc n) → Exp' (suc (n + m))
  exp↑≡suc {m} {n} e rewrite m+1+n≡1+m+n m n | +-comm m n = e

  exp↑m : ∀ {n} m → Exp' (suc n) → Exp' (suc (n + m))
  exp↑m {n} m (EVar x) = exp↑≡suc {m} (EVar (raise m x)) 
  exp↑m m (ECst x) = ECst x
  exp↑m m (ELam e) = ELam (exp↑m m e)
  exp↑m m (EApp e e₁) = EApp (exp↑m m e) (exp↑m m e₁)

  exp0↑m : ∀ m → Exp' zero → Exp' m
  exp0↑m m (EVar ())
  exp0↑m m (ECst x) = ECst x
  exp0↑m m (ELam e) = ELam (exp↑m m e)
  exp0↑m m (EApp e e₁) = EApp (exp0↑m m e) (exp0↑m m e₁)

  exp↑' : ∀ m d → Exp' m → Exp' (m + d)
  exp↑' zero d e = exp0↑m d e
  exp↑' (suc m) d e = exp↑m d e


  exp↑≡∸ : ∀ {m n} → n ≤ m → Exp' (n + (m ∸ n)) → Exp' m
  exp↑≡∸ p e rewrite m+n∸m≡n p = e

open Weakening-Ken public


------------------------------------------------------------------
--[ATInt'] generates
--a)the untyped base-language [Exp'] if the input type is dynamic;
--b)the Agda types [ℕ] and [→] if the input type is static.
------------------------------------------------------------------
ATInt' : (m : ℕ) → AType → Set
ATInt' m (Ann S SNum) = ℕ
ATInt' m (Ann S (SFun α₁ α₂)) = ∀ n → m ≤ n → (ATInt' n α₁ → ATInt' n α₂)
ATInt' m (Ann D σ) = Exp' m

-----------------------------------------------------------
--[int↑'] weakens the typing scope [m] of the target term.
-----------------------------------------------------------
int↑' : ∀ {m n} α → m ≤ n → ATInt' m α → ATInt' n α 
int↑' (Ann S SNum) p v = v
int↑' (Ann S (SFun x x₁)) p v = λ k n≤k → v k (≤-trans p n≤k)
int↑' {m} {n} (Ann D σ) p v = exp↑≡∸ p (exp↑' m (n ∸ m) v)

------------------------------------------------------------------
--[AEnv'] as the environment storing the "target values"
--of all free variable occurrences in the source expression.
--note:
--a)it is not necessary to have two constructors one for dynamic
--  values and one for static values;
--b)for target values are distinguished by their type annotations. 
------------------------------------------------------------------
data AEnv' : ℕ → ACtx → Set where
  [] : AEnv' 0 []
  envS : ∀ {m Δ o} → m ≤ o → (α : AType) → ATInt' o α → AEnv' m Δ → AEnv' o (α ∷ Δ)
  envD : ∀ {m Δ} → (α : AType) → isTrue (D ≼ btof α) → ATInt' (suc m) α → AEnv' m Δ → AEnv' (suc m) (α ∷ Δ)


-----------------------------------------------------------------------
--[lookup'] get from the environment the corresponding "target value" of 
--a given free variable in the source expression.
-----------------------------------------------------------------------
lookup' : ∀ {α Δ m n} → m  ≤ n → AEnv' m Δ → α ∈ Δ → ATInt' n α
lookup' {α} p (envS _ .α x env) hd = int↑' α p x
lookup' {α} p (envD .α x x₁ env) hd = int↑' α p x₁
lookup' p (envS p' .y x env) (tl {_} {y} x₁) = lookup' (≤-trans p' p) env x₁
lookup' p (envD .y x x₁ env) (tl {_} {y} x₂) = lookup' (≤-suc-left p) env x₂


------------------------------------------------------------------------
--[pe'] upon receiving a two-level expression [AExp] and an environment
--gives back the corresponding partially evaluated result where all 
--static parts of the expression are computed over their meta-level(Agda)
--projections while the static parts being merely translated to the base
--language [Exp']
------------------------------------------------------------------------
pe' : ∀ {α Δ} m → AExp Δ α → AEnv' m Δ → ATInt' m α
pe' m (Var x) env = lookup' ≤-refl env x
pe' m (Cst S x) env = x
pe' m (Cst D x) env = ECst x
pe' m (Lam S x e) env = λ o p → λ v → pe' o e (envS p _ v env)
pe' m (Lam {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
pe' m (Lam {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun _ _ d≤bt₁ d≤bt₂) e) env
  | is-dyn σ₁ | is-dyn σ₂ = ELam (pe' (suc m) e (envD (Ann D σ₁) d≤bt₁ (EVar zero) env))
pe' m (App S x e e₁) env = (pe' m e env) m ≤-refl (pe' m e₁ env)
pe' m (App {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env 
  with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
pe' m (App {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env
  | is-dyn σ₁ | is-dyn σ₂ = EApp (pe' m e env) (pe' m e₁ env)

-----------------------------------
--module "SimpAenv" 
--note:
--[AEnv'] is simplified 
--by combining [envS] and [envD].
-----------------------------------
module SimpAenv where
  data AEnv'' : ℕ → ACtx → Set where
    [] : AEnv'' 0 []
    _∷_ : ∀ {m Δ o} → m ≤ o → (α : AType) → ATInt' o α → AEnv'' m Δ → AEnv'' o (α ∷ Δ)

  lookup'' : ∀ {α Δ m n} → m  ≤ n → AEnv'' m Δ → α ∈ Δ → ATInt' n α
  lookup'' {α} p (_∷_ _ .α x env) hd = int↑' α p x
  lookup'' p (_∷_ p' .y x env) (tl {_} {y} x₁) = lookup'' (≤-trans p' p) env x₁

  pe'' : ∀ {α Δ} m → AExp Δ α → AEnv'' m Δ → ATInt' m α
  pe'' m (Var x) env = lookup'' ≤-refl env x
  pe'' m (Cst S x) env = x
  pe'' m (Cst D x) env = ECst x
  pe'' m (Lam S x e) env = λ o p → λ v → pe'' o e (_∷_ p _ v env)
  pe'' m (Lam {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e) env 
    with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
  pe'' m (Lam {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun _ _ d≤bt₁ d≤bt₂) e) env
    | is-dyn σ₁ | is-dyn σ₂ = ELam (pe'' (suc m) e (_∷_  (≤-suc-right ≤-refl)  _ (EVar zero) env))
  pe'' m (App S x e e₁) env = (pe'' m e env) m ≤-refl (pe'' m e₁ env)
  pe'' m (App {α₂} {α₁} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env 
    with lem-IsDynamic-by-wf α₁ d≤bt₁ | lem-IsDynamic-by-wf α₂ d≤bt₂ 
  pe'' m (App {.(Ann D σ₂)} {.(Ann D σ₁)} D (wf-fun w₁ w₂ d≤bt₁ d≤bt₂) e e₁) env
    | is-dyn σ₁ | is-dyn σ₂ = EApp (pe'' m e env) (pe'' m e₁ env)
