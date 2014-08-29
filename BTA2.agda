--simplify the environment [AEnv] defined in [BTA1.agda] 
--by combining constructors [envD] and [envS]

module BTA2 where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Lib

-- Binding times
data BT : Set where
  S : BT
  D : BT

-- defining a data type [BT],where two members are
-- [S] standing for "static" and [D] standing for dynamic.

-- ``subsumption'' binding times; static can be treated as dynamic,
-- but not vice versa
_≼_ : BT → BT → Bool
_≼_ D S  = false
_≼_ _ _  = true


-- Standard propositional equality, see also Relation.Binary.PropositionalEquality
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x



record True : Set where
data False : Set where


isTrue : Bool → Set
isTrue true  = True
isTrue false = False


-----------
-- Sublists
-----------
data _cx-≤_ {A : Set} : List A → List A → Set where
  cxle-eq : (l : List A) → l cx-≤ l
  cxle-lt : ∀ {l₁ l₂} x → l₁ cx-≤ l₂ → l₁ cx-≤ (x ∷ l₂)


lem-cx-≤-trans : {A : Set} → {l₁ : List A} {l₂ : List A} {l₃ : List A} →
                 l₁ cx-≤ l₂ → l₂ cx-≤ l₃ → l₁ cx-≤ l₃
lem-cx-≤-trans le1  (cxle-eq l) = le1
lem-cx-≤-trans (cxle-eq l) (cxle-lt x e) = cxle-lt x e
lem-cx-≤-trans (cxle-lt x e) (cxle-lt x' e') = cxle-lt x' (lem-cx-≤-trans (cxle-lt x e) e')

_cxle-∷_ : {A : Set} (x : A) (l : List A) → l cx-≤ (x ∷ l)
x cxle-∷ l = cxle-lt x (cxle-eq l)


data _⊆_ {A : Set} : List A → List A → Set where
  refl-⊆ : ∀ {l} → l ⊆ l
  step-⊆ : ∀ {l} x l₁ l₂ → l ⊆ (l₁ ++ l₂) → l ⊆ (l₁ ++ (x ∷ l₂))

lem-⊆-trans : {A : Set} → {l₁ : List A} {l₂ : List A} {l₃ : List A} →
                 l₁ ⊆ l₂ → l₂ ⊆ l₃ → l₁ ⊆ l₃
lem-⊆-trans e (refl-⊆ {l}) = e
lem-⊆-trans (refl-⊆ {l}) (step-⊆ x l₁ l₂ e) = step-⊆ x l₁ l₂ e
lem-⊆-trans (step-⊆ x l₁ l₂ e) (step-⊆ x' l₁' l₂' e') = step-⊆ x' l₁' l₂' (lem-⊆-trans (step-⊆ x l₁ l₂ e) e')

---------------
-- end sublists
---------------

-- some lemmas about BT subsumption
lem-bt≼S : {bt : BT} → isTrue (bt ≼ S) → bt == S
lem-bt≼S {S} bt≼S = refl
lem-bt≼S {D} ()



lem-D≼bt : {bt : BT} → isTrue (D ≼ bt) → bt == D
lem-D≼bt {S} ()
lem-D≼bt {D} D≼bt = refl


-- Types of the calculus
mutual
  -- s ^ BT
  data AType : Set where
    Ann : BT → SType → AType

  -- int | t -> t
  data SType : Set where
    SNum  : SType
    SFun  : AType → AType → SType


-- aux definitions
ATInt : BT → AType
ATInt bt = Ann bt SNum
ATFun  : BT → AType → AType → AType
ATFun  bt at1 at2 = Ann bt (SFun at1 at2)


-- projection: get the BT from a type
btof : AType → BT
btof (Ann bt _) = bt

-- constraint on types: well-formedness
data wft : AType → Set where
  wf-int  : ∀ {bt} → wft (Ann bt SNum)
  wf-fun  : ∀ {bt at1 at2} → wft at1 → wft at2
          → isTrue (bt ≼ btof at1) → isTrue (bt ≼ btof at2) → wft (Ann bt (SFun at1 at2))


lem-force-bt : ∀ {bt at} → isTrue (bt ≼ btof at) → D == bt → D == btof at
lem-force-bt {S} bt≼at ()
lem-force-bt {D} {Ann S y'} () D=bt
lem-force-bt {D} {Ann D y'} bt≼at D=bt = refl


-- Low-level types
data Type : Set where
  TNum : Type
  TFun : Type → Type → Type

-- translation from ATypes to low-level types
mutual
  strip : AType → Type
  strip (Ann _ σ) = strip' σ

  strip' : SType → Type
  strip' SNum = TNum
  strip' (SFun y y') = TFun (strip y) (strip y')





-- Typing context
Ctx = List Type



-- Typed expression
data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ TNum
  ELam : ∀ {τ₁ τ₂} → Exp (τ₂ ∷ Γ) τ₁ → Exp Γ (TFun τ₂ τ₁)
  EApp : ∀ {τ₁ τ₂} → Exp Γ (TFun τ₂ τ₁) → Exp Γ τ₂ → Exp Γ τ₁


count_tl : ∀ {A Γ Γ'} {τ : A} → τ ∈ Γ → Γ cx-≤ Γ' → τ ∈ Γ'
count_tl  x (cxle-eq Γ) = x
count_tl x  (cxle-lt T e) = tl (count_tl x e)


data _cx=≤_ {A : Set} : List A → List A → Set where
  cxle-peq : ∀ {l₁ l₂} { x } → l₁ cx-≤ l₂ → (x ∷ l₁) cx=≤ (x ∷ l₂)
  cxle-plt : ∀ {l₁ l₂} { x } → l₁ cx=≤ l₂ → (x ∷ l₁) cx=≤ (x ∷ l₂)

count_tl' : ∀ {A  Γ Γ'} {τ : A } → τ ∈ Γ → Γ cx=≤ Γ' → τ ∈ Γ'
count_tl' hd (cxle-plt e) = hd
count_tl' hd (cxle-peq e) = hd
count_tl' (tl xid) (cxle-plt e) = tl (count_tl' xid  e)
count_tl' (tl xid) (cxle-peq e) = tl (count_tl xid e)



lem-Exp-weakening' : ∀ {τ₂ τ₁ Γ Γ'} → Exp (τ₂ ∷ Γ) τ₁ → (τ₂ ∷ Γ) cx=≤ (τ₂ ∷ Γ') → Exp (τ₂ ∷ Γ') τ₁
lem-Exp-weakening' (EVar x) e  = EVar (count_tl' x e)
lem-Exp-weakening'  (ECst n) e = ECst n
lem-Exp-weakening'  (ELam t) e = ELam (lem-Exp-weakening' t (cxle-plt e))
lem-Exp-weakening'  (EApp t1 t2) e = EApp (lem-Exp-weakening' t1 e) (lem-Exp-weakening' t2 e)   

lem-Exp-weakening : ∀ {τ Γ Γ'} → Exp Γ τ → Γ cx-≤ Γ' → Exp Γ' τ
lem-Exp-weakening t (cxle-eq Γ) = t
lem-Exp-weakening (ECst n) e = ECst n
lem-Exp-weakening (EVar x) e  = EVar (count_tl x e)
lem-Exp-weakening (ELam t) (cxle-lt T e) = ELam (lem-Exp-weakening' t (cxle-peq (cxle-lt T e))) 
lem-Exp-weakening (EApp t1 t2) e = EApp (lem-Exp-weakening t1 e) (lem-Exp-weakening t2 e)




-- typed annotated expressions
ACtx = List AType

data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  Cst : (bt : BT) → ℕ → AExp Δ (ATInt bt)
  Lam : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp (α₂ ∷ Δ) α₁ → AExp Δ (ATFun bt α₂ α₁)
  App : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp Δ (ATFun bt α₂ α₁) → AExp Δ α₂ → AExp Δ α₁


-- stripping of contexts
residual : ACtx → Ctx
residual [] = []
residual (Ann S _ ∷ xs) = residual xs
residual (Ann D σ ∷ xs) = strip' σ ∷ residual xs

-- ``semantic domain'' for partially evaluated AExp-terms:
--   - AExp-terms of dynamic type evaluate to Exp-terms
--   - AExp-terms of static type evaluate to agda terms, where SFun
--     are functions and SInt are natural numbers
mutual 
  impTA : Ctx → AType → Set
  impTA Γ (Ann S σ) = impTA' Γ σ
  impTA Γ (Ann D σ) = Exp Γ (strip' σ)
  
  impTA' : Ctx → SType → Set
  impTA' Γ SNum = ℕ
  impTA' Γ (SFun y y') = ∀ {Γ'} → Γ cx-≤ Γ' → impTA Γ' y → impTA Γ' y'

lem-impTA-weakening : ∀ {α Γ Γ'} →
                      impTA Γ α →
                      Γ cx-≤ Γ' →
                      impTA Γ' α
lem-impTA-weakening {Ann S SNum} v _ = v
lem-impTA-weakening {Ann S (SFun x x₁)} f prf = λ prf' → f (lem-cx-≤-trans prf prf')
lem-impTA-weakening {Ann D x₁} v prf = lem-Exp-weakening v prf 

data AEnv : Ctx → ACtx → Set where
  env[] :  ∀ {Γ} → AEnv Γ []
  env:: : ∀ {Γ Δ} {α} →
           impTA Γ α → 
           AEnv Γ Δ →
           AEnv Γ (α ∷ Δ)

lem-AEnv-weakening : ∀ {Γ Γ' Δ} → AEnv Γ Δ → Γ cx-≤ Γ' → AEnv Γ' Δ
lem-AEnv-weakening env[] prf = env[]
lem-AEnv-weakening (env:: {α = α} x env) prf = env:: (lem-impTA-weakening {α} x prf) (lem-AEnv-weakening env prf)

lookup : ∀ {Γ Δ α} → AEnv Γ Δ → (o : α ∈ Δ ) → impTA Γ α
lookup env[] ()
lookup (env:: x env) hd = x
lookup (env:: x env) (tl idx) = lookup env idx

data IsDynamic : AType → Set where
  is-dyn : ∀ σ → IsDynamic (Ann D σ)

lem-IsDynamic-by-wf : ∀ α → isTrue (D ≼ btof α) → IsDynamic α
lem-IsDynamic-by-wf (Ann S σ) ()
lem-IsDynamic-by-wf (Ann D σ) _ = is-dyn σ 


pe : ∀ {Δ Γ α} → AEnv Γ Δ → AExp Δ α → impTA Γ α
pe env (Var idx) = lookup env idx
pe env (Cst S i) = i
pe env (Cst D i) = ECst i
pe {Γ = Γ} env (Lam {α₁} {α₂} S prf exp) =
  λ {Γ'} (prf₁ : Γ cx-≤ Γ') (v : impTA Γ' α₂) → pe (env:: v (lem-AEnv-weakening env prf₁)) exp
pe env (Lam {α₁} {α₂} D (wf-fun _ _ prf-2 prf-1) e)
  with lem-IsDynamic-by-wf α₁ prf-1 | lem-IsDynamic-by-wf α₂ prf-2
pe {Γ = Γ} env (Lam {.(Ann D σ₁)} {.(Ann D σ₂)} D (wf-fun _ _ prf-1 prf-2) e)
  | is-dyn σ₁ | is-dyn σ₂ =
  ELam (pe (env:: (EVar hd) (lem-AEnv-weakening env ((strip' σ₂) cxle-∷ Γ))) e)
pe {Γ = Γ} env (App S _ f e) = (pe env f (cxle-eq Γ)) (pe env e)
pe env (App {α₁} {α₂} D (wf-fun _ _ prf₂ prf₁) f e)
  with lem-IsDynamic-by-wf α₁ prf₁ | lem-IsDynamic-by-wf α₂ prf₂
pe env (App {.(Ann D σ₁)} {.(Ann D σ₂)} D (wf-fun _ _ prf₂ prf₁) f e) | is-dyn σ₁ | is-dyn σ₂ = EApp (pe env f) (pe env e)




