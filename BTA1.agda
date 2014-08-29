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

open import Data.Nat
open import Data.Bool
open import Data.List
--open import Lib 

-- Binding times
data BT : Set where
  S : BT
  D : BT


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

infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈ (x ∷ xs)
  tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)


-----------
-- Sublists
-----------


data _↝_ {A : Set} : List A → List A → Set where
  refl   : {l : List A} → l ↝ l
  extend : ∀ {l₁ l₂ τ}  → l₁ ↝ l₂ → l₁ ↝ (τ ∷ l₂)



lem-↝-trans : {A : Set} → {l₁ : List A} {l₂ : List A} {l₃ : List A} →
                 l₁ ↝ l₂ → l₂ ↝ l₃ → l₁ ↝ l₃
lem-↝-trans le1  refl = le1
lem-↝-trans refl (extend e) = extend e
lem-↝-trans (extend e) (extend e') = extend (lem-↝-trans (extend e) e') 



_↝-∷_ : {A : Set} (x : A) (l : List A) → l ↝ (x ∷ l)
x ↝-∷ l = extend refl



data _↝_↝_ {A : Set} : List A → List A → List A → Set where
  refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ''
  extend : ∀ {Γ Γ' Γ'' τ} →
             Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'')

_⊕_ : ∀ {A : Set}{Γ Γ' Γ'' : List A} → 
        Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
_⊕_ Γ↝Γ' refl = Γ↝Γ'                                 
_⊕_ Γ↝Γ' (extend Γ'↝Γ'') = extend (Γ↝Γ' ⊕ Γ'↝Γ'')


---------------
-- end Sublists
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
  -- [EVar] corresponds to the bounded variables in [AExp]
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ TNum
  ELam : ∀ {τ₁ τ₂} → Exp (τ₂ ∷ Γ) τ₁ → Exp Γ (TFun τ₂ τ₁)
  EApp : ∀ {τ₁ τ₂} → Exp Γ (TFun τ₂ τ₁) → Exp Γ τ₂ → Exp Γ τ₁



elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var refl τ∈Γ = τ∈Γ
elevate-var (extend Γ↝Γ') τ∈Γ = tl (elevate-var Γ↝Γ' τ∈Γ)



elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ'' 
elevate-var2 (refl x) x₁ = elevate-var x x₁
elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)


elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (ECst x) = ECst x
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)



exp↑ : ∀ {τ τ' Γ} → Exp Γ τ' → Exp (τ ∷ Γ) τ'
exp↑ e = elevate (refl (extend refl)) e



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
  impTA' Γ (SFun y y') = ∀ {Γ'} → Γ ↝ Γ' → impTA Γ' y → impTA Γ' y'


int↑ : ∀ { α Γ Γ'} → Γ ↝ Γ' → impTA Γ α → impTA Γ' α
int↑ refl e = e
int↑ {Ann S SNum} (extend Γ↝Γ') e = e
int↑ {Ann S (SFun x x₁)} {Γ} {τ ∷ Γ'} (extend {.Γ} {.Γ'} {.τ} Γ↝Γ') e = λ Γ'↝Γ'' x₂ → e ((Γ↝Γ' ⊕ (τ ↝-∷ Γ')) ⊕ Γ'↝Γ'') x₂
int↑ {Ann D x₁} {Γ} {τ ∷ Γ'} (extend {.Γ} {.Γ'} {.τ} Γ↝Γ') e = exp↑ (int↑ {Ann D x₁} Γ↝Γ' e)



data AEnv : Ctx → ACtx → Set where
  env[] :  ∀ {Γ} → AEnv Γ []
  envS:: : ∀ {Γ Δ} {α} →
           impTA Γ α → 
           AEnv Γ Δ →
           AEnv Γ (α ∷ Δ)
  envD:: : ∀ {Γ Δ} →
           (σ : SType) →
           impTA (strip' σ ∷ Γ) (Ann D σ) →
           AEnv Γ Δ →
           AEnv (strip' σ ∷ Γ) (Ann D σ ∷ Δ)



env↑ : ∀ { Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ _ env[] = env[]
env↑ Γ↝Γ' (envS:: {α = α} x env) = envS:: (int↑ {α} Γ↝Γ' x) (env↑ Γ↝Γ' env)
env↑ Γ↝Γ' (envD:: {Γ} σ x env) = envS:: (int↑ {Ann D σ} Γ↝Γ' x) (env↑ ((strip' σ ↝-∷ Γ) ⊕ Γ↝Γ') env)



lookup : ∀ {Γ Δ α} → α ∈ Δ → AEnv Γ Δ → impTA Γ α
lookup () env[] 
lookup hd (envS:: x env) = x
lookup (tl idx) (envS:: x env) = lookup idx env 
lookup hd (envD:: σ x env) = x 
lookup {α = α} (tl idx) (envD:: {Γ} σ x env) = int↑ {α} ((strip' σ) ↝-∷ Γ) (lookup idx env)  

data IsDynamic : AType → Set where
  is-dyn : ∀ σ → IsDynamic (Ann D σ)

lem-IsDynamic-by-wf : ∀ α → isTrue (D ≼ btof α) → IsDynamic α
lem-IsDynamic-by-wf (Ann S σ) ()
lem-IsDynamic-by-wf (Ann D σ) _ = is-dyn σ 




pe : ∀ {Δ Γ α} → AEnv Γ Δ → AExp Δ α → impTA Γ α
pe env (Var idx) = lookup idx env
pe env (Cst S i) = i
pe env (Cst D i) = ECst i
pe {Γ = Γ} env (Lam {α₁} {α₂} S prf exp) = λ {Γ'} (prf₁ : Γ ↝ Γ') (v : impTA Γ' α₂) →
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
