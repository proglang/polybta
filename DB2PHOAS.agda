-----------------------------------------------------
--translation from "De Bruijn" terms to "PHOAS" terms
-----------------------------------------------------
module DB2PHOAS where
open import Lib
open Auxiliaries
open DB&PHOAS

--------------------------------------
--module "PE-DB" 
--note: 
--a)partial evaluation of DB terms;
--b)simpler liftable condition is
--  applied(See Lib.agda for details).
--------------------------------------
module PE-DB where

    ATInt : Ctx → AType → Set
    ATInt Γ (SNum) = ℕ
    ATInt Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (ATInt Γ' α₁ → ATInt Γ' α₂)
    ATInt Γ (D σ) = Exp Γ σ

    int↑ : ∀ {Γ Γ'} α → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α 
    int↑ SNum p v = v
    int↑ (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (lem-↝-trans Γ↝Γ' Γ'↝Γ'') 
    int↑ (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v

    data AEnv (Γ : Ctx) : ACtx → Set where
      [] : AEnv Γ []
      cons : ∀ {Δ} {α : AType} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

    env↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
    env↑ Γ↝Γ' [] = []
    env↑ Γ↝Γ' (cons {α = α} x env) = cons {α = α} (int↑ α Γ↝Γ' x) (env↑ Γ↝Γ' env)

    consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
    consD σ env = (cons {α = D σ} (EVar hd) (env↑ (extend {τ = σ} refl) env))

    lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → ATInt Γ α
    lookup [] ()
    lookup {α} (cons x aenv) hd = x
    lookup {α} (cons x aenv) (tl {.α} {y} id) = lookup aenv id

    mutual 
      Lift : ∀ {Γ α} → liftable1 α → ATInt Γ α → (Exp Γ (typeof α))
      Lift base v = v
      Lift {Γ} {SFun α₁ α₂} (Func l l₁) v = ELam ((λ x → Lift l₁ (v (extend {τ = typeof α₁} refl) x))
                                                  (Embed l (EVar {Γ = typeof α₁ ∷ Γ} hd)))
 
      Embed : ∀ {Γ α} → liftable1 α → Exp Γ (typeof α) → (ATInt Γ α)
      Embed base e = e
      Embed {Γ} {SFun α₁ α₂} (Func l l₁) e = λ Γ↝Γ' v₁ → Embed l₁ (EApp (exp↑ Γ↝Γ' e) (Lift l v₁))

    -------------------------------
    --partial evaluator of DB terms
    -------------------------------
      PE : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → ATInt Γ α
      PE (Var x) env = lookup env x
      PE (SCst x) env = x
      PE (SAdd e e₁) env = PE e env + PE e₁ env
      PE (SLam {α} e) env = λ Γ↝Γ' → λ y → PE e (cons {α = α} y (env↑ Γ↝Γ' env))
      PE (SApp e e₁) env = PE e env refl (PE e₁ env)
      PE (DCst x) env = ECst x
      PE (DAdd e e₁) env = EAdd (PE e env) (PE e₁ env)
      PE (DLam {σ} e) env = ELam (PE e (consD σ env))
      PE (DApp e e₁) env = EApp (PE e env) (PE e₁ env)
      PE (↑ l e) env = Lift l (PE e env) 




--------------------------------------
--module "PE-PHOAS" 
--note: 
--a)partial evaluation of PHOAS terms.
--------------------------------------
module PE-PHOAS where

  atint : (Type → Set) → AType → Set
  atint var SNum = ℕ
  atint var (SFun aty aty₁) = atint var aty → atint var aty₁
  atint var (D x) = exp var x

  data Env (var : Type → Set) : ACtx → Set₁ where
    []   : Env var []
    cons : ∀ {Δ} {α : AType} → atint var α → Env var Δ → Env var (α ∷ Δ)

  lookupenv : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → A ∈ Δ → Env var Δ → atint var A
  lookupenv hd (cons x l) = x
  lookupenv (tl id) (cons x l) = lookupenv id l 

  mutual 
    lift : ∀ {A var} → liftable1 A → atint var A → (exp var (typeof A))
    lift base v = v
    lift {SFun α₁ α₂} {var} (Func l l₁) v = ELam (λ x → lift l₁ (v (embed l (EVar x))))
 
    embed : ∀ {A var} → liftable1 A → exp var (typeof A) → (atint var A)
    embed base e = e
    embed {SFun α₁ α₂} {var} (Func l l₁) e = λ x → embed l₁ (EApp e (lift l x))
 
  ----------------------------------
  --partial evaluator of PHOAS terms
  ----------------------------------
  pe : ∀ {A var} → aexp (atint var) A → atint var A
  pe (Var x) = x
  pe (SCst x) = x
  pe (SAdd e1 e2) = pe e1 + pe e2
  pe (SLam x) = λ v → pe (x v)
  pe (SApp e1 e2) = (pe e1) (pe e2)
  pe (DCst x) = ECst x
  pe (DAdd e1 e2) = EAdd (pe e1) (pe e2)
  pe {D (Fun A2 B)} {var} (DLam x) = ELam (λ v → pe (x (EVar v)))
  pe (DApp e1 e2) = EApp (pe e1) (pe e2)
  pe (↑ l e) = lift l (pe e)




module DB→PHOAS where
  open PE-DB
  open PE-PHOAS

  module examples where
    
    --a. variable
    --suppose that we have [Imp] as the interpreter of annotated types in [de bruijn]

    -- Var hd : aexp [AInt] AInt
    -- Imp Γ AInt = ℕ   (cons 5 [] : AEnv Γ [AInt])
    -- Var 5 : exp (ATInt TInt) AInt

    -- Var hd : aexp [D Int] (D Int)
    -- Imp Γ (D Int) = Exp Γ Int
    -- cons (EInt 5) [] : AEnv Γ [D Int]
    -- Var (ECst 5) : exp (ATInt TInt) (D Int)

    -- Var hd : aexp [D (Fun Int Int)] (D (Fun Int Int))
    -- Imp Γ (D (Fun Int Int)) = Exp Γ (Fun Int Int) (cons (ELam (EVar hd)) [] : AEnv Γ [D (Fun Int Int)])
    -- ATInt TInt (D (Fun Int Int)) = exp TInt (Fun Int Int)
    -- Var (ELam (λ x → EVar x))

    -- Var hd : aexp [AFun AInt AInt] (AFun AInt AInt)
    -- Imp Γ (AFun AInt AInt) = ∀ {Γ'} → Γ↝Γ' → (ℕ → ℕ)
    -- cons (λ {Γ'} → (λ Γ↝Γ' → (λ x → x))) [] : AEnv Γ [AFun AInt AInt] 
    -- ATInt TInt (AFun AInt AInt) = ℕ → ℕ 
    -- Var (λ x → x)

    -- Var hd : aexp [AFun AInt (D Int)] (AFun AInt (D Int))
    -- Imp Γ (AFun AInt (D Int)) = ∀ {Γ'} → Γ↝Γ' → (ℕ → exp Γ Int)
    -- cons (λ Γ↝Γ' → (λ x → EInt 0)) [] : AEnv Γ [AFun AInt (D Int)]
    -- ATInt TInt (AFun AInt (D Int)) = ℕ → exp AInt Int
    -- Var (λ x → SCst 0)

    --b. λ-abstraction

    -- ALam (Var hd) : aexp Γ (AFun AInt AInt)
    -- ATInt TInt AInt → aexp (ATInt TInt) AInt
    -- SLam (λ x → Var x)

    -- DLam (Var hd) : aexp Γ (D (Fun Int Int))
    -- ATInt TInt (D Int) → aexp (ATInt TInt) (D Int)
    -- DLam (λ x → Var x)

    -- ALam (DInt 0) : aexp Γ (AFun AInt (D Int))
    -- ATInt TInt AInt → aexp (ATInt TInt) (D Int) 
    -- SLam (λ x → DCst 0)

    -- ALam (Var hd) : aexp Γ (AFun (D Int) (D Int))
    -- ATInt TInt (D Int) → aexp (ATInt TInt) (D Int) 
    -- SLam (λ x → Var x)

    --c. application

    -- AApp (ALam (Var hd)) (AInt 0) : AExp Δ AInt
    -- SApp (SLam (λ x → Var x))(SCst 0)

    -- AApp (ALam (Var hd)) (DInt 0) : AExp Δ (D Int)
    -- SApp (SLam (λ x → Var x))(DCst 0)

    -- DApp (DLam (Var hd)) (DInt 0) : AExp Δ (D Int)
    -- DApp (DLam (λ x → Var x)) (DCst 0)

    ----------------------------------------------------------------------------
    -- some points regarding the projection function from [de bruijn] to [PHOAS]
    ----------------------------------------------------------------------------
    -- 1. variables 
    -- proj ((Var x) , env ) = Var (process(lookitup x env))  
    -- note that when it comes variables,the first thing to do in [proj] is to 
    -- look up its value in the "environment". After that walk through the value
    -- and modify it as you go alone

    -- 2. functions
    -- proj (ALam (Var hd) , env) = SLam (λ x → proj (Var hd) , x :: env) 
    -- proj (DLam (Var hd) , env) = DLam (λ x → proj (Var hd) , x :: env)
    -- proj (ALam (DInt 0)) , env) = SLam (λ x → proj (DInt 0) , x :: env)

    -- 3. application
    -- proj ((AApp (ALam (Var hd))(AInt 0)) , env) = SApp (proj (ALam (Var hd)) , env) (proj (AInt 0) , env)

  module Proj where

    proj : ∀ {A : AType} {Δ : ACtx} {var : Type → Set}  → AExp Δ A → Env var Δ  → aexp (atint var) A
    proj {A} {Δ} (Var x) env = Var (lookupenv x env)
    proj {SNum} (SCst x) env = SCst x
    proj (SAdd ae ae₁) env = SAdd (proj ae env) (proj ae₁ env)
    proj {SFun α₁ α₂}  (SLam ae) env = SLam (λ x → proj ae (cons x env))
    proj (SApp ae ae₁) env = SApp (proj ae env) (proj ae₁ env)
    proj (DCst x) env = DCst x
    proj (DAdd ae ae₁) env = DAdd (proj ae env) (proj ae₁ env)
    proj {D (Fun τ₁ τ₂)} (DLam ae) env = DLam (λ v → proj ae (cons v env))
    proj (DApp ae ae₁) env = DApp (proj ae env) (proj ae₁ env)
    proj (↑ l e) env = ↑ l (proj e env)
  
  open Proj public



