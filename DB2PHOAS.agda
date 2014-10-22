-----------------------------------------------------
--translation from "De Bruijn" terms to "PHOAS" terms
-----------------------------------------------------
module DB2PHOAS where
open import Lib
open Auxiliaries
open DB&PHOAS
open import Types
open two-level-types-simp


--------------------------
--two-level-terms-DB&PHOAS
--------------------------
-------------------
--"De Bruijn" terms
-------------------
module DB-Terms where
  
  data Exp (Γ : Ctx) : Type → Set where
    EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
    ECst : ℕ → Exp Γ Num
    EAdd : Exp Γ Num → Exp Γ Num -> Exp Γ Num
    ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
    EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'
   
  module liftable where
      
    typeof : AType → Type
    typeof SNum = Num
    typeof (SFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
    typeof (D x) = x

    -----------------------------------
    --a less powerful lifting criterion
    -----------------------------------
    data liftable1 : AType → Set where
      base : ∀ {x : Type} → liftable1 (D x)
      Func : ∀ {α₁ α₂ : AType} 
              → liftable1 α₁ → liftable1 α₂
              → liftable1 (SFun α₁ α₂)

    ---------------------------------------------
    --[liftable] in [BTA9] without pairs and sums
    ---------------------------------------------
    mutual 
      data Liftable2 : AType → Set where
        D : ∀ τ → Liftable2 (D τ)
        SCst : Liftable2 SNum
        SFun : ∀ {α₁ α₂} → Liftable2⁻ α₁ → Liftable2 α₂ → Liftable2 (SFun α₁ α₂)

      data Liftable2⁻ : AType → Set where
        D : ∀ τ → Liftable2⁻ (D τ)
        SFun : ∀ {α₁ α₂} → Liftable2 α₁ → Liftable2⁻ α₂ → Liftable2⁻ (SFun α₁ α₂)
   
  open liftable public


  data AExp (Δ : ACtx) : AType → Set where
    Var : ∀ {α} → α ∈ Δ → AExp Δ α
    SCst : ℕ → AExp Δ SNum
    SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
    SLam : ∀ {α₁ α₂}   → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
    SApp : ∀ {α₁ α₂}   → AExp Δ (SFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
    DCst : ℕ → AExp Δ (D Num)
    DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
    DLam : ∀ {τ₁ τ₂}   → AExp ((D τ₁) ∷ Δ) (D τ₂) → AExp Δ (D (Fun τ₁ τ₂))
    DApp : ∀ {τ₁ τ₂}   → AExp Δ (D (Fun τ₂ τ₁)) → AExp Δ (D τ₂) → AExp Δ (D τ₁)
    ↑    : ∀  {α} → liftable1 α → AExp Δ α → AExp Δ (D (typeof α))

open DB-Terms public
  
---------------
--"PHOAS" terms
---------------
module PHOAS-Terms where
 

  data exp (var : Type → Set) : Type → Set where
    EVar : ∀ {A} → var A → exp var A
    ECst : ℕ → exp var Num
    EAdd : exp var Num → exp var Num → exp var Num
    ELam : ∀ {A B} → (var A → exp var B) → exp var (Fun A B)
    EApp : ∀ {A B} → exp var (Fun A B) → exp var A → exp var B

  data aexp (var : AType → Set) : AType → Set where
    Var  : ∀ {A} → var A → aexp var A
    SCst : ℕ → aexp var SNum
    SAdd : aexp var SNum → aexp var SNum → aexp var SNum
    SLam : ∀ {A B} → (var A → aexp var B) → aexp var (SFun A B)
    SApp : ∀ {A B} → aexp var (SFun A B) → aexp var A → aexp var B
    DCst : ℕ → aexp var (D Num)
    DAdd : aexp var (D Num) → aexp var (D Num) → aexp var (D Num)
    DLam : ∀ {a b} → (var (D a) → aexp var (D b)) → aexp var (D (Fun a b))
    DApp : ∀ {a b} → aexp var (D (Fun a b)) → aexp var (D a) → aexp var (D b)
    ↑    : ∀  {α} → liftable1 α → aexp var α → aexp var (D (typeof α))
  
open PHOAS-Terms public


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
    elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
    elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (extend Γ↝Γ'↝Γ'') e)
    elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)

    exp↑ : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
    exp↑ Γ↝Γ' e = elevate (refl Γ↝Γ') e


    int↑ : ∀ {Γ Γ'} α → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α 
    int↑ SNum p v = v
    int↑ (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (lem-↝-trans Γ↝Γ' Γ'↝Γ'') 
    int↑ (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v

    data AEnv (Γ : Ctx) : ACtx → Set where
      [] : AEnv Γ []
      _∷_ : ∀ {Δ} {α : AType} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

    env↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
    env↑ Γ↝Γ' [] = []
    env↑ Γ↝Γ' (_∷_ {α = α} x env) = _∷_ {α = α} (int↑ α Γ↝Γ' x) (env↑ Γ↝Γ' env)

    consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
    consD σ env = (_∷_ {α = D σ} (EVar hd) (env↑ (extend {τ = σ} refl) env))

    lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → ATInt Γ α
    lookup [] ()
    lookup {α} (x ∷ aenv) hd = x
    lookup {α} (x ∷ aenv) (tl {.α} {y} id) = lookup aenv id

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
      PE (SLam {α} e) env = λ Γ↝Γ' → λ y → PE e (_∷_ {α = α} y (env↑ Γ↝Γ' env))
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
    _∷_ : ∀ {Δ} {α : AType} → atint var α → Env var Δ → Env var (α ∷ Δ)

  lookupenv : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → A ∈ Δ → Env var Δ → atint var A
  lookupenv hd (x ∷ l) = x
  lookupenv (tl id) (x ∷ l) = lookupenv id l 

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
    proj {SFun α₁ α₂}  (SLam ae) env = SLam (λ x → proj ae (x ∷ env))
    proj (SApp ae ae₁) env = SApp (proj ae env) (proj ae₁ env)
    proj (DCst x) env = DCst x
    proj (DAdd ae ae₁) env = DAdd (proj ae env) (proj ae₁ env)
    proj {D (Fun τ₁ τ₂)} (DLam ae) env = DLam (λ v → proj ae (v ∷ env))
    proj (DApp ae ae₁) env = DApp (proj ae env) (proj ae₁ env)
    proj (↑ l e) env = ↑ l (proj e env)
  
  open Proj public



