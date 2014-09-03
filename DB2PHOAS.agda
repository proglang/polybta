--a)translation from "De Bruijn" terms to "PHOAS" terms
--b)correctness proof of the translation
module DB2PHOAS where
open import Data.Nat hiding  (_<_;_⊔_;_*_;equal)
open import Data.Bool hiding (_∨_) 
open import Function using (_∘_)
open import Data.List
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 
open import Data.Empty
open import Data.Product
open import Data.Sum



infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
    hd : ∀ {x xs} → x ∈ (x ∷ xs)
    tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)


  -- Extension of a list by consing elements at the front. 
data _↝_ {A : Set} : List A → List A → Set where
    refl   : ∀ {Γ}      → Γ ↝ Γ
    extend : ∀ {Γ Γ' τ} → Γ ↝ Γ' → Γ ↝ (τ ∷ Γ')
  
  -- Combining two transitive extensions. 
lem-↝-trans : ∀ {A : Set}{Γ Γ' Γ'' : List A} → Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
lem-↝-trans Γ↝Γ' refl = Γ↝Γ'
lem-↝-trans Γ↝Γ' (extend Γ'↝Γ'') = extend (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
  
  -- Of course, ↝-refl is the identity for combining two extensions.
lem-↝-refl-id : ∀ {A : Set} {Γ Γ' : List A} →
                    (Γ↝Γ' : Γ ↝ Γ') →
                    Γ↝Γ' ≡ (lem-↝-trans refl Γ↝Γ')  
lem-↝-refl-id refl = refl
lem-↝-refl-id (extend Γ↝Γ') = cong extend (lem-↝-refl-id Γ↝Γ')

  -- Extending a list in the middle: 
data _↝_↝_ {A : Set} : List A → List A → List A → Set where
    -- First prepend the extension list to the common suffix
    refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ'' 
    -- ... and then add the common prefix
    extend : ∀ {Γ Γ' Γ'' τ} →
                 Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'') 


----------------------
--residual type [Type]
----------------------
data Type : Set where
  Num : Type
  Fun : Type → Type → Type

----------------------------------
--annotated two-level type [AType]
----------------------------------
data AType : Set where
  SNum : AType
  SFun : AType → AType → AType
  D    : Type → AType





----------------------
--higher order lifting
----------------------
typeof : AType → Type
typeof SNum = Num
typeof (SFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
typeof (D x) = x


----------------
--liftable types
----------------
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

-----------
--de bruijn
-----------
---------------------
--residual expression
---------------------
Ctx = List Type

data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ Num
  EAdd : Exp Γ Num → Exp Γ Num -> Exp Γ Num
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'

--------------------------------
--two-level annotated expression
--------------------------------
ACtx = List AType

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

----------------------------
-- The interpreter of [Type]
----------------------------
TInt : Type → Set
TInt Num = ℕ
TInt (Fun ty ty₁) = TInt ty → TInt ty₁



-----------------------------
-- The interpreter of [AType]
-----------------------------
ATInt : Ctx → AType → Set
ATInt Γ (SNum) = ℕ
ATInt Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (ATInt Γ' α₁ → ATInt Γ' α₂)
ATInt Γ (D σ) = Exp Γ σ

-------------
--environment
-------------
data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  cons : ∀ {Δ} {α : AType} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)


-------
--PHOAS
-------
---------------
--residual term
---------------
data exp (var : Type → Set) : Type → Set where
  EVar : ∀ {A} → var A → exp var A
  ECst : ℕ → exp var Num
  EAdd : exp var Num → exp var Num → exp var Num
  ELam : ∀ {A B} → (var A → exp var B) → exp var (Fun A B)
  EApp : ∀ {A B} → exp var (Fun A B) → exp var A → exp var B

--------------------------
--annotated two-level term
--------------------------
data aexp (var : AType → Set) : AType → Set where
  Var  : ∀ {A} → var A → aexp var A
--static expression
  SCst : ℕ → aexp var SNum
  SAdd : aexp var SNum → aexp var SNum → aexp var SNum
  SLam : ∀ {A B} → (var A → aexp var B) → aexp var (SFun A B)
  SApp : ∀ {A B} → aexp var (SFun A B) → aexp var A → aexp var B
--dynamic expression
  DCst : ℕ → aexp var (D Num)
  DAdd : aexp var (D Num) → aexp var (D Num) → aexp var (D Num)
  DLam : ∀ {a b} → (var (D a) → aexp var (D b)) → aexp var (D (Fun a b))
  DApp : ∀ {a b} → aexp var (D (Fun a b)) → aexp var (D a) → aexp var (D b)
  ↓    : ∀  {α} → liftable1 α → aexp var α → aexp var (D (typeof α))

-----------------------
--interpreter of [Type]
-----------------------
tint : Type → Set
tint Num = ℕ
tint (Fun ty ty₁) = tint ty → tint ty₁

------------------------
--interpreter of [AType]
------------------------
atint : (Type → Set) → AType → Set
atint var SNum = ℕ
atint var (SFun aty aty₁) = atint var aty → atint var aty₁
atint var (D x) = exp var x

-----------------------------------------
--from [De Bruijn] to [PHOAS]
--[proj]
-----------------------------------------
----------------
--some instances
----------------
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

---------------------
--projection function
---------------------

----------------------------
--redefining the environment
----------------------------
data Env (var : Type → Set) : ACtx → Set₁ where
  []   : Env var []
  cons : ∀ {Δ} {α : AType} → atint var α → Env var Δ → Env var (α ∷ Δ)

-----------------------
--some auxiliary lemmas
-----------------------
lookupenv : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → A ∈ Δ → Env var Δ → atint var A
lookupenv hd (cons x l) = x
lookupenv (tl id) (cons x l) = lookupenv id l 



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
proj (↑ l e) env = ↓ l (proj e env)


----------------------------------
--auxiliary functions for shifting
----------------------------------
lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → ATInt Γ α
lookup [] ()
lookup {α} (cons x aenv) hd = x
lookup {α} (cons x aenv) (tl {.α} {y} id) = lookup aenv id


elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var refl x = x
elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)


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

liftE : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
liftE Γ↝Γ' e = elevate (refl Γ↝Γ') e


lift : ∀ {Γ Γ'} α → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α 
lift SNum p v = v
lift (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
lift (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v


liftEnv : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
liftEnv Γ↝Γ' [] = []
liftEnv Γ↝Γ' (cons {α = α} x env) = cons {α = α} (lift α Γ↝Γ' x) (liftEnv Γ↝Γ' env)

consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
consD σ env = (cons {α = D σ} (EVar hd) (liftEnv (extend {τ = σ} refl) env))
-----
--end
----- 
------------------------------------
--[lift'] and [embed] in [De Bruijn] 
------------------------------------
mutual 
  Lift' : ∀ {Γ α} → liftable1 α → ATInt Γ α → (Exp Γ (typeof α))
  Lift' base v = v
  Lift' {Γ} {SFun α₁ α₂} (Func l l₁) v = ELam ((λ x → Lift' l₁ (v (extend {τ = typeof α₁} refl) x))
                                                 (Embed l (EVar {Γ = typeof α₁ ∷ Γ} hd)))
 
  Embed : ∀ {Γ α} → liftable1 α → Exp Γ (typeof α) → (ATInt Γ α)
  Embed base e = e
  Embed {Γ} {SFun α₁ α₂} (Func l l₁) e = λ Γ↝Γ' v₁ → Embed l₁ (EApp (liftE Γ↝Γ' e) (Lift' l v₁))

------------------------------------
--[lift'] and [embed] in [PHOAS] 
------------------------------------
mutual 
  lift' : ∀ {A var} → liftable1 A → atint var A → (exp var (typeof A))
  lift' base v = v
  lift' {SFun α₁ α₂} {var} (Func l l₁) v = ELam (λ x → lift' l₁ (v (embed l (EVar x))))
 
  embed : ∀ {A var} → liftable1 A → exp var (typeof A) → (atint var A)
  embed base e = e
  embed {SFun α₁ α₂} {var} (Func l l₁) e = λ x → embed l₁ (EApp e (lift' l x))

----------------------------------------------------------------------------------------------------

PE : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → ATInt Γ α
PE (Var x) env = lookup env x
PE (SCst x) env = x
PE (SAdd e e₁) env = PE e env + PE e₁ env
PE (SLam {α} e) env = λ Γ↝Γ' → λ y → PE e (cons {α = α} y (liftEnv Γ↝Γ' env))
PE (SApp e e₁) env = PE e env refl (PE e₁ env)
PE (DCst x) env = ECst x
PE (DAdd e e₁) env = EAdd (PE e env) (PE e₁ env)
PE (DLam {σ} e) env = ELam (PE e (consD σ env))
PE (DApp e e₁) env = EApp (PE e env) (PE e₁ env)
PE (↑ l e) env = Lift' l (PE e env) 


-----------------------------
--partial evaluator of [aexp]
-----------------------------
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
pe (↓ l e) = lift' l (pe e)

--------------------------------------------
--projection from [Imp Γ A] to [ATInt var A]
--------------------------------------------
---------------------------------
--consider the following examples
---------------------------------
--a. A = AInt , Imp Γ AInt = ℕ , ATInt var AInt = ℕ
--[5 : ℕ] to [5 : ℕ]

--b. A = AFun AInt AInt , Imp Γ (AFun AInt AInt) = ℕ → ℕ 
--                      , ATInt var (AFun AInt AInt) = ℕ → ℕ
--[λ x → x : ℕ → ℕ] to [λ x → x : ℕ → ℕ]

--c. A = D Int , Imp Γ (D Int) = Exp Γ Int , ATInt var (D Int) = exp var Int
--[EInt x : Exp Γ Int] to [ECst x : exp var Int]

--d. A = D (Fun Int Int) , Imp Γ (D (Fun Int Int)) = Exp Γ (Fun Int Int)
--                       , ATInt var (D (Fun Int Int)) = exp var (Fun Int Int)
--[ELam (EVar hd) : Exp Γ (Fun Int Int)] to [ELam (EVar hd) : exp Γ (Fun Int Int)]

--e. A = AFun AInt (D Int) , Imp Γ (AFun AInt (D Int)) = ℕ → Exp Γ Int 
--                         , ATInt var (AFun AInt (D Int)) = ℕ → exp var Int
--[λ x → EInt x : ℕ → Exp Γ Int] → [λ x → ECst x : ℕ → exp var Int]

--------------------------
--some auxiliary functions
--------------------------
----------------------------------------------------------
--now we have to redefine the environment [Env] as follows
----------------------------------------------------------
data env (var : Type → Set) : Ctx → Set₁ where
  []   : env var []
  cons : ∀ {Γ} {α : Type} → var α → env var Γ → env var (α ∷ Γ)

-----------------------
--some auxiliary lemmas
-----------------------
lookuprenv : ∀ {a : Type} {Γ} {var : Type → Set} → a ∈ Γ → env var Γ → var a
lookuprenv hd (cons x env) = x
lookuprenv (tl id) (cons x env) = lookuprenv id env


------------------------------------
--now a proof that [proj] is correct
------------------------------------
----------
--analysis
----------
--a. [AInt]
--a.1. variable
--[proj] : from [De Bruijn] to [PHOAS]
-- Var hd : AExp [AInt] AInt
-- Imp Γ AInt = ℕ   (cons 5 [] : AEnv Γ [AInt])
-- Var 5 : aexp (ATInt TInt) AInt
--proj (Var hd) (cons 5 []) = Var 5

--[PE] and [pe] : partial evaluation of respective expressions
--PE (Var hd) (cons 5 []) = 5 : ℕ
--pe (Var 5) = 5 : ℕ

--conclusion : PE (Var hd)(cons 5 []) = pe (proj (Var hd)(cons 5 []))

--a.2. constant
--[proj]
--AInt x : AExp Δ AInt
--Imp Γ AInt = ℕ (env : AEnv Γ Δ)
--SCst x : aexp (ATInt TInt) AInt
--proj (AInt x) env' = SCst x 

--[PE] and [pe] 
--PE (AInt x) env = x : ℕ
--pe (SCst x) = x : ℕ

--conclusion : PE (AInt x) env = pe (proj (AInt x) env')
--note that [env' : Env var Δ] corresponds to [env : AEnv Γ Δ]


--a.3. application
--[proj]
--AApp (ALam (Var hd))(AInt x) : AExp Δ AInt
--Imp Γ (AFun AInt AInt) = ∀ {Γ'} → Γ↝Γ' → ℕ → ℕ (env : AEnv Γ Δ)
--SLam (λ x → Var x) : aexp (ATInt TInt) (AFun AInt AInt) 
--SApp (SLam (λ x → Var x)) (SCst x) : aexp (ATInt TInt) AInt
--proj (AApp (ALam (Var hd))(AInt x)) env' = SApp (SLam (λ x → Var x))(SCst x)

--[PE] and [pe]
--PE (AApp (ALam (Var hd))(AInt x)) env = x : ℕ
--pe (SApp (SLam (λ x → Var x))(SCst x)) = x : ℕ

--conclusion : PE (AApp (ALam (Var hd))(AInt x)) env = pe (proj (AApp (ALam (Var hd))(AInt x)) env')

--b. [AFun AInt AInt]
--b.1. variable
--[proj]
--Var hd : AExp [AFun AInt AInt] (AFun AInt AInt)
--Imp Γ (AFun AInt AInt) = ∀ {Γ'} → Γ↝Γ' → ℕ → ℕ (cons (λ {Γ'} → (λ Γ↝Γ' → (λ x → x))) [] : AEnv Γ [AFun AInt AInt])
--Var (λ x → x) : aexp (ATInt AInt) (AFun AInt AInt)   
--proj (Var hd) env = Var (λ x → x) 

--[PE] and [pe]
--PE (Var hd) env = λ {Γ'} → (λ Γ↝Γ' → (λ x → x)) ≡ f1 : {Γ Γ' : Exp} → (Γ ↝ Γ') → (ℕ → ℕ) 
--pe (Var (λ x → x)) = λ x → x ≡ f2 : ℕ → ℕ

--conclusion : forall v :ℕ, f1  ↝-refl v = f2 v

--c. [AFun (D Int) AInt]
--c.1 λ-abstraction
--[proj]
--ALam ((AInt x)) : AExp Δ (AFun (D Int) AInt)
--Imp Γ (AFun (D Int) AInt) = ∀ {Γ'} → Γ↝Γ' → ((Exp Γ' Int) → ℕ)
--SLam (λ v → SCst x) : aexp (ATInt TInt) (AFun (D Int) AInt)
--proj (ALam (AInt x)) env' = SLam (λ v → SCst x)

--[PE] and [pe]
--PE (ALam (AInt x)) env = λ {Γ'} → (λ Γ↝Γ' → (λ v → x)) ≡ f1 : {Γ Γ' : Exp} → (Γ ↝ Γ') → (Exp Γ' AInt → ℕ) 
--pe (SLam (λ v → SCst x)) = λ v → x ≡ f2 : exp TInt Int → ℕ

--conclusion : forall v:Exp Γ' AInt and v':exp TInt Int such that v ∽ v' then
--f1 v ∽ f2 v'

--d. [D Int]
--d.1. variable
--[proj]
--Var hd : AExp [D Int] (D Int)
--Imp Γ (D Int) = Exp Γ Int (cons (EInt 0) [] : AEnv Γ [D Int])
--ECst 0 : exp TInt Int
--proj (Var hd) env' = Var (ECst 0)

--[PE] and [pe]
--PE (Var hd) (cons (EInt 0) []) = EInt 0 : Exp Γ Int
--pe (Var (ECst 0)) = ECst 0 : exp TInt Int

--conclusion: Exp2exp (EInt 0) env'' = ECst 0 where env'' defined as [env]
--which can be considered as the environment [AEnv] after the partial evaluation

--d.2. constant
--[proj]
--DInt 0 : AExp Δ (D Int) 
--Imp Γ (D Int) = Exp Γ Int 
--DCst 0 : aexp (ATInt TInt) (D Int)
--proj (DInt 0) env' = DCst 0

--[PE] and [pe]
--PE (DInt 0) env = EInt 0 : Exp Γ Int
--pe (DCst 0) = ECst 0 : exp TInt Int

--conclusion : Exp2exp (EInt 0) env'' = ECst 0


--e. [D (Fun Int Int)]
--e.1 λ-abstraction
--DLam (Var hd) : AExp Δ (D (Fun Int Int))
--Imp Γ (D (Fun Int Int)) = Exp Γ (Fun Int Int)
--DLam (λ x → Var x) : aexp (ATInt TInt) (D (Fun Int Int))
--proj (DLam (Var hd)) env = DLam (λ x → Var x)

--[PE] and [pe]
--PE (DLam (Var hd)) env = ELam (EVar hd) : Exp Γ (Fun Int Int)
--pe (DLam (λ x → Var x)) = ELam (λ x → EVar x) : exp TInt (Fun Int Int)

--conclusion : Exp2exp (ELam (EVar hd)) env'' = ELam (λ x → EVar x)


------------------------
--now redefine [Similar]
------------------------
--------------------------
--some auxiliary functions
--------------------------
Γ2Ctx : ∀ {var₁ : Type → Set} {var₂ : Type → Set} → (Γ : List (Σ[ A ∈ Type ] (var₁ A × var₂ A))) → Ctx
Γ2Ctx [] = []
Γ2Ctx ((proj₁ , x) ∷ Γ) = proj₁ ∷ Γ2Ctx Γ

Γ2en₁ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} → (Γ : List (Σ[ A ∈ Type ] (var₁ A × var₂ A))) → List (Σ[ A ∈ Type ] (var₁ A))
Γ2en₁ [] = []
Γ2en₁ ((proj₁ , proj₂ , proj₃) ∷ Γ) = (proj₁ , proj₂) ∷ Γ2en₁ Γ

en₁2Ctx : ∀ {var : Type → Set} → (Γ : List (Σ[ A ∈ Type ] (var A))) → Ctx
en₁2Ctx [] = []
en₁2Ctx ((proj₁ , proj₂) ∷ en₁) = proj₁ ∷ en₁2Ctx en₁

----------------------------------------
--redefine [Exp2exp] or [en : env var Γ]
----------------------------------------
Exp2exp : ∀ {a} {var : Type → Set} → 
             (Γ : List (Σ[ A ∈ Type ] (var A))) →
             Exp (en₁2Ctx Γ) a →
             exp var a 
Exp2exp [] (EVar ())
Exp2exp ((proj₁ , proj₂) ∷ Γ) (EVar hd) = EVar proj₂
Exp2exp ((proj₁ , proj₂) ∷ Γ) (EVar (tl x₁)) = Exp2exp Γ (EVar x₁)
Exp2exp Γ (ECst x) = ECst x
Exp2exp Γ (EAdd e e₁) = EAdd (Exp2exp Γ e) (Exp2exp Γ e₁)
Exp2exp {Fun A B} {var} Γ (ELam e) = ELam (λ v → Exp2exp {B} ((A , v) ∷ Γ) e)
Exp2exp Γ (EApp e e₁) = EApp (Exp2exp Γ e) (Exp2exp Γ e₁)           

Exp2expELam≡ : ∀ {A B var Γ} {e : Exp (A ∷ en₁2Ctx Γ) B} →
           Exp2exp {Fun A B} {var} Γ (ELam e) ≡ ELam (λ v → Exp2exp {B} ((A , v) ∷ Γ) e)
Exp2expELam≡ {A} {B} {var} {[]} = λ {e} → refl
Exp2expELam≡ {A} {B} {var} {x ∷ Γ} = λ {e} → refl 

Exp2expEApp≡ : ∀ {A B var Γ} {f : Exp (en₁2Ctx Γ) (Fun A B)} {e : Exp (en₁2Ctx Γ) A} →
           Exp2exp {B} {var} Γ (EApp f e) ≡ EApp (Exp2exp Γ f) (Exp2exp Γ e)
Exp2expEApp≡ {A} {B} {var} {[]} {f} {e} = refl
Exp2expEApp≡ {A} {B} {var} {x ∷ Γ} {f} {e} = refl 

data similar-Exp {var₁ var₂} (Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A))))
     : ∀ {A} → exp var₁ A → exp var₂ A → Set where
  similar-EVar  : ∀ {A x₁ x₂} → (A , x₁ , x₂) ∈ Γ → similar-Exp Γ (EVar x₁) (EVar x₂)
  similar-ECst  : ∀ {n} → similar-Exp Γ (ECst n) (ECst n)
  similar-EAdd  : ∀ {a₁ a₂ b₁ b₂} → similar-Exp Γ a₁ b₁ → similar-Exp Γ a₂ b₂ → similar-Exp Γ (EAdd a₁ a₂) (EAdd b₁ b₂)
  similar-ELam  : ∀ {A B} {f₁ : var₁ A → exp var₁ B} {f₂ : var₂ A → exp var₂ B} →
                  (∀ (v₁ : var₁ A) → (v₂ : var₂ A) → similar-Exp ((A , v₁ , v₂) ∷ Γ) (f₁ v₁) (f₂ v₂) ) →
                  similar-Exp Γ (ELam f₁) (ELam f₂)
  similar-EApp  : ∀ {A B} {f₁ : exp var₁ (Fun A B)} {f₂ : exp var₂ (Fun A B)} {a₁ : exp var₁ A} {a₂ : exp var₂ A} →
                  similar-Exp Γ f₁ f₂ → similar-Exp Γ a₁ a₂ →
                  similar-Exp Γ (EApp f₁ a₁) (EApp f₂ a₂)


Γ2Ctx≡ : ∀ {var₁ var₂} {Γ :  List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} → en₁2Ctx (Γ2en₁ {var₁} {var₂} Γ) ≡ Γ2Ctx Γ
Γ2Ctx≡ {var₁} {var₂} {[]} = refl
Γ2Ctx≡ {var₁} {var₂} {x ∷ Γ} rewrite Γ2Ctx≡ {Γ = Γ} = refl 

data _⊂_ {A : Set} : List A → List A → Set where
  extend-hd  : ∀ {Γ Γ'} → Γ ↝ Γ' → Γ ⊂ Γ'
  extend-mid : ∀ {Γ Γ' τ} → Γ ⊂ Γ' → (τ ∷ Γ) ⊂ (τ ∷ Γ')



etG2S : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
          {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
           Γ ↝ Γ' →
          en₁2Ctx (Γ2en₁ Γ) ↝ en₁2Ctx (Γ2en₁ Γ')
etG2S refl = refl
etG2S (extend etG) = extend (etG2S etG)

etG2S' : ∀ {var : Type → Set} 
          {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ' : List (Σ[ A ∈ Type ] (var A))} →
           Γ ↝ Γ' →
          en₁2Ctx Γ ↝ en₁2Ctx Γ'
etG2S' refl = refl
etG2S' (extend etG) = extend (etG2S' etG)

etG2S'' : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
          {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
           Γ ↝ Γ' →
          Γ2en₁ Γ ↝ Γ2en₁ Γ'
etG2S'' refl = refl
etG2S'' (extend etG) = extend (etG2S'' etG)

etG2S≡ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
          {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
          {et : Γ ↝ Γ'} → 
           etG2S et ≡  etG2S' (etG2S'' et)
etG2S≡ {var₁} {var₂} {.Γ'} {Γ'} {refl} = refl
etG2S≡ {var₁} {var₂} {Γ} {(τ ∷ Γ')} {extend et} = cong extend this 
   where this : (etG2S et) ≡ (etG2S' (etG2S'' et))
         this  rewrite etG2S≡ {var₁} {var₂} {Γ} {Γ'} {et} = refl
   


etG2S-trans≡ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
                {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                {Γ'' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                {et : Γ ↝ Γ'} {et₁ : Γ' ↝ Γ''} →
                lem-↝-trans (etG2S et) (etG2S et₁) ≡ etG2S (lem-↝-trans et et₁)
etG2S-trans≡ {var₁} {var₂} {Γ} {.Γ''} {Γ''} {et} {refl} = refl
etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {(τ ∷ Γ'')} {et} {extend et₁} = cong extend this
       where this : (lem-↝-trans (etG2S et) (etG2S et₁)) ≡ (etG2S (lem-↝-trans et et₁))
             this rewrite etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {Γ''} {et} {et₁} = refl 
                  

Similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set}  → (Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))) → ATInt (en₁2Ctx (Γ2en₁ Γ)) A → 
            atint var₂ A → Set
Similar {SNum} Γ e e' = e ≡ e'
Similar {SFun A A₁} {var₁} {var₂} Γ e e' = {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {v : ATInt (en₁2Ctx (Γ2en₁ {var₁} {var₂} Γ')) A} 
                                           {v' : atint var₂ A} →
                                           (et : Γ ↝ Γ') →
                                           Similar Γ' v v' → Similar Γ' (e (etG2S et) v) (e' v')
Similar {D x} Γ e e' = similar-Exp Γ (Exp2exp (Γ2en₁ Γ) e) e'
    

data similar-env {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
     : ∀ {Δ : ACtx} → AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ → Env var₂ Δ → Set₁ where
 []    : similar-env [] [] 
 scons  : ∀ {A : AType} {Δ : ACtx} {e : ATInt (en₁2Ctx (Γ2en₁ Γ)) A} {e' : atint var₂ A} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} {en : Env var₂ Δ} 
          → Similar Γ e e'  → similar-env {var₁} {var₂} {Γ} {Δ} aen en → similar-env (cons e aen) (cons e' en)



id-extend : ∀ {A : Set} {a : A} {b : A} {Γ : List A} → a ∈ Γ → a ∈ (b ∷ Γ)
id-extend hd = tl hd
id-extend (tl a∈Γ) = tl (tl a∈Γ)

-----------------------------------------
--some auxiliary lemmas regarding lemma1≡
-----------------------------------------

Exp2exp-EInt≡ : ∀ {n} {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} → 
                  Exp2exp Γ (ECst n) ≡ ECst n
Exp2exp-EInt≡ {n} {var} {[]} = refl
Exp2exp-EInt≡ {n} {var} {x ∷ Γ} = refl

Exp2exp-EAdd≡ : ∀ {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} {e e₁} → 
                  Exp2exp Γ (EAdd e e₁) ≡ EAdd (Exp2exp Γ e) (Exp2exp Γ e₁)
Exp2exp-EAdd≡ {var} {[]} {e} {e₁} = refl
Exp2exp-EAdd≡ {var} {x ∷ Γ} = refl

Exp2exp-ELam≡ : ∀ {A B} {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} {e} →
                  Exp2exp {Fun A B} {var} Γ (ELam e) ≡ ELam (λ v → Exp2exp {B} ((A , v) ∷ Γ) e)
Exp2exp-ELam≡ {A} {B} {var} {[]} {e} = refl
Exp2exp-ELam≡ {A} {B} {var} {x ∷ Γ} = refl

Exp2exp-EApp≡ : ∀ {A B} {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} {f} {v} →
                  Exp2exp {B} {var} Γ (EApp {τ = A} f v) ≡ EApp (Exp2exp Γ f) (Exp2exp Γ v)
Exp2exp-EApp≡ {A} {B} {var} {[]} {f} {v}= refl
Exp2exp-EApp≡ {A} {B} {var} {x ∷ Γ} = refl


postulate
  ext : ∀ {A B : Set} {f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g


⊂2↝ : ∀  {var : Type → Set}
         {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ'' : List (Σ[ A ∈ Type ] (var A))} → 
         Γ ⊂ Γ'' → Σ Ctx (λ Γ' → en₁2Ctx {var} Γ ↝ Γ' ↝ en₁2Ctx {var} Γ'') 
⊂2↝ (extend-hd x) = [] , refl (etG2S' x)
⊂2↝ (extend-mid {τ = (a , v)} Γ⊂Γ'') = (a ∷ proj₁ (⊂2↝ Γ⊂Γ'')) , extend (proj₂ (⊂2↝ Γ⊂Γ''))




lemmaExp2exp≡ : ∀ {τ τ'} {var : Type → Set} {v : var τ}
                  {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ' : List (Σ[ A ∈ Type ] (var A))}
                  {et : Γ ⊂ Γ'}
                  {e : Exp (τ ∷ en₁2Ctx Γ) τ'} →
                  Exp2exp ((τ , v) ∷ Γ) e ≡ Exp2exp ((τ , v) ∷ Γ') (elevate (extend (proj₂ (⊂2↝ {var} {Γ} {Γ'} et))) e)
lemmaExp2exp≡ {τ} {.τ} {var} {v} {Γ} {Γ'} {extend-hd x} {EVar hd} = refl
lemmaExp2exp≡ {τ} {τ'} {var} {v} {.Γ'} {Γ'} {extend-hd refl} {EVar (tl x₁)} = refl
lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {τ₁ ∷ Γ'} {extend-hd (extend x)} {EVar (tl x₁)} 
       = lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {Γ'} {extend-hd x} {EVar (tl x₁)}
lemmaExp2exp≡ {τ} {.τ} {var} {v} {τ₁ ∷ Γ} {.τ₁ ∷ Γ'} {extend-mid et} {EVar hd} = refl
lemmaExp2exp≡ {τ} {τ'} {var} {v} {τ₁ ∷ Γ} {.τ₁ ∷ Γ'} {extend-mid et} {EVar (tl x)} 
       = lemmaExp2exp≡ {proj₁ τ₁} {τ'} {var} {proj₂ τ₁} {Γ} {Γ'} {et} {EVar x}
lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {ECst x} = refl
lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {EAdd e e₁} 
        rewrite lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {e} |
                lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {e₁}
       = refl
lemmaExp2exp≡ {τ} {(Fun τ₁ τ')} {var} {v} {Γ} {Γ'} {et} {ELam e} 
       = cong ELam
           (ext {var τ₁} {exp var τ'}
            {λ v₁ → Exp2exp ((τ₁ , v₁) ∷ (τ , v) ∷ Γ) e}
            {λ v₁ →
               Exp2exp ((τ₁ , v₁) ∷ (τ , v) ∷ Γ')
               (elevate (extend (extend (proj₂ (⊂2↝ et)))) e)}
            (λ v₁ →
               lemmaExp2exp≡ {τ₁} {τ'} {var} {v₁} {(τ , v) ∷ Γ} {(τ , v) ∷ Γ'}
               {extend-mid {τ = τ , v} et} {e}))
lemmaExp2exp≡ {τ} {B} {var} {v} {Γ} {Γ'} {et} {EApp {τ = A} e e₁} 
        rewrite lemmaExp2exp≡ {τ} {Fun A B} {var} {v} {Γ} {Γ'} {et} {e} |
                lemmaExp2exp≡ {τ} {A} {var} {v} {Γ} {Γ'} {et} {e₁}  
       = refl


lemma1≡ :  ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} 
                 {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                 {et : Γ ↝ Γ'} 
                 {e : Exp (en₁2Ctx (Γ2en₁ Γ)) A} →
                 Exp2exp (Γ2en₁ Γ) e ≡ Exp2exp (Γ2en₁ Γ') (elevate (refl (etG2S et)) e)
lemma1≡ {A} {var₁} {var₂} {.Γ'} {Γ'} {refl} {EVar x} = refl
lemma1≡ {A} {var₁} {var₂} {Γ} {τ ∷ Γ'} {extend et} {EVar x} = lemma1≡ {A} {var₁} {var₂} {Γ} {Γ'} {et} {EVar x}
lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {ECst x} 
         rewrite Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ} | Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ'}
      = refl
lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {EAdd e e₁}
         rewrite Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ} {e} {e₁} | 
                 Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ'} {elevate (refl (etG2S et)) e} {elevate (refl (etG2S et)) e₁} |
                 lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {e} |
                 lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {e₁}
      = refl
lemma1≡ {(Fun τ τ')} {var₁} {var₂} {Γ} {Γ'} {et} {ELam e} 
      rewrite Exp2exp-ELam≡ {τ} {τ'} {var₁} {Γ2en₁ Γ} {e} | 
              Exp2exp-ELam≡ {τ} {τ'} {var₁} {Γ2en₁ Γ'} {elevate (extend (refl (etG2S et))) e} 
           =   cong ELam
                 (ext {var₁ τ} {exp var₁ τ'} {λ v → Exp2exp ((τ , v) ∷ Γ2en₁ Γ) e}
                  {λ v →
                     Exp2exp ((τ , v) ∷ Γ2en₁ Γ')
                     (elevate (extend (refl (etG2S et))) e)}
                  (λ v → this {v}))
                               where   this : ∀ {v} → Exp2exp ((τ , v) ∷ Γ2en₁ Γ) e ≡
                                              Exp2exp ((τ , v) ∷ Γ2en₁ Γ')
                                                      (elevate (extend (refl (etG2S et))) e)
                                       this {v} rewrite etG2S≡ {var₁} {var₂} {Γ} {Γ'} {et}
                                            = lemmaExp2exp≡ {τ} {τ'} {var₁} {v} {Γ2en₁ Γ} {Γ2en₁ Γ'} {extend-hd (etG2S'' et)} {e}
      


lemma1≡ {B} {var₁} {var₂} {Γ} {Γ'} {et} {EApp {τ = A} e e₁} 
      rewrite Exp2exp-EApp≡ {A} {B} {var₁} {Γ2en₁ Γ} {e} {e₁} |
              Exp2exp-EApp≡ {A} {B} {var₁} {Γ2en₁ Γ'} {elevate (refl (etG2S et)) e} {elevate (refl (etG2S et)) e₁} |
              lemma1≡ {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {e} |
              lemma1≡ {A} {var₁} {var₂} {Γ} {Γ'} {et} {e₁}
      = refl 








lemma2-EVar : ∀ {var₁ : Type → Set} {var₂ : Type → Set} {a}
                {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
                Γ ⊂ Γ' →
                a ∈ Γ →
                a ∈ Γ'
lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-hd refl) a∈Γ = a∈Γ
lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-hd (extend x)) a∈Γ = id-extend (lemma2-EVar (extend-hd x) a∈Γ)
lemma2-EVar {var₁} {var₂} {.proj₁ , .proj₂ , .proj₃} (extend-mid {Γ} {Γ'} {proj₁ , proj₂ , proj₃} Γ⊂Γ') hd = hd
lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-mid {Γ} {Γ'} {proj₁ , proj₂ , proj₃} Γ⊂Γ') (tl a∈Γ) = tl (lemma2-EVar Γ⊂Γ' a∈Γ)

lemma2  : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} 
                {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                {et : Γ ⊂ Γ'}
                {e : exp var₁ A} {e' : exp var₂ A} →
                similar-Exp Γ e e' →
                similar-Exp Γ' e e' 
lemma2 {A} {var₁} {var₂} {Γ} {Γ'} {et} {EVar x₁} {EVar x₂} (similar-EVar x) = similar-EVar (lemma2-EVar et x)
lemma2 similar-ECst = similar-ECst
lemma2 {Num} {var₁} {var₂} {Γ} {Γ'} {et} {EAdd a₁ a₂} {EAdd b₁ b₂} (similar-EAdd sim sim₁) 
    = similar-EAdd (lemma2 {Num} {var₁} {var₂} {Γ} {Γ'} {et} {a₁} {b₁} sim) 
                   (lemma2 {Num} {var₁} {var₂} {Γ} {Γ'} {et} {a₂} {b₂} sim₁)
lemma2 {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {ELam f₁} {ELam f₂} (similar-ELam sim) 
    = similar-ELam {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} (λ v₁ v₂ →
                                                            lemma2 {B} {var₁} {var₂} {(A , v₁ , v₂) ∷ Γ} {(A , v₁ , v₂) ∷ Γ'}
                                                            {extend-mid et} (sim v₁ v₂))
lemma2 {B} {var₁} {var₂} {Γ} {Γ'} {et} {EApp {A}  f₁ a₁} {EApp {.A} f₂ a₂} (similar-EApp sim sim₁) 
    = similar-EApp (lemma2 {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {f₁} {f₂} sim) 
                   (lemma2 {A} {var₁} {var₂} {Γ} {Γ'} {et} {a₁} {a₂} sim₁) 

lift-similar : ∀ {A var₁ var₂} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                 {et : Γ ↝ Γ'} {e : ATInt (en₁2Ctx (Γ2en₁ Γ)) A} {e' : atint var₂ A} →  
                 Similar {A} {var₁} {var₂} Γ e e' → 
                 Similar {A} {var₁} {var₂} Γ' (lift A (etG2S et) e) e'
lift-similar {SNum} sim = sim
lift-similar {SFun A A₁} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} sim 
    = λ {Γ''} {v} {v'} et₁ simvv' → this {Γ''} {v} {v'} et₁ simvv'
       where this : ∀ {Γ''} {v} {v'} et₁ simvv' → Similar Γ'' (e (lem-↝-trans (etG2S et) (etG2S et₁)) v) (e' v')
             this {Γ''} {v} {v'} et₁ simvv' rewrite etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {Γ''} {et} {et₁}
                  = sim {Γ''} {v} {v'} (lem-↝-trans et et₁) simvv'
lift-similar {D x} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} sim rewrite lemma1≡ {x} {var₁} {var₂} {Γ} {Γ'} {et} {e} 
    = lemma2 {x} {var₁} {var₂} {Γ} {Γ'} {extend-hd et} {Exp2exp (Γ2en₁ Γ') (elevate (refl (etG2S et)) e)} {e'} sim


lift-similar-env : ∀ {Δ var₁ var₂} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                     {et : Γ ↝ Γ'} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} {en : Env var₂ Δ} →
                    similar-env {var₁} {var₂} {Γ} {Δ} aen en → 
                    similar-env {var₁} {var₂} {Γ'} {Δ} (liftEnv (etG2S et) aen) en 
lift-similar-env [] = []
lift-similar-env {A ∷ Δ} {var₁} {var₂} {Γ} {Γ'} {et} {cons e aen} {cons e' en}  (scons x sim) 
    = scons (lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x) 
            (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim) 
 

Exp2expEVar≡ : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} {v₁ : var₁ A} {v₂ : var₂ A} 
                 {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                 {et : ((A , v₁ , v₂) ∷ Γ) ↝ Γ'} →
                 Exp2exp (Γ2en₁ Γ') (EVar {τ = A} (elevate-var {A ∷ (en₁2Ctx (Γ2en₁ Γ))} {en₁2Ctx (Γ2en₁ Γ')} {A} (etG2S et) hd)) ≡ EVar v₁
Exp2expEVar≡ {A} {var₁} {var₂} {v₁} {v₂} {Γ} {.((A , v₁ , v₂) ∷ Γ)} {refl} = refl
Exp2expEVar≡ {A} {var₁} {var₂} {v₁} {v₂} {Γ} {(τ ∷ Γ')} {extend et} 
   = Exp2expEVar≡ {A} {var₁} {var₂} {v₁} {v₂} {Γ} {Γ'} {et}

A∈Γ↝Γ' : ∀ {A} {Γ : List A} {Γ' : List A} {α : A} →
           (et : (α ∷ Γ) ↝ Γ') → α ∈ Γ'
A∈Γ↝Γ' refl = hd
A∈Γ↝Γ' (extend et) = tl (A∈Γ↝Γ' et)  

mutual
  similar-Exp2Similar-Embed : ∀ {α} {l : liftable1 α}
                              {var₁ : Type → Set} {var₂ : Type → Set} 
                              {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                              {e : Exp (en₁2Ctx (Γ2en₁ Γ)) (typeof α)} {e' : exp var₂ (typeof α)} →
                              similar-Exp Γ (Exp2exp (Γ2en₁ Γ) e) e' →
                              Similar Γ (Embed l e) (embed l e')
  similar-Exp2Similar-Embed {SNum} {()} sim
  similar-Exp2Similar-Embed {SFun α α₁} {Func l l₁} {var₁} {var₂} {Γ} {e} {e'} sim 
     = λ {Γ'} {v} {v'} et simvv' →
           similar-Exp2Similar-Embed {α₁} {l₁} {var₁} {var₂} {Γ'}
           {EApp (elevate (refl (etG2S et)) e) (Lift' l v)}
           {EApp e' (lift' l v')} (that {Γ'} {et} {v} {v'} {simvv'})   
       where that : ∀ {Γ'} {et : Γ ↝ Γ'} {v} {v'} {simvv' : Similar Γ' v v'} →       
                      similar-Exp Γ'
                         (Exp2exp (Γ2en₁ Γ') (EApp (elevate (refl (etG2S et)) e) (Lift' l v)))
                         (EApp e' (lift' l v'))
             that {Γ'} {et} {v} {v'} {simvv'}
               rewrite Exp2exp-EApp≡ {typeof α} {typeof α₁} {var₁} {Γ2en₁ Γ'} {elevate (refl (etG2S et)) e} {Lift' l v}
               = similar-EApp (this {Γ'} {et})
                   (Lift-Similar {α} {var₁} {var₂} {Γ'} {l} {v} {v'} simvv') 
                where
                 this : ∀ {Γ'} {et : Γ ↝ Γ'} → similar-Exp Γ' (Exp2exp (Γ2en₁ Γ') (elevate (refl (etG2S et)) e)) e'
                 this {Γ'} {et}
                      rewrite sym (lemma1≡ {Fun (typeof α) (typeof α₁)} {var₁} {var₂} {Γ} {Γ'} {et} {e})
                         = lemma2 {Fun (typeof α) (typeof α₁)} {var₁} {var₂} {Γ} {Γ'}
                             {extend-hd et} {Exp2exp (Γ2en₁ Γ) e} {e'} sim 
  similar-Exp2Similar-Embed {D x} {base} sim = sim

  Lift-Similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {l : liftable1 A} 
                 {v : ATInt (en₁2Ctx (Γ2en₁ Γ)) A} {v' : atint var₂ A} →
                 Similar Γ v v' →
                 similar-Exp Γ (Exp2exp (Γ2en₁ Γ) (Lift' l v)) (lift' l v')
  Lift-Similar {(D x)} {var₁} {var₂} {Γ} {base} sim = sim
  Lift-Similar {(SFun α₁ α₂)} {var₁} {var₂} {Γ} {Func l l₁} {v} {v'} sim 
      rewrite Exp2expELam≡ {typeof α₁} {typeof α₂} {var₁} {Γ2en₁ Γ} {Lift' l₁ (v (extend refl) (Embed l (EVar hd)))}
      = similar-ELam (λ v₁ v₂ →
                          Lift-Similar {α₂} {var₁} {var₂} {(typeof α₁ , v₁ , v₂) ∷ Γ} {l₁}
                          {v (extend refl) (Embed l (EVar hd))} {v' (embed l (EVar v₂))}
                          (sim {(typeof α₁ , v₁ , v₂) ∷ Γ} {Embed l (EVar hd)}
                           {embed l (EVar v₂)} (extend refl)
                           (similar-Exp2Similar-Embed {α₁} {l} {var₁} {var₂}
                            {(typeof α₁ , v₁ , v₂) ∷ Γ} {EVar hd} {EVar v₂} (this {v₁} {v₂}))))
       where this : ∀ {v₁} {v₂} → similar-Exp ((typeof α₁ , v₁ , v₂) ∷ Γ) (Exp2exp (Γ2en₁ ((typeof α₁ , v₁ , v₂) ∷ Γ)) (EVar hd)) (EVar v₂)
             this {v₁} {v₂} = similar-EVar hd 


proj-correct : ∀ {Δ A var₁ var₂} {Γ :  List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {e : AExp Δ A} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} 
                 {en : Env var₂ Δ} →
               similar-env {var₁} {var₂} {Γ} {Δ} aen en → 
               let e' = proj e en in
               Similar {A} {var₁} {var₂} Γ (PE e aen) (pe e')
proj-correct {[]} {A} {var₁} {var₂} {Γ} {Var ()} []
proj-correct {A₁ ∷ Δ} {.A₁} {var₁} {var₂} {Γ} {Var hd} (scons x₁ sim) = x₁
proj-correct {A₁ ∷ Δ} {A} {var₁} {var₂} {Γ} {Var (tl x)} (scons x₁ sim) 
  = proj-correct {Δ} {A} {var₁} {var₂} {Γ} {Var x} sim
proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {SCst x} sim = refl
proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {SAdd e e₁} sim 
  rewrite proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {e} sim | proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {e₁} sim
  = refl
proj-correct {Δ} {(SFun α₁ α₂)} {var₁} {var₂} {Γ} {SLam e} {aen} {en} sim 
  = λ {Γ'} {v} {v'} et simvv' →
        proj-correct {α₁ ∷ Δ} {α₂} {var₁} {var₂} {Γ'} {e}
        {cons v (liftEnv (etG2S et) aen)} {cons v' en}
        (scons {A = α₁} {Δ = Δ} {e = v} {e' = v'}
         {aen = liftEnv (etG2S et) aen} {en = en} simvv'
         (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim))
proj-correct {Δ} {B} {var₁} {var₂} {Γ} {SApp {α₂ = A} e e₁} {aen} {en} sim 
  = proj-correct {Δ} {SFun A B} {var₁} {var₂} {Γ} {e} {aen} {en} sim
      {Γ} {PE e₁ aen} {pe (proj e₁ en)} refl
      (proj-correct {Δ} {A} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
proj-correct {Δ} {(D Num)} {var₁} {var₂} {Γ} {DCst x} sim 
  rewrite Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ}
  = similar-ECst
proj-correct {Δ} {(D Num)} {var₁} {var₂} {Γ} {DAdd e e₁} {aen} {en} sim 
  rewrite Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ} {PE e aen} {PE e₁ aen}
  = similar-EAdd (proj-correct {Δ} {D Num} {var₁} {var₂} {Γ} {e} {aen} {en} sim) 
                 (proj-correct {Δ} {D Num} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
proj-correct {Δ} {(D (Fun τ₁ τ₂))} {var₁} {var₂} {Γ} {DLam e} {aen} {en} sim 
  rewrite Exp2exp-ELam≡ {τ₁} {τ₂} {var₁} {Γ2en₁ Γ} {PE e (cons (EVar hd) (liftEnv (extend refl) aen))}
  = similar-ELam {A = τ₁} {B = τ₂} 
                 {f₁ = λ v → Exp2exp ((τ₁ , v) ∷ Γ2en₁ Γ)(PE e (cons (EVar hd) (liftEnv (extend refl) aen)))} 
                 {f₂ = λ v → pe (proj e (cons (EVar v) en))}  
    (λ v₁ v₂ →
         proj-correct {D τ₁ ∷ Δ} {D τ₂} {var₁} {var₂} {(τ₁ , v₁ , v₂) ∷ Γ}
         {e} {cons (EVar hd) (liftEnv (extend refl) aen)}
         {cons (EVar v₂) en} (this {v₁} {v₂}))
    where this : ∀ {v₁} {v₂} → similar-env (cons (EVar hd) (liftEnv (extend refl) aen)) (cons (EVar v₂) en)
          this {v₁} {v₂} = scons (similar-EVar hd) (lift-similar-env sim)
proj-correct {Δ} {(D τ₁)} {var₁} {var₂} {Γ} {DApp {τ₂ = τ₂} e e₁} {aen} {en} sim 
  rewrite Exp2exp-EApp≡ {τ₂} {τ₁} {var₁} {Γ2en₁ Γ} {PE e aen} {PE e₁ aen}
  = similar-EApp (proj-correct {Δ} {D (Fun τ₂ τ₁)} {var₁} {var₂} {Γ} {e} {aen} {en} sim) 
                 (proj-correct {Δ} {D τ₂} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
proj-correct {Δ} {.(D (typeof α))} {var₁} {var₂} {Γ} {e = ↑ {α} l e} {aen} {en} sim 
  = Lift-Similar {α} {var₁} {var₂} {Γ} {l} {PE e aen} {pe (proj e en)}
      (proj-correct {e = e} sim)

