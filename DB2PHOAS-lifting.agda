module DB2PHOAS-lifting where
open import Data.Nat hiding  (_<_;_⊔_;_*_;equal)
open import Data.Bool hiding (_∨_) 
open import Function using (_∘_)
open import Data.List
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 
open import Data.Empty
open import Data.Product
open import Lib hiding (_∧_)
open import Data.Sum

----------------------
--residual type [Type]
----------------------
data Type : Set where
  Int : Type
  Fun : Type → Type → Type

----------------------------------
--annotated two-level type [AType]
----------------------------------
data AType : Set where
  AInt : AType
  AFun : AType → AType → AType
  D    : Type → AType





----------------------
--higher order lifting
----------------------
typeof : AType → Type
typeof AInt = Int
typeof (AFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
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
          → liftable1 (AFun α₁ α₂)

---------------------------------------------
--[liftable] in [BTA9] without pairs and sums
---------------------------------------------
mutual 
  data Liftable2 : AType → Set where
    D : ∀ τ → Liftable2 (D τ)
    AInt : Liftable2 AInt
    AFun : ∀ {α₁ α₂} → Liftable2⁻ α₁ → Liftable2 α₂ → Liftable2 (AFun α₁ α₂)

  data Liftable2⁻ : AType → Set where
    D : ∀ τ → Liftable2⁻ (D τ)
    AFun : ∀ {α₁ α₂} → Liftable2 α₁ → Liftable2⁻ α₂ → Liftable2⁻ (AFun α₁ α₂)

-----------
--de bruijn
-----------
---------------------
--residual expression
---------------------
Ctx = List Type

data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  EInt : ℕ → Exp Γ Int
  EAdd : Exp Γ Int → Exp Γ Int -> Exp Γ Int
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'

--------------------------------
--two-level annotated expression
--------------------------------
ACtx = List AType

data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  AInt : ℕ → AExp Δ AInt
  AAdd : AExp Δ AInt → AExp Δ AInt → AExp Δ AInt
  ALam : ∀ {α₁ α₂}   → AExp (α₁ ∷ Δ) α₂ → AExp Δ (AFun α₁ α₂)
  AApp : ∀ {α₁ α₂}   → AExp Δ (AFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
  DInt : ℕ → AExp Δ (D Int)
  DAdd : AExp Δ (D Int) → AExp Δ (D Int) → AExp Δ (D Int)
  DLam : ∀ {τ₁ τ₂}   → AExp ((D τ₁) ∷ Δ) (D τ₂) → AExp Δ (D (Fun τ₁ τ₂))
  DApp : ∀ {τ₁ τ₂}   → AExp Δ (D (Fun τ₂ τ₁)) → AExp Δ (D τ₂) → AExp Δ (D τ₁)
  ↓    : ∀  {α} → liftable1 α → AExp Δ α → AExp Δ (D (typeof α))

----------------------------
-- The interpreter of [Type]
----------------------------
EImp : Type → Set
EImp Int = ℕ
EImp (Fun ty ty₁) = EImp ty → EImp ty₁



-----------------------------
-- The interpreter of [AType]
-----------------------------
Imp : Ctx → AType → Set
Imp Γ (AInt) = ℕ
Imp Γ (AFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (Imp Γ' α₁ → Imp Γ' α₂)
Imp Γ (D σ) = Exp Γ σ

-------------
--environment
-------------
data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  cons : ∀ {Δ} {α : AType} → Imp Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)


-------
--PHOAS
-------
---------------
--residual term
---------------
data exp (var : Type → Set) : Type → Set where
  EVar : ∀ {A} → var A → exp var A
  ECst : ℕ → exp var Int
  EAdd : exp var Int → exp var Int → exp var Int
  ELam : ∀ {A B} → (var A → exp var B) → exp var (Fun A B)
  EApp : ∀ {A B} → exp var (Fun A B) → exp var A → exp var B

--------------------------
--annotated two-level term
--------------------------
data aexp (var : AType → Set) : AType → Set where
  Var  : ∀ {A} → var A → aexp var A
--static expression
  SCst : ℕ → aexp var AInt
  SAdd : aexp var AInt → aexp var AInt → aexp var AInt
  SLam : ∀ {A B} → (var A → aexp var B) → aexp var (AFun A B)
  SApp : ∀ {A B} → aexp var (AFun A B) → aexp var A → aexp var B
--dynamic expression
  DCst : ℕ → aexp var (D Int)
  DAdd : aexp var (D Int) → aexp var (D Int) → aexp var (D Int)
  DLam : ∀ {a b} → (var (D a) → aexp var (D b)) → aexp var (D (Fun a b))
  DApp : ∀ {a b} → aexp var (D (Fun a b)) → aexp var (D a) → aexp var (D b)
  ↓    : ∀  {α} → liftable1 α → aexp var α → aexp var (D (typeof α))

-----------------------
--interpreter of [Type]
-----------------------
TInt : Type → Set
TInt Int = ℕ
TInt (Fun ty ty₁) = TInt ty → TInt ty₁

------------------------
--interpreter of [AType]
------------------------
ATInt : (Type → Set) → AType → Set
ATInt var AInt = ℕ
ATInt var (AFun aty aty₁) = ATInt var aty → ATInt var aty₁
ATInt var (D x) = exp var x

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
  cons : ∀ {Δ} {α : AType} → ATInt var α → Env var Δ → Env var (α ∷ Δ)

-----------------------
--some auxiliary lemmas
-----------------------
lookupenv : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → A ∈ Δ → Env var Δ → ATInt var A
lookupenv hd (cons x l) = x
lookupenv (tl id) (cons x l) = lookupenv id l 



proj : ∀ {A : AType} {Δ : ACtx} {var : Type → Set}  → AExp Δ A → Env var Δ  → aexp (ATInt var) A
proj {A} {Δ} (Var x) env = Var (lookupenv x env)
proj {AInt} (AInt x) env = SCst x
proj (AAdd ae ae₁) env = SAdd (proj ae env) (proj ae₁ env)
proj {AFun α₁ α₂}  (ALam ae) env = SLam (λ x → proj ae (cons x env))
proj (AApp ae ae₁) env = SApp (proj ae env) (proj ae₁ env)
proj (DInt x) env = DCst x
proj (DAdd ae ae₁) env = DAdd (proj ae env) (proj ae₁ env)
proj {D (Fun τ₁ τ₂)} (DLam ae) env = DLam (λ v → proj ae (cons v env))
proj (DApp ae ae₁) env = DApp (proj ae env) (proj ae₁ env)
proj (↓ l e) env = ↓ l (proj e env)

---------------------------------
--a generalized version of [proj]
---------------------------------
----------------------------
--alternative environment
----------------------------
data Env' : (AType → Set) → ACtx → Set₁ where
  []   : ∀ var → Env' var []
  cons : ∀ {Δ} {α : AType} {var : AType → Set} → var α → Env' var Δ → Env' var (α ∷ Δ)

-----------------------
--some auxiliary lemmas
-----------------------
lookupenv' : ∀ {A : AType} {Δ : ACtx} {var : AType → Set} → A ∈ Δ → Env' var Δ → var A
lookupenv' hd (cons x l) = x
lookupenv' (tl id) (cons x l) = lookupenv' id l 



proj' : ∀ {A : AType} {Δ : ACtx} {var : AType → Set}  → AExp Δ A → Env' var Δ  → aexp var A
proj' {A} {Δ} (Var x) env = Var (lookupenv' x env)
proj' {AInt} (AInt x) env = SCst x
proj' (AAdd ae ae₁) env = SAdd (proj' ae env) (proj' ae₁ env)
proj' {AFun α₁ α₂}  (ALam ae) env = SLam (λ x → proj' ae (cons x env))
proj' (AApp ae ae₁) env = SApp (proj' ae env) (proj' ae₁ env)
proj' (DInt x) env = DCst x
proj' (DAdd ae ae₁) env = DAdd (proj' ae env) (proj' ae₁ env)
proj' {D (Fun τ₁ τ₂)} (DLam ae) env = DLam (λ v → proj' ae (cons v env))
proj' (DApp ae ae₁) env = DApp (proj' ae env) (proj' ae₁ env)
proj' (↓ l e) env = ↓ l (proj' e env)

-----------------------------
--from [PHOAS] to [De Bruijn]
--[proj']
-----------------------------
----------
--analysis
----------
--Since free variable in [PHOAS] stores its value within itself as follows,
--[Var 5] where [5] is the value stored within this free variable
--we donot need to consider "environment" when specifying partial evaluator.
--We need,however,consider it when tranlating from [PHOAS] to [De Bruijn].

-- ifeq' : ∀ (A B : Type) → Bool
-- ifeq' Int Int = true
-- ifeq' Int (Fun b b₁) = false
-- ifeq' (Fun a a₁) Int = false
-- ifeq' (Fun a a₁) (Fun b b₁) = ifeq' a b ∧ ifeq' a₁ b₁

-- ifeq : ∀ (A B : AType) → Bool
-- ifeq AInt AInt = true
-- ifeq AInt (AFun b b₁) = false
-- ifeq AInt (D x) = false
-- ifeq (AFun a a₁) AInt = false
-- ifeq (AFun a a₁) (AFun b b₁) = ifeq a b ∧ ifeq a₁ b₁
-- ifeq (AFun a a₁) (D x) = false
-- ifeq (D x) AInt = false
-- ifeq (D x) (AFun b b₁) = false
-- ifeq (D x) (D x₁) = ifeq' x x₁

-- ifeqAInt : ∀ {var : Type → Set} {A : AType} (a b : ATInt var A) → Σ (ATInt var A) \ x → Bool
-- ifeqAInt {var} {AInt} zero zero = zero , true
-- ifeqAInt {var} {AInt} zero (suc b) = zero , false
-- ifeqAInt {var} {AInt} (suc a) zero = (suc a) , false
-- ifeqAInt {var} {AInt} (suc a) (suc b) = zero , (proj₂ (ifeqAInt {var} {AInt} a b))
-- ifeqAInt {var} {AFun A A₁} a b = {!!} , {!!}
-- ifeqAInt {var} {D x} a b = {!!}

-- ∧-eq : ∀ {a b : Bool} → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
-- ∧-eq {true} {true} eq = refl , refl
-- ∧-eq {true} {false} ()
-- ∧-eq {false} ()

-- eqAB' : ∀ {A B : Type} → (ifeq' A B ≡ true) → A ≡ B
-- eqAB' {Int} {Int} b = refl
-- eqAB' {Int} {Fun B B₁} ()
-- eqAB' {Fun A A₁} {Int} ()
-- eqAB' {Fun A A₁} {Fun B B₁} b 
--   rewrite eqAB' {A} {B} (proj₁ (∧-eq {ifeq' A B} {ifeq' A₁ B₁} b)) | eqAB' {A₁} {B₁} (proj₂ (∧-eq {ifeq' A B} {ifeq' A₁ B₁} b))
--     = refl

-- eqAB : ∀ {A B : AType} → (ifeq A B ≡ true)  → A ≡ B
-- eqAB {AInt} {AInt} b = refl
-- eqAB {AInt} {AFun B B₁} ()
-- eqAB {AInt} {D x} ()
-- eqAB {AFun A A₁} {AInt} ()
-- eqAB {AFun A A₁} {AFun B B₁} b 
--   rewrite eqAB {A} {B} (proj₁ (∧-eq {ifeq A B} {ifeq A₁ B₁} b)) | eqAB {A₁} {B₁} (proj₂ (∧-eq {ifeq A B} {ifeq A₁ B₁} b)) 
--     = refl
-- eqAB {AFun A A₁} {D x} ()
-- eqAB {D x} {AInt} ()
-- eqAB {D x} {AFun B B₁} ()
-- eqAB {D x} {D x₁} b rewrite eqAB' {x} {x₁} b = refl



-- lookupenv'' : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → ATInt var A → Env var Δ → A ∈ Δ
-- lookupenv'' {A} {.[]} {var} e ([]) = {!!}
-- lookupenv'' {A} e (cons {α = α} x l) = {!!} 

-- proj'' : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → aexp (ATInt var) A → Env var Δ → AExp Δ A
-- proj'' (Var x) env = Var (lookupenv'' x env)
-- proj'' (SCst x) env = AInt x
-- proj'' (SAdd e e₁) env = AAdd (proj'' e env) (proj'' e₁ env)
-- proj'' {AFun A B} {var = var} (SLam x) env = ALam {!λ v → proj'' (x v) (cons v env)!}
-- proj'' (SApp e e₁) env = AApp (proj'' e env) (proj'' e₁ env)
-- proj'' (DCst x) env = DInt x
-- proj'' (DAdd e e₁) env = DAdd (proj'' e env) (proj'' e₁ env)
-- proj'' (DLam x) env = DLam {!λ v → proj'' (x v) (cons v env)!}
-- proj'' (DApp e e₁) env = DApp (proj'' e env) (proj'' e₁ env)

--------------------------------------------------------------------------------------
--partial evaluation is indifferent to the translation from [AExp] to [aexp] by [proj]
--------------------------------------------------------------------------------------
-----------------------------
--partial evaluator of [AExp]
-----------------------------
----------------------------------
--auxiliary functions for shifting
----------------------------------
lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → Imp Γ α
lookup [] ()
lookup {α} (cons x aenv) hd = x
lookup {α} (cons x aenv) (tl {.α} {y} id) = lookup aenv id


elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var ↝-refl x = x
elevate-var (↝-extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)


elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
elevate-var2 (↝↝-base x) x₁ = elevate-var x x₁
elevate-var2 (↝↝-extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (↝↝-extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)




elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (EInt x) = EInt x
elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (↝↝-extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)

liftE : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
liftE Γ↝Γ' e = elevate (↝↝-base Γ↝Γ') e


lift : ∀ {Γ Γ'} α → Γ ↝ Γ' → Imp Γ α → Imp Γ' α 
lift AInt p v = v
lift (AFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (↝-trans Γ↝Γ' Γ'↝Γ'')
lift (D x₁) Γ↝Γ' v = elevate (↝↝-base Γ↝Γ') v


liftEnv : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
liftEnv Γ↝Γ' [] = []
liftEnv Γ↝Γ' (cons {α = α} x env) = cons {α = α} (lift α Γ↝Γ' x) (liftEnv Γ↝Γ' env)

consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
consD σ env = (cons {α = D σ} (EVar hd) (liftEnv (↝-extend {τ = σ} ↝-refl) env))
-----
--end
----- 
------------------------------------
--[lift'] and [embed] in [De Bruijn] 
------------------------------------
mutual 
  Lift' : ∀ {Γ α} → liftable1 α → Imp Γ α → (Exp Γ (typeof α))
  Lift' base v = v
  Lift' {Γ} {AFun α₁ α₂} (Func l l₁) v = ELam ((λ x → Lift' l₁ (v (↝-extend {τ = typeof α₁} ↝-refl) x))
                                                 (Embed l (EVar {Γ = typeof α₁ ∷ Γ} hd)))
 
  Embed : ∀ {Γ α} → liftable1 α → Exp Γ (typeof α) → (Imp Γ α)
  Embed base e = e
  Embed {Γ} {AFun α₁ α₂} (Func l l₁) e = λ Γ↝Γ' v₁ → Embed l₁ (EApp (liftE Γ↝Γ' e) (Lift' l v₁))

------------------------------------
--[lift'] and [embed] in [PHOAS] 
------------------------------------
mutual 
  lift' : ∀ {A var} → liftable1 A → ATInt var A → (exp var (typeof A))
  lift' base v = v
  lift' {AFun α₁ α₂} {var} (Func l l₁) v = ELam (λ x → lift' l₁ (v (embed l (EVar x))))
 
  embed : ∀ {A var} → liftable1 A → exp var (typeof A) → (ATInt var A)
  embed base e = e
  embed {AFun α₁ α₂} {var} (Func l l₁) e = λ x → embed l₁ (EApp e (lift' l x))

----------------------------------------------------------------------------------------------------

PE : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → Imp Γ α
PE (Var x) env = lookup env x
PE (AInt x) env = x
PE (AAdd e e₁) env = PE e env + PE e₁ env
PE (ALam {α} e) env = λ Γ↝Γ' → λ y → PE e (cons {α = α} y (liftEnv Γ↝Γ' env))
PE (AApp e e₁) env = PE e env ↝-refl (PE e₁ env)
PE (DInt x) env = EInt x
PE (DAdd e e₁) env = EAdd (PE e env) (PE e₁ env)
PE (DLam {σ} e) env = ELam (PE e (consD σ env))
PE (DApp e e₁) env = EApp (PE e env) (PE e₁ env)
PE (↓ l e) env = Lift' l (PE e env) 


-----------------------------
--partial evaluator of [aexp]
-----------------------------
pe : ∀ {A var} → aexp (ATInt var) A → ATInt var A
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
Exp2exp Γ (EInt x) = ECst x
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
etG2S ↝-refl = ↝-refl
etG2S (↝-extend etG) = ↝-extend (etG2S etG)

etG2S' : ∀ {var : Type → Set} 
          {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ' : List (Σ[ A ∈ Type ] (var A))} →
           Γ ↝ Γ' →
          en₁2Ctx Γ ↝ en₁2Ctx Γ'
etG2S' ↝-refl = ↝-refl
etG2S' (↝-extend etG) = ↝-extend (etG2S' etG)

etG2S'' : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
          {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
           Γ ↝ Γ' →
          Γ2en₁ Γ ↝ Γ2en₁ Γ'
etG2S'' ↝-refl = ↝-refl
etG2S'' (↝-extend etG) = ↝-extend (etG2S'' etG)

etG2S≡ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
          {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
          {et : Γ ↝ Γ'} → 
           etG2S et ≡  etG2S' (etG2S'' et)
etG2S≡ {var₁} {var₂} {.Γ'} {Γ'} {↝-refl} = refl
etG2S≡ {var₁} {var₂} {Γ} {(τ ∷ Γ')} {↝-extend et} = this 
   where this : ↝-extend (etG2S et) ≡ ↝-extend (etG2S' (etG2S'' et))
         this rewrite etG2S≡ {var₁} {var₂} {Γ} {Γ'} {et}
              = refl



etG2S-trans≡ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
                {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                {Γ'' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                {et : Γ ↝ Γ'} {et₁ : Γ' ↝ Γ''} →
                ↝-trans (etG2S et) (etG2S et₁) ≡ etG2S (↝-trans et et₁)
etG2S-trans≡ {var₁} {var₂} {Γ} {.Γ''} {Γ''} {et} {↝-refl} = refl
etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {(τ ∷ Γ'')} {et} {↝-extend et₁} = this
       where this : ↝-extend (↝-trans (etG2S et) (etG2S et₁)) ≡ ↝-extend (etG2S (↝-trans et et₁))
             this 
              rewrite etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {Γ''} {et} {et₁} 
                  = refl     

Similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set}  → (Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))) → Imp (en₁2Ctx (Γ2en₁ Γ)) A → 
            ATInt var₂ A → Set
Similar {AInt} Γ e e' = e ≡ e'
Similar {AFun A A₁} {var₁} {var₂} Γ e e' = {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {v : Imp (en₁2Ctx (Γ2en₁ {var₁} {var₂} Γ')) A} 
                                           {v' : ATInt var₂ A} →
                                           --(et : en₁2Ctx (Γ2en₁ Γ) ↝ en₁2Ctx (Γ2en₁ Γ')) →
                                           (et : Γ ↝ Γ') →
                                           Similar Γ' v v' → Similar Γ' (e (etG2S et) v) (e' v')
Similar {D x} Γ e e' = similar-Exp Γ (Exp2exp (Γ2en₁ Γ) e) e'
    

data similar-env {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
     : ∀ {Δ : ACtx} → AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ → Env var₂ Δ → Set₁ where
 []    : similar-env [] [] 
 scons  : ∀ {A : AType} {Δ : ACtx} {e : Imp (en₁2Ctx (Γ2en₁ Γ)) A} {e' : ATInt var₂ A} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} {en : Env var₂ Δ} 
          → Similar Γ e e'  → similar-env {var₁} {var₂} {Γ} {Δ} aen en → similar-env (cons e aen) (cons e' en)



id-extend : ∀ {A : Set} {a : A} {b : A} {Γ : List A} → a ∈ Γ → a ∈ (b ∷ Γ)
id-extend hd = tl hd
id-extend (tl a∈Γ) = tl (tl a∈Γ)

-----------------------------------------
--some auxiliary lemmas regarding lemma1≡
-----------------------------------------

Exp2exp-EInt≡ : ∀ {n} {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} → 
                  Exp2exp Γ (EInt n) ≡ ECst n
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
⊂2↝ (extend-hd x) = [] , ↝↝-base (etG2S' x)
⊂2↝ (extend-mid {τ = (a , v)} Γ⊂Γ'') = (a ∷ proj₁ (⊂2↝ Γ⊂Γ'')) , ↝↝-extend (proj₂ (⊂2↝ Γ⊂Γ''))




lemmaExp2exp≡ : ∀ {τ τ'} {var : Type → Set} {v : var τ}
                  {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ' : List (Σ[ A ∈ Type ] (var A))}
                  {et : Γ ⊂ Γ'}
                  {e : Exp (τ ∷ en₁2Ctx Γ) τ'} →
                  Exp2exp ((τ , v) ∷ Γ) e ≡ Exp2exp ((τ , v) ∷ Γ') (elevate (↝↝-extend (proj₂ (⊂2↝ {var} {Γ} {Γ'} et))) e)
lemmaExp2exp≡ {τ} {.τ} {var} {v} {Γ} {Γ'} {extend-hd x} {EVar hd} = refl
lemmaExp2exp≡ {τ} {τ'} {var} {v} {.Γ'} {Γ'} {extend-hd ↝-refl} {EVar (tl x₁)} = refl
lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {τ₁ ∷ Γ'} {extend-hd (↝-extend x)} {EVar (tl x₁)} 
       = lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {Γ'} {extend-hd x} {EVar (tl x₁)}
lemmaExp2exp≡ {τ} {.τ} {var} {v} {τ₁ ∷ Γ} {.τ₁ ∷ Γ'} {extend-mid et} {EVar hd} = refl
lemmaExp2exp≡ {τ} {τ'} {var} {v} {τ₁ ∷ Γ} {.τ₁ ∷ Γ'} {extend-mid et} {EVar (tl x)} 
       = lemmaExp2exp≡ {proj₁ τ₁} {τ'} {var} {proj₂ τ₁} {Γ} {Γ'} {et} {EVar x}
lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {EInt x} = refl
lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {EAdd e e₁} 
        rewrite lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {e} |
                lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {e₁}
       = refl
lemmaExp2exp≡ {τ} {(Fun τ₁ τ')} {var} {v} {Γ} {Γ'} {et} {ELam e} 
       = cong ELam
           (ext {var τ₁} {exp var τ'}
            {λ v₁ → Exp2exp ((τ₁ , v₁) ∷ (τ , v) ∷ Γ) e}
            {λ v₁ →
               Exp2exp ((τ₁ , v₁) ∷ (τ , v) ∷ Γ')
               (elevate (↝↝-extend (↝↝-extend (proj₂ (⊂2↝ et)))) e)}
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
                 Exp2exp (Γ2en₁ Γ) e ≡ Exp2exp (Γ2en₁ Γ') (elevate (↝↝-base (etG2S et)) e)
lemma1≡ {A} {var₁} {var₂} {.Γ'} {Γ'} {↝-refl} {EVar x} = refl
lemma1≡ {A} {var₁} {var₂} {Γ} {τ ∷ Γ'} {↝-extend et} {EVar x} = lemma1≡ {A} {var₁} {var₂} {Γ} {Γ'} {et} {EVar x}
lemma1≡ {Int} {var₁} {var₂} {Γ} {Γ'} {et} {EInt x} 
         rewrite Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ} | Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ'}
      = refl
lemma1≡ {Int} {var₁} {var₂} {Γ} {Γ'} {et} {EAdd e e₁}
         rewrite Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ} {e} {e₁} | 
                 Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ'} {elevate (↝↝-base (etG2S et)) e} {elevate (↝↝-base (etG2S et)) e₁} |
                 lemma1≡ {Int} {var₁} {var₂} {Γ} {Γ'} {et} {e} |
                 lemma1≡ {Int} {var₁} {var₂} {Γ} {Γ'} {et} {e₁}
      = refl
lemma1≡ {(Fun τ τ')} {var₁} {var₂} {Γ} {Γ'} {et} {ELam e} 
      rewrite Exp2exp-ELam≡ {τ} {τ'} {var₁} {Γ2en₁ Γ} {e} | 
              Exp2exp-ELam≡ {τ} {τ'} {var₁} {Γ2en₁ Γ'} {elevate (↝↝-extend (↝↝-base (etG2S et))) e} 
           =   cong ELam
                 (ext {var₁ τ} {exp var₁ τ'} {λ v → Exp2exp ((τ , v) ∷ Γ2en₁ Γ) e}
                  {λ v →
                     Exp2exp ((τ , v) ∷ Γ2en₁ Γ')
                     (elevate (↝↝-extend (↝↝-base (etG2S et))) e)}
                  (λ v → this {v}))
                               where   this : ∀ {v} → Exp2exp ((τ , v) ∷ Γ2en₁ Γ) e ≡
                                              Exp2exp ((τ , v) ∷ Γ2en₁ Γ')
                                                      (elevate (↝↝-extend (↝↝-base (etG2S et))) e)
                                       this {v} rewrite etG2S≡ {var₁} {var₂} {Γ} {Γ'} {et}
                                            = lemmaExp2exp≡ {τ} {τ'} {var₁} {v} {Γ2en₁ Γ} {Γ2en₁ Γ'} {extend-hd (etG2S'' et)} {e}
      


lemma1≡ {B} {var₁} {var₂} {Γ} {Γ'} {et} {EApp {τ = A} e e₁} 
      rewrite Exp2exp-EApp≡ {A} {B} {var₁} {Γ2en₁ Γ} {e} {e₁} |
              Exp2exp-EApp≡ {A} {B} {var₁} {Γ2en₁ Γ'} {elevate (↝↝-base (etG2S et)) e} {elevate (↝↝-base (etG2S et)) e₁} |
              lemma1≡ {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {e} |
              lemma1≡ {A} {var₁} {var₂} {Γ} {Γ'} {et} {e₁}
      = refl 








lemma2-EVar : ∀ {var₁ : Type → Set} {var₂ : Type → Set} {a}
                {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
                Γ ⊂ Γ' →
                a ∈ Γ →
                a ∈ Γ'
lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-hd ↝-refl) a∈Γ = a∈Γ
lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-hd (↝-extend x)) a∈Γ = id-extend (lemma2-EVar (extend-hd x) a∈Γ)
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
lemma2 {Int} {var₁} {var₂} {Γ} {Γ'} {et} {EAdd a₁ a₂} {EAdd b₁ b₂} (similar-EAdd sim sim₁) 
    = similar-EAdd (lemma2 {Int} {var₁} {var₂} {Γ} {Γ'} {et} {a₁} {b₁} sim) 
                   (lemma2 {Int} {var₁} {var₂} {Γ} {Γ'} {et} {a₂} {b₂} sim₁)
lemma2 {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {ELam f₁} {ELam f₂} (similar-ELam sim) 
    = similar-ELam {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} (λ v₁ v₂ →
                                                            lemma2 {B} {var₁} {var₂} {(A , v₁ , v₂) ∷ Γ} {(A , v₁ , v₂) ∷ Γ'}
                                                            {extend-mid et} (sim v₁ v₂))
lemma2 {B} {var₁} {var₂} {Γ} {Γ'} {et} {EApp {A}  f₁ a₁} {EApp {.A} f₂ a₂} (similar-EApp sim sim₁) 
    = similar-EApp (lemma2 {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {f₁} {f₂} sim) 
                   (lemma2 {A} {var₁} {var₂} {Γ} {Γ'} {et} {a₁} {a₂} sim₁) 

lift-similar : ∀ {A var₁ var₂} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                 {et : Γ ↝ Γ'} {e : Imp (en₁2Ctx (Γ2en₁ Γ)) A} {e' : ATInt var₂ A} →  
                 Similar {A} {var₁} {var₂} Γ e e' → 
                 Similar {A} {var₁} {var₂} Γ' (lift A (etG2S et) e) e'
lift-similar {AInt} sim = sim
lift-similar {AFun A A₁} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} sim 
    = λ {Γ''} {v} {v'} et₁ simvv' → this {Γ''} {v} {v'} et₁ simvv'
       where this : ∀ {Γ''} {v} {v'} et₁ simvv' → Similar Γ'' (e (↝-trans (etG2S et) (etG2S et₁)) v) (e' v')
             this {Γ''} {v} {v'} et₁ simvv' rewrite etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {Γ''} {et} {et₁}
                  = sim {Γ''} {v} {v'} (↝-trans et et₁) simvv'
lift-similar {D x} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} sim rewrite lemma1≡ {x} {var₁} {var₂} {Γ} {Γ'} {et} {e} 
    = lemma2 {x} {var₁} {var₂} {Γ} {Γ'} {extend-hd et} {Exp2exp (Γ2en₁ Γ') (elevate (↝↝-base (etG2S et)) e)} {e'} sim


lift-similar-env : ∀ {Δ var₁ var₂} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                     {et : Γ ↝ Γ'} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} {en : Env var₂ Δ} →
                    similar-env {var₁} {var₂} {Γ} {Δ} aen en → 
                    similar-env {var₁} {var₂} {Γ'} {Δ} (liftEnv (etG2S et) aen) en 
lift-similar-env [] = []
lift-similar-env {A ∷ Δ} {var₁} {var₂} {Γ} {Γ'} {et} {cons e aen} {cons e' en}  (scons x sim) 
   --= {!lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x  !}
   --= {!lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim!}
    = scons (lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x) 
            (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim) 
      -- scons (lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x) 
      --       (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim)

Exp2expEVar≡ : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} {v₁ : var₁ A} {v₂ : var₂ A} 
                 {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                 {et : ((A , v₁ , v₂) ∷ Γ) ↝ Γ'} →
                 Exp2exp (Γ2en₁ Γ') (EVar {τ = A} (elevate-var {A ∷ (en₁2Ctx (Γ2en₁ Γ))} {en₁2Ctx (Γ2en₁ Γ')} {A} (etG2S et) hd)) ≡ EVar v₁
Exp2expEVar≡ {A} {var₁} {var₂} {v₁} {v₂} {Γ} {.((A , v₁ , v₂) ∷ Γ)} {↝-refl} = refl
Exp2expEVar≡ {A} {var₁} {var₂} {v₁} {v₂} {Γ} {(τ ∷ Γ')} {↝-extend et} 
   = Exp2expEVar≡ {A} {var₁} {var₂} {v₁} {v₂} {Γ} {Γ'} {et}

A∈Γ↝Γ' : ∀ {A} {Γ : List A} {Γ' : List A} {α : A} →
           (et : (α ∷ Γ) ↝ Γ') → α ∈ Γ'
A∈Γ↝Γ' ↝-refl = hd
A∈Γ↝Γ' (↝-extend et) = tl (A∈Γ↝Γ' et)  

mutual
  similar-Exp2Similar-Embed : ∀ {α} {l : liftable1 α}
                              {var₁ : Type → Set} {var₂ : Type → Set} 
                              {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                              {e : Exp (en₁2Ctx (Γ2en₁ Γ)) (typeof α)} {e' : exp var₂ (typeof α)} →
                              similar-Exp Γ (Exp2exp (Γ2en₁ Γ) e) e' →
                              Similar Γ (Embed l e) (embed l e')
  similar-Exp2Similar-Embed {AInt} {()} sim
  similar-Exp2Similar-Embed {AFun α α₁} {Func l l₁} {var₁} {var₂} {Γ} {e} {e'} sim 
     = λ {Γ'} {v} {v'} et simvv' →
           similar-Exp2Similar-Embed {α₁} {l₁} {var₁} {var₂} {Γ'}
           {EApp (elevate (↝↝-base (etG2S et)) e) (Lift' l v)}
           {EApp e' (lift' l v')} (that {Γ'} {et} {v} {v'} {simvv'})   
       where that : ∀ {Γ'} {et : Γ ↝ Γ'} {v} {v'} {simvv' : Similar Γ' v v'} →       
                      similar-Exp Γ'
                         (Exp2exp (Γ2en₁ Γ') (EApp (elevate (↝↝-base (etG2S et)) e) (Lift' l v)))
                         (EApp e' (lift' l v'))
             that {Γ'} {et} {v} {v'} {simvv'}
               rewrite Exp2exp-EApp≡ {typeof α} {typeof α₁} {var₁} {Γ2en₁ Γ'} {elevate (↝↝-base (etG2S et)) e} {Lift' l v}
               = similar-EApp (this {Γ'} {et})
                   (Lift-Similar {α} {var₁} {var₂} {Γ'} {l} {v} {v'} simvv') 
                where
                 this : ∀ {Γ'} {et : Γ ↝ Γ'} → similar-Exp Γ' (Exp2exp (Γ2en₁ Γ') (elevate (↝↝-base (etG2S et)) e)) e'
                 this {Γ'} {et}
                      rewrite sym (lemma1≡ {Fun (typeof α) (typeof α₁)} {var₁} {var₂} {Γ} {Γ'} {et} {e})
                         = lemma2 {Fun (typeof α) (typeof α₁)} {var₁} {var₂} {Γ} {Γ'}
                             {extend-hd et} {Exp2exp (Γ2en₁ Γ) e} {e'} sim 
  similar-Exp2Similar-Embed {D x} {base} sim = sim

  Lift-Similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {l : liftable1 A} 
                 {v : Imp (en₁2Ctx (Γ2en₁ Γ)) A} {v' : ATInt var₂ A} →
                 Similar Γ v v' →
                 similar-Exp Γ (Exp2exp (Γ2en₁ Γ) (Lift' l v)) (lift' l v')
  Lift-Similar {(D x)} {var₁} {var₂} {Γ} {base} sim = sim
  Lift-Similar {(AFun α₁ α₂)} {var₁} {var₂} {Γ} {Func l l₁} {v} {v'} sim 
      rewrite Exp2expELam≡ {typeof α₁} {typeof α₂} {var₁} {Γ2en₁ Γ} {Lift' l₁ (v (↝-extend ↝-refl) (Embed l (EVar hd)))}
      = similar-ELam (λ v₁ v₂ →
                          Lift-Similar {α₂} {var₁} {var₂} {(typeof α₁ , v₁ , v₂) ∷ Γ} {l₁}
                          {v (↝-extend ↝-refl) (Embed l (EVar hd))} {v' (embed l (EVar v₂))}
                          (sim {(typeof α₁ , v₁ , v₂) ∷ Γ} {Embed l (EVar hd)}
                           {embed l (EVar v₂)} (↝-extend ↝-refl)
                           (similar-Exp2Similar-Embed {α₁} {l} {var₁} {var₂}
                            {(typeof α₁ , v₁ , v₂) ∷ Γ} {EVar hd} {EVar v₂} (this {v₁} {v₂}))))
       where this : ∀ {v₁} {v₂} → similar-Exp ((typeof α₁ , v₁ , v₂) ∷ Γ) (Exp2exp (Γ2en₁ ((typeof α₁ , v₁ , v₂) ∷ Γ)) (EVar hd)) (EVar v₂)
             this {v₁} {v₂} = similar-EVar hd 
-- Embed-similar-Func : ∀ {α₁ α₂} {var₁ : Type → Set} {var₂ : Type → Set} {l : liftable1 α₁} {l₁ : liftable1 α₂} 
--                         {v₁ : var₁ (Fun (typeof α₁) (typeof α₂))} {v₂ : var₂ (Fun (typeof α₁) (typeof α₂))}
--                         {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
--                         {v : Imp (en₁2Ctx (Γ2en₁ Γ')) α₁} {v' : ATInt var₂ α₁}
--                         {et : ((Fun (typeof α₁) (typeof α₂) , v₁ , v₂) ∷ Γ) ↝ Γ'} →
--                         Similar Γ' v v' →
--                         Similar Γ'
--                         (Embed l₁ (EApp (EVar (elevate-var (etG2S et) hd)) (Lift' l v)))
--                         (embed l₁ (EApp (EVar v₂) (lift' l v'))) 
-- Embed-similar-Func {α₁} {(D x)} {var₁} {var₂} {l} {base} {v₁} {v₂} {Γ} {Γ'} {v} {v'} {et} simvv' 
--       = {!this!}
--          where this : similar-Exp Γ'
--                       (Exp2exp (Γ2en₁ Γ')
--                       (EApp (EVar (elevate-var (etG2S et) hd)) (Lift' l v)))
--                       (EApp (EVar v₂) (lift' l v'))
--                this 
--                     rewrite Exp2expEApp≡ {typeof α₁} {x} {var₁} {Γ2en₁ Γ'} 
--                                     {EVar {τ = Fun (typeof α₁) x} 
--                             (elevate-var  {(Fun (typeof α₁) x) ∷ (en₁2Ctx (Γ2en₁ Γ))} {en₁2Ctx (Γ2en₁ Γ')} {Fun (typeof α₁) x} 
--                             (etG2S et) hd)} {Lift' l v}   |
--                         Exp2expEVar≡ {Fun (typeof α₁) x} {var₁} {var₂} {v₁} {v₂} {Γ} {Γ'} {et}
--                 = {!similar-EApp (similar-EVar (A∈Γ↝Γ' et)) 
--                                (Lift-similar {α₁} {var₁} {var₂} {Γ'} {l} {v} {v'} simvv')!}
 
                      
-- Embed-similar-Func {α₁} {(AFun α₂ α₃)} {var₁} {var₂} {l} {Func l₁ l₂} simvv' = {!!}
  
-- mutual
--     Embed-similar : ∀ {α : AType} {var₁ : Type → Set} {var₂ : Type → Set} 
--                   {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {l : liftable1 α} 
--                   {v₁ : var₁ (typeof α)} {v₂ : var₂ (typeof α)} →
--                   Similar ((typeof α , v₁ , v₂) ∷ Γ) (Embed l (EVar hd)) (embed l (EVar v₂))
--     Embed-similar {(D x)} {var₁} {var₂} {Γ} {base} {v₁} {v₂} = similar-EVar hd
--     Embed-similar {AFun α₁ α₂} {var₁} {var₂} {Γ} {Func l l₁} {v₁} {v₂} 
--       = λ {Γ'} {v} {v'} et simvv' →
--             this {Γ'} {α₁} {α₂} {v} {v'} {v₁} {v₂} {et} {l} {l₁} {simvv'}
--          where this : ∀ {Γ'} {α₁} {α₂} {v : Imp (en₁2Ctx (Γ2en₁ Γ')) α₁} {v' : ATInt var₂ α₁}
--                         {v₁ : var₁ (Fun (typeof α₁) (typeof α₂))}
--                         {v₂ : var₂ (Fun (typeof α₁) (typeof α₂))} 
--                         {et : ((Fun (typeof α₁) (typeof α₂) , v₁ , v₂) ∷ Γ) ↝ Γ'} 
--                         {l : liftable1 α₁} {l₁ : liftable1 α₂} {simvv' : Similar Γ' v v'} → 
--                        Similar Γ'
--                       (Embed l₁ (EApp (EVar (elevate-var (etG2S et) hd)) (Lift' l v)))
--                       (embed l₁ (EApp (EVar v₂) (lift' l v')))
--                this {Γ'} {α₁} {(D x)} {v} {v'} {v₁} {v₂} {et} {l} {base} {simvv'}
--                     rewrite Exp2expEApp≡ {typeof α₁} {x} {var₁} {Γ2en₁ Γ'} 
--                                 {EVar {τ = Fun (typeof α₁) x} 
--                              (elevate-var  {(Fun (typeof α₁) x) ∷ (en₁2Ctx (Γ2en₁ Γ))} {en₁2Ctx (Γ2en₁ Γ')} {Fun (typeof α₁) x} 
--                              (etG2S et) hd)} {Lift' l v}   |
--                          Exp2expEVar≡ {Fun (typeof α₁) x} {var₁} {var₂} {v₁} {v₂} {Γ} {Γ'} {et} 
--                   = similar-EApp (similar-EVar (A∈Γ↝Γ' et)) (Lift-similar {α₁} {var₁} {var₂} {Γ'} {l} {v} {v'} simvv')
--                this {Γ'} {α₁} {(AFun α₂ α₃)} {v} {v'} {v₁} {v₂} {et} {l} {Func l₁ l₂} {simvv'}  
--                   = {!λ {Γ''} {v₃} {v''} et₁ simv₃v'' →
--                      this {Γ''} {α₂} {α₃} 
--                           {v₃} {v''}
--                           {} {} {}
--                           {l₁} {l₂}
--                           {simv₃v''}!} 
--   -- Embed-similar {.(AFun α₁ AInt)} {var₁} {var₂} {Γ} {Func {α₁} {AInt} l ()}
--   -- Embed-similar {.(AFun α₁ (D x))} {var₁} {var₂} {Γ} {Func {α₁} {D x} l base} {v₁} {v₂}  
--   --   = λ {Γ'} {v} {v'} et simvv' → this {Γ'} {v} {v'} {et} {simvv'}
--   --     where this : ∀ {Γ' v v' et} {simvv' : Similar Γ' v v'} → similar-Exp Γ'
--   --                                  (Exp2exp (Γ2en₁ Γ')
--   --                                   (EApp (EVar (elevate-var (etG2S et) hd)) (Lift' l v)))
--   --                                   (EApp (EVar v₂) (lift' l v'))
--   --           this {Γ'} {v} {v'} {et} {simvv'}
--   --               rewrite Exp2expEApp≡ {typeof α₁} {x} {var₁} {Γ2en₁ Γ'} 
--   --                                   {EVar {τ = Fun (typeof α₁) x} 
--   --                           (elevate-var  {(Fun (typeof α₁) x) ∷ (en₁2Ctx (Γ2en₁ Γ))} {en₁2Ctx (Γ2en₁ Γ')} {Fun (typeof α₁) x} 
--   --                           (etG2S et) hd)} {Lift' l v}   |
--   --                       Exp2expEVar≡ {Fun (typeof α₁) x} {var₁} {var₂} {v₁} {v₂} {Γ} {Γ'} {et}
--   --               = similar-EApp (similar-EVar (A∈Γ↝Γ' et)) 
--   --                              (Lift-similar {α₁} {var₁} {var₂} {Γ'} {l} {v} {v'} simvv')
--   -- Embed-similar {(AFun α₁ (AFun α₂ (D x)))} {var₁} {var₂} {Γ} {Func {.α₁} {.(AFun α₂ (D x))} l (Func l₁ base)} 
--   --               = {!can be proven,similar to above!}
--   -- Embed-similar {(AFun α₁ (AFun α₂ (AFun α₃ α₄)))} {var₁} {var₂} {Γ} {Func {.α₁} {.(AFun α₂ (AFun α₃ α₄))} l (Func l₁ (Func l₂ l₃))} 
--   --               = {!!}


--     Lift-similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {l : liftable1 A} 
--                  {v : Imp (en₁2Ctx (Γ2en₁ Γ)) A} {v' : ATInt var₂ A} →
--                  Similar Γ v v' →
--                  similar-Exp Γ (Exp2exp (Γ2en₁ Γ) (Lift' l v)) (lift' l v')
--     Lift-similar {(D x)} {var₁} {var₂} {Γ} {base} sim = sim
--     Lift-similar {(AFun α₁ α₂)} {var₁} {var₂} {Γ} {Func l l₁} {v} {v'} sim 
--       --rewrite Exp2expELam≡ {typeof α₁} {typeof α₂} {var₁} {Γ2en₁ Γ} {Lift' l₁ (v (↝-extend ↝-refl) (Embed l (EVar hd)))}
--       = {!similar-ELam (λ v₁ v₂ →
--                         Lift-similar {l = l₁}
--                         (sim {(typeof α₁ , v₁ , v₂) ∷ Γ} {Embed l (EVar hd)}
--                          {embed l (EVar v₂)} (↝-extend ↝-refl)
--                          (Embed-similar {α₁} {var₁} {var₂} {Γ} {l} {v₁} {v₂})))
--         !}

proj-correct : ∀ {Δ A var₁ var₂} {Γ :  List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {e : AExp Δ A} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} 
                 {en : Env var₂ Δ} →
               similar-env {var₁} {var₂} {Γ} {Δ} aen en → 
               let e' = proj e en in
               Similar {A} {var₁} {var₂} Γ (PE e aen) (pe e')
proj-correct {[]} {A} {var₁} {var₂} {Γ} {Var ()} []
proj-correct {A₁ ∷ Δ} {.A₁} {var₁} {var₂} {Γ} {Var hd} (scons x₁ sim) = x₁
proj-correct {A₁ ∷ Δ} {A} {var₁} {var₂} {Γ} {Var (tl x)} (scons x₁ sim) 
  = proj-correct {Δ} {A} {var₁} {var₂} {Γ} {Var x} sim
proj-correct {Δ} {AInt} {var₁} {var₂} {Γ} {AInt x} sim = refl
proj-correct {Δ} {AInt} {var₁} {var₂} {Γ} {AAdd e e₁} sim 
  rewrite proj-correct {Δ} {AInt} {var₁} {var₂} {Γ} {e} sim | proj-correct {Δ} {AInt} {var₁} {var₂} {Γ} {e₁} sim
  = refl
proj-correct {Δ} {(AFun α₁ α₂)} {var₁} {var₂} {Γ} {ALam e} {aen} {en} sim 
  = λ {Γ'} {v} {v'} et simvv' →
        proj-correct {α₁ ∷ Δ} {α₂} {var₁} {var₂} {Γ'} {e}
        {cons v (liftEnv (etG2S et) aen)} {cons v' en}
        (scons {A = α₁} {Δ = Δ} {e = v} {e' = v'}
         {aen = liftEnv (etG2S et) aen} {en = en} simvv'
         (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim))
proj-correct {Δ} {B} {var₁} {var₂} {Γ} {AApp {α₂ = A} e e₁} {aen} {en} sim 
  = proj-correct {Δ} {AFun A B} {var₁} {var₂} {Γ} {e} {aen} {en} sim
      {Γ} {PE e₁ aen} {pe (proj e₁ en)} ↝-refl
      (proj-correct {Δ} {A} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
proj-correct {Δ} {(D Int)} {var₁} {var₂} {Γ} {DInt x} sim 
  rewrite Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ}
  = similar-ECst
proj-correct {Δ} {(D Int)} {var₁} {var₂} {Γ} {DAdd e e₁} {aen} {en} sim 
  rewrite Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ} {PE e aen} {PE e₁ aen}
  = similar-EAdd (proj-correct {Δ} {D Int} {var₁} {var₂} {Γ} {e} {aen} {en} sim) 
                 (proj-correct {Δ} {D Int} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
proj-correct {Δ} {(D (Fun τ₁ τ₂))} {var₁} {var₂} {Γ} {DLam e} {aen} {en} sim 
  rewrite Exp2exp-ELam≡ {τ₁} {τ₂} {var₁} {Γ2en₁ Γ} {PE e (cons (EVar hd) (liftEnv (↝-extend ↝-refl) aen))}
  = similar-ELam {A = τ₁} {B = τ₂} 
                 {f₁ = λ v → Exp2exp ((τ₁ , v) ∷ Γ2en₁ Γ)(PE e (cons (EVar hd) (liftEnv (↝-extend ↝-refl) aen)))} 
                 {f₂ = λ v → pe (proj e (cons (EVar v) en))}  
    (λ v₁ v₂ →
         proj-correct {D τ₁ ∷ Δ} {D τ₂} {var₁} {var₂} {(τ₁ , v₁ , v₂) ∷ Γ}
         {e} {cons (EVar hd) (liftEnv (↝-extend ↝-refl) aen)}
         {cons (EVar v₂) en} (this {v₁} {v₂}))
    where this : ∀ {v₁} {v₂} → similar-env (cons (EVar hd) (liftEnv (↝-extend ↝-refl) aen)) (cons (EVar v₂) en)
          this {v₁} {v₂} = scons (similar-EVar hd) (lift-similar-env sim)
proj-correct {Δ} {(D τ₁)} {var₁} {var₂} {Γ} {DApp {τ₂ = τ₂} e e₁} {aen} {en} sim 
  rewrite Exp2exp-EApp≡ {τ₂} {τ₁} {var₁} {Γ2en₁ Γ} {PE e aen} {PE e₁ aen}
  = similar-EApp (proj-correct {Δ} {D (Fun τ₂ τ₁)} {var₁} {var₂} {Γ} {e} {aen} {en} sim) 
                 (proj-correct {Δ} {D τ₂} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
proj-correct {Δ} {.(D (typeof α))} {var₁} {var₂} {Γ} {e = ↓ {α} l e} {aen} {en} sim 
  = Lift-Similar {α} {var₁} {var₂} {Γ} {l} {PE e aen} {pe (proj e en)}
      (proj-correct {e = e} sim)

