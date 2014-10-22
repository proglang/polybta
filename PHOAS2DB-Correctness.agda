module PHOAS2DB-Correctness where

--under construction
--translating from "PHOAS" terms to "De Bruijn" terms
module PHOAS2DB where
-- open import Data.Nat hiding  (_<_;_⊔_;_*_;equal)
open import Data.Bool hiding (_∨_) 
-- open import Function using (_∘_)
-- open import Data.List
-- open import Data.Nat.Properties
-- open import Relation.Nullary
-- open import Relation.Binary.PropositionalEquality 
open import Data.Empty
open import Data.Product
-- open import Data.Sum
-- open import Data.Unit
open import Lib
open Auxiliaries


-- infix 4 _∈_
-- data _∈_ {A : Set} : A → List A → Set where
--     hd : ∀ {x xs} → x ∈ (x ∷ xs)
--     tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)


--   -- Extension of a list by consing elements at the front. 
-- data _↝_ {A : Set} : List A → List A → Set where
--     refl   : ∀ {Γ}      → Γ ↝ Γ
--     extend : ∀ {Γ Γ' τ} → Γ ↝ Γ' → Γ ↝ (τ ∷ Γ')
  
--   -- Combining two transitive extensions. 
-- lem-↝-trans : ∀ {A : Set}{Γ Γ' Γ'' : List A} → Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
-- lem-↝-trans Γ↝Γ' refl = Γ↝Γ'
-- lem-↝-trans Γ↝Γ' (extend Γ'↝Γ'') = extend (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
  
--   -- Of course, ↝-refl is the identity for combining two extensions.
-- lem-↝-refl-id : ∀ {A : Set} {Γ Γ' : List A} →
--                     (Γ↝Γ' : Γ ↝ Γ') →
--                     Γ↝Γ' ≡ (lem-↝-trans refl Γ↝Γ')  
-- lem-↝-refl-id refl = refl
-- lem-↝-refl-id (extend Γ↝Γ') = cong extend (lem-↝-refl-id Γ↝Γ')

--   -- Extending a list in the middle: 
-- data _↝_↝_ {A : Set} : List A → List A → List A → Set where
--     -- First prepend the extension list to the common suffix
--     refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ'' 
--     -- ... and then add the common prefix
--     extend : ∀ {Γ Γ' Γ'' τ} →
--                  Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'') 

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
data liftable : AType → Set where
  base : ∀ {x : Type} → liftable (D x)
  Func : ∀ {α₁ α₂ : AType} 
          → liftable α₁ → liftable α₂
          → liftable (SFun α₁ α₂)


 
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
  --↑    : ∀  {α} → liftable α → AExp Δ α → AExp Δ (D (typeof α)) 

------------------------------
--lifting typing environment Δ
------------------------------
Lift-var : ∀ {Δ Δ'} {α : AType} → Δ ↝ Δ' → α ∈ Δ → α ∈ Δ'
Lift-var refl x = x
Lift-var (extend Δ↝Δ') x = tl (Lift-var Δ↝Δ' x)


Lift-var2 : ∀ {Δ Δ' Δ'' α} → Δ ↝ Δ' ↝ Δ'' → α ∈ Δ → α ∈ Δ''
Lift-var2 (refl x) x₁ = Lift-var x x₁
Lift-var2 (extend Δ↝Δ'↝Δ'') hd = hd
Lift-var2 (extend Δ↝Δ'↝Δ'') (tl x) = tl (Lift-var2 Δ↝Δ'↝Δ'' x)




-- Elevate : ∀ {Δ Δ' Δ'' α} → Δ ↝ Δ' ↝ Δ'' → AExp Δ α → AExp Δ'' α
-- Elevate Δ↝Δ'↝Δ'' (Var x) = Var (Lift-var2 Δ↝Δ'↝Δ'' x)
-- Elevate Δ↝Δ'↝Δ'' (SCst x) = SCst x
-- Elevate Δ↝Δ'↝Δ'' (SAdd e e₁) = SAdd (Elevate Δ↝Δ'↝Δ'' e) (Elevate Δ↝Δ'↝Δ'' e₁)
-- Elevate Δ↝Δ'↝Δ'' (SLam e) = SLam (Elevate (extend Δ↝Δ'↝Δ'') e)
-- Elevate Δ↝Δ'↝Δ'' (SApp e e₁) = SApp (Elevate Δ↝Δ'↝Δ'' e) (Elevate Δ↝Δ'↝Δ'' e₁)
-- Elevate Δ↝Δ'↝Δ'' (DCst x) = DCst x
-- Elevate Δ↝Δ'↝Δ'' (DAdd e e₁) = DAdd (Elevate Δ↝Δ'↝Δ'' e) (Elevate Δ↝Δ'↝Δ'' e₁)
-- Elevate Δ↝Δ'↝Δ'' (DLam e) = DLam (Elevate (extend Δ↝Δ'↝Δ'') e)
-- Elevate Δ↝Δ'↝Δ'' (DApp e e₁) = DApp (Elevate Δ↝Δ'↝Δ'' e) (Elevate Δ↝Δ'↝Δ'' e₁)
-- Elevate Δ↝Δ'↝Δ'' (↑ l e) = ↑ l (Elevate Δ↝Δ'↝Δ'' e)



-- lift-AExp : ∀ {Δ : List AType} {Δ' : List AType} {α} → Δ ↝ Δ' → AExp Δ α → AExp Δ' α
-- lift-AExp Δ↝Δ' e = Elevate (refl Δ↝Δ') e
-----------------------
--[reify] and [reflect]
-----------------------
-- mutual
--   reify   : ∀ {Δ α} → liftable α → AExp Δ α → AExp Δ (D (typeof α))
--   reify base e = e
--   reify {Δ} {SFun (D x) α₂} (Func base l₁) e = DLam (reify l₁ (SApp (lift-AExp (extend refl) e) (Var {α = D x} hd)))
--   reify {Δ} {SFun (SFun α₁ α₂) α₃} (Func (Func l l₁) l₂) e 
--      = DLam (reify l₂
--                (SApp (lift-AExp (extend refl) e)
--                 (reflect (Func l l₁)
--                  (Var {α = D (Fun (typeof α₁) (typeof α₂))} hd))))

--   reflect : ∀ {Δ α} → liftable α → AExp Δ (D (typeof α)) → AExp Δ α
--   reflect base e = e
--   reflect {Δ} {SFun (D x) α₂} (Func base l₁) e = SLam (reflect l₁ (DApp (lift-AExp (extend refl) e) (Var {α = D x} hd)))
--   reflect {Δ} {SFun (SFun α₁ α₂) α₃} (Func (Func l l₁) l₂) e 
--      = SLam (reflect l₂
--                (DApp (lift-AExp (extend refl) e)
--                 (reify (Func l l₁) (Var {α = SFun α₁ α₂} hd))))





-- ----------------------------
-- -- The interpreter of [Type]
-- ----------------------------
-- EImp : Type → Set
-- EImp Num = ℕ
-- EImp (Fun ty ty₁) = EImp ty → EImp ty₁



-- -----------------------------
-- -- The interpreter of [AType]
-- -----------------------------
-- Imp : Ctx → AType → Set
-- Imp Γ (SNum) = ℕ
-- Imp Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (Imp Γ' α₁ → Imp Γ' α₂)
-- Imp Γ (D σ) = Exp Γ σ



-------------
--environment
-------------
-- data AEnv (Γ : Ctx) : ACtx → Set where
--   [] : AEnv Γ []
--   cons : ∀ {Δ} {α : AType} → Imp Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)


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
  ↑    : ∀  {α} → liftable α → aexp var α → aexp var (D (typeof α))
----------------------------------
--annotated PHOAS term-alternative
----------------------------------
svar : AType → Set
svar aty = ℕ
--use de


aexp-1 : aexp svar SNum
aexp-1 = Var 5

-----------------------
--interpreter of [Type]
-----------------------
TInt : Type → Set
TInt Num = ℕ
TInt (Fun ty ty₁) = TInt ty → TInt ty₁

------------------------
--interpreter of [AType]
------------------------
ATInt : (Type → Set) → AType → Set
ATInt var SNum = ℕ
ATInt var (SFun aty aty₁) = ATInt var aty → ATInt var aty₁
ATInt var (D x) = exp var x


---------------------------------
--transforming the type of [AENV]
---------------------------------
-----------
--axiom one
-----------
-- FUN2fun : ∀ {A B Γ} → (TInt A → exp TInt B) → Exp (A ∷ Γ) B
-- FUN2fun {A} {B} {Γ} f = {!!}
-- fstargu : Type → Type
-- fstargu Int = Int
-- fstargu (Fun ty ty₁) = ty

-- mutual
--   Exp2exp : ∀ {τ Γ} {var : Type → Set} → Exp Γ τ → exp var τ
--   Exp2exp (EVar x) = {!!}
--   Exp2exp (EInt x) = ECst x
--   Exp2exp (EAdd RE RE₁) = EAdd (Exp2exp RE) (Exp2exp RE₁)
--   Exp2exp (ELam RE) = ELam (λ x → Exp2exp RE)
--   Exp2exp (EApp RE RE₁) = EApp (Exp2exp RE) (Exp2exp RE₁)  
  
--   exp2Exp : ∀ {τ Γ} {var var' : Type → Set} → exp var' τ → Exp Γ τ
--   exp2Exp (EVar x) = {!!}
--   exp2Exp (ECst x) = EInt x
--   exp2Exp (EAdd re re₁) = EAdd (exp2Exp re) (exp2Exp re₁)
--   exp2Exp {Fun A B} {Γ} {var} {λ v → var (fstargu v)} (ELam x) = {!(λ v → exp2Exp {B} {A ∷ Γ} {var} (x v))!}
--   exp2Exp (EApp re re₁) = EApp (exp2Exp re) (exp2Exp re₁)

-- mutual
--   Imp2AT : ∀ {α Γ} {var : Type → Set}  → Imp Γ α → ATInt var α
--   Imp2AT {AInt} e = e 
--   Imp2AT {AFun a₁ α₂} {Γ} e = λ v → Imp2AT (e {Γ} ↝-refl (AT2Imp v))
--   Imp2AT {D τ} e = Exp2exp e

--   AT2Imp : ∀ {α Γ} {var : Type → Set}  → ATInt var α → Imp Γ α
--   AT2Imp {AInt} E = E
--   AT2Imp {AFun α₁ α₂} {Γ} E = λ Γ↝Γ' → λ v → AT2Imp (E (Imp2AT v))
  -- AT2Imp {D τ} E = exp2Exp E
 

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

--Where does [Env] come from?

-----------------------
--some auxiliary lemmas
-----------------------
lookupenv : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → A ∈ Δ → Env var Δ → ATInt var A
lookupenv hd (cons x l) = x
lookupenv (tl id) (cons x l) = lookupenv id l 



-- proj : ∀ {A : AType} {Δ : ACtx} {var : Type → Set}  → AExp Δ A → Env var Δ  → aexp (ATInt var) A
-- proj {A} {Δ} (Var x) env = Var (lookupenv x env)
-- proj {SNum} (SCst x) env = SCst x
-- proj (SAdd ae ae₁) env = SAdd (proj ae env) (proj ae₁ env)
-- proj {SFun α₁ α₂}  (SLam ae) env = SLam (λ x → proj ae (cons x env))
-- proj (SApp ae ae₁) env = SApp (proj ae env) (proj ae₁ env)
-- proj (DCst x) env = DCst x
-- proj (DAdd ae ae₁) env = DAdd (proj ae env) (proj ae₁ env)
-- proj {D (Fun τ₁ τ₂)} (DLam ae) env = DLam (λ v → proj ae (cons v env))
-- proj (DApp ae ae₁) env = DApp (proj ae env) (proj ae₁ env)
-- proj (↑ l e) env = {!!}
-- proj (reify l e) env

---------------------------------
--a generalized version of [proj]
---------------------------------
----------------------------
--alternative environment
----------------------------
-- data Env' : (AType → Set) → ACtx → Set₁ where
--   []   : ∀ var → Env' var []
--   cons : ∀ {Δ} {α : AType} {var : AType → Set} → var α → Env' var Δ → Env' var (α ∷ Δ)

-- -----------------------
-- --some auxiliary lemmas
-- -----------------------
-- lookupenv' : ∀ {A : AType} {Δ : ACtx} {var : AType → Set} → A ∈ Δ → Env' var Δ → var A
-- lookupenv' hd (cons x l) = x
-- lookupenv' (tl id) (cons x l) = lookupenv' id l 



-- proj' : ∀ {A : AType} {Δ : ACtx} {var : AType → Set}  → AExp Δ A → Env' var Δ  → aexp var A
-- proj' {A} {Δ} (Var x) env = Var (lookupenv' x env)
-- proj' {AInt} (AInt x) env = SCst x
-- proj' (AAdd ae ae₁) env = SAdd (proj' ae env) (proj' ae₁ env)
-- proj' {AFun α₁ α₂}  (ALam ae) env = SLam (λ x → proj' ae (cons x env))
-- proj' (AApp ae ae₁) env = SApp (proj' ae env) (proj' ae₁ env)
-- proj' (DInt x) env = DCst x
-- proj' (DAdd ae ae₁) env = DAdd (proj' ae env) (proj' ae₁ env)
-- proj' {D (Fun τ₁ τ₂)} (DLam ae) env = DLam (λ v → proj' ae (cons v env))
-- proj' (DApp ae ae₁) env = DApp (proj' ae env) (proj' ae₁ env)

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



lookupenv'' : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → ATInt var A → Env var Δ → A ∈ Δ
lookupenv'' {A} {.[]} {var} e ([]) = {!!}
lookupenv'' {A} e (cons {α = α} x l) = {!!} 

--var: λ τ → λ Γ' → Exp Γ' τ, where Γ' is extended from Γ
-- proj'' : ∀ {A : AType} {Δ : ACtx} {var : Type → Set} → aexp (ATInt var) A → Env var Δ → AExp Δ A
-- proj'' (Var x) env = Var (lookupenv'' x env)
-- --a typing context corresponding to "env" is enough
-- proj'' (SCst x) env = SCst x
-- proj'' (SAdd e e₁) env = SAdd (proj'' e env) (proj'' e₁ env)
-- proj'' {SFun A B} {var = var} (SLam x) env = {!!}
-- --ALam {!λ v → proj'' (x v) (cons v env)!}
-- proj'' (SApp e e₁) env = SApp (proj'' e env) (proj'' e₁ env)
-- proj'' (DCst x) env = DCst x
-- proj'' (DAdd e e₁) env = DAdd (proj'' e env) (proj'' e₁ env)
-- proj'' (DLam x) env = DLam {!λ v → proj'' (x v) (cons v env)!}
-- proj'' (DApp e e₁) env = DApp (proj'' e env) (proj'' e₁ env)



-----------------------------------------
--translation from [PHOAS] to [De Bruijn]
--alternative
-----------------------------------------
--some notes,
--a. regarding the choice of [var : AType → Set] in the type of [PHOAS] terms
--   we can set it as [Imp Γ] so that essentially the environment for [PHOAS] 
--   terms [en : Env var Δ] is the same as that for [De Bruijn] terms [aen : AEnv Γ Δ]
A≡B? : ∀ {A : AType} {B : AType} → Bool
A≡B? {SNum} {B} = {!!}
A≡B? {SFun A A₁} = {!!}
A≡B? {D x} = {!!}
 

A∈Δ? : ∀ {A : AType} {Δ : ACtx} → Bool 
A∈Δ? {A} {[]} = false
A∈Δ? {A} {x ∷ Δ} with A≡B? {A} {x} 
... | false = A∈Δ? {A} {Δ}
... | true  = true 

A∈Δ?T-id : ∀ {A : AType} {Δ : ACtx} → A∈Δ? {A} {Δ} ≡ true → A ∈ Δ
A∈Δ?T-id {A} {[]} ()
A∈Δ?T-id {A} {x ∷ Δ} A∈Δ = {!!}
 
-- BuildΔ : ∀ {A : AType} {Δ : ACtx} {var : AType → Set} → aexp var A 
--               → ACtx
-- BuildΔ {A} {Δ} {var} (Var x) with A∈Δ? {A} {Δ} 
-- ... | true  = Δ
-- ... | false = A ∷ Δ
-- BuildΔ {Δ = Δ} (SCst x) = Δ
-- BuildΔ {Δ = Δ} (SAdd e e₁) = BuildΔ {Δ = BuildΔ {Δ = Δ} e} e₁
-- BuildΔ {SFun A B} {Δ} {var} (SLam x) = {!!}
-- BuildΔ (SApp e e₁) = {!!}
-- BuildΔ (DCst x) = {!!}
-- BuildΔ (DAdd e e₁) = {!!}
-- BuildΔ (DLam x) = {!!}
-- BuildΔ (DApp e e₁) = {!!}  

data _∨_ (A : Set) (B : Set) : Set where
 ∨-introl : A → (A ∨ B)
 ∨-intror : B → (A ∨ B)
 
-- projp2d : ∀ {A : AType} {Δ : ACtx} {Γ : Ctx} {aen : AEnv Γ Δ} 
--             → aexp (Imp Γ) A → (AExp Δ A) ∨ (AExp (A ∷ Δ) A)
-- projp2d {A} {Δ} {Γ} {aen} (Var x) with A∈Δ? {A} {Δ} 
-- ... | false = ∨-intror (Var hd)
-- ... | true  = {!!}
-- projp2d (SCst x) = {!!}
-- projp2d (SAdd e e₁) = {!!}
-- projp2d (SLam x) = {!!}
-- projp2d (SApp e e₁) = {!!}
-- projp2d (DCst x) = {!!}
-- projp2d (DAdd e e₁) = {!!}
-- projp2d (DLam x) = {!!}
-- projp2d (DApp e e₁) = {!!}


PVar :  ACtx → AType → Set
PVar Δ A = ∀ {Δ'} → (A ∷ Δ) ↝ Δ' → AExp Δ' A
------------------------------
-----working interpreter [var]
------------------------------
pVar : AType → Set
pVar A = ∀ {Δ} {Δ'} → (A ∷ Δ) ↝ Δ' → AExp Δ' A
--intuition: When the corresponding De Bruijn expression is
--           not closed then [A] should appear in [Δ'] 
--           "somewhere";
--           When it is closed now restriction over the typing
--           context [Δ].



pVar' : AType → Set
pVar' A = ∀ {Δ} {Δ'} → Δ ↝ Δ' → AExp Δ' A 
-------------------------------------------------------------
-------------------------------------------------------------
PVar'' :  ACtx → AType → Set
PVar'' Δ A = ∀ {Δ'} →  Δ ↝ Δ' → AExp Δ' A


PVar' :  ACtx → AType → Set
PVar' Δ A = ∀ { Δ'} → Δ ↝ (A ∷ Δ') → AExp (A ∷ Δ') A


-- pvar :  Ctx → AType → Set
-- pvar Γ A = Imp Γ A


-- projP2D : ∀ {A : AType} {Δ : ACtx}  
--             {Γ : Ctx} {aen : AEnv Γ Δ} 
--             → aexp (AExp Δ) A  
--             → AExp Δ A
-- projP2D (Var x) = {!!}
-- projP2D (SCst x) = {!!}
-- projP2D (SAdd e e₁) = {!!}
-- projP2D (SLam x) = {!!}
-- projP2D (SApp e e₁) = {!!}
-- projP2D (DCst x) = {!!}
-- projP2D (DAdd e e₁) = {!!}
-- projP2D (DLam x) = {!!}
-- projP2D (DApp e e₁) = {!!}

--try 
-- projP2D' : ∀ {A : AType} {Δ} {Δ' : ACtx} {Δ'' : ACtx} 
--             → (A ∷ Δ) ↝ Δ' ↝ Δ''  
--             → aexp (PVar' Δ) A  
--             → AExp Δ'' A
-- projP2D' {A} {Δ} {Δ'} {Δ''} ext (Var x) = {!x {A ∷ Δ'} {Δ''}  !}
-- projP2D' ext (SCst x) = {!!}
-- projP2D' ext (SAdd e e₁) = {!!}
-- projP2D' ext (SLam x) = {!!}
-- projP2D' ext (SApp e e₁) = {!!}
-- projP2D' ext (DCst x) = {!!}
-- projP2D' ext (DAdd e e₁) = {!!}
-- projP2D' ext (DLam x) = {!!}
-- projP2D' ext (DApp e e₁) = {!!}




-- projP2D : ∀ {A : AType} {Δ'} {Δ : ACtx}  
--             → (A ∷ Δ') ↝ Δ   
--             → aexp (PVar Δ') A  
--             → AExp Δ A
-- projP2D {A} {Δ'} {Δ} shift (Var x) = x {Δ} shift
-- projP2D _ (SCst x) = SCst x
-- projP2D {SNum} {Δ}  shift (SAdd e e₁) 
--      = SAdd (projP2D {SNum} {Δ}  shift e) (projP2D {SNum} {Δ}  shift e₁)
-- projP2D {SFun A B} {Δ'} {Δ} shift (SLam x) 
--         = SLam {α₁ = A} {α₂ = B}
--             (projP2D {B} {Δ'} {A ∷ Δ} {!!}
--              (x
--               (λ {Δ'' : ACtx} (ext : (A ∷ Δ') ↝ Δ'') →
--                  lift-AExp {A ∷ Δ'} {Δ''} {A} ext (Var {α = A} hd))))

{-
ALam {α₁ = A} {α₂ = B} 
   (projP2D {B} {Δ'} {A ∷ Δ} {!(↝-extend {τ = A} shift)!}
      (x
       (λ {Δ'' : ACtx} (ext : (A ∷ Δ') ↝ Δ'') →
          lift-AExp {A ∷ Δ'} {Δ''} {A} ext (Var {α = A} hd)))) 
-}

{-
ALam {α₁ = A} {α₂ = B} 
   (projP2D {B} {A ∷ Δ} {A ∷ Δ'} {A ∷ Δ''} {}
      (x
       (λ {Δ'' : ACtx} (ext : (A ∷ Δ) ↝ Δ' ↝ Δ'') →
          lift-AExp {A ∷ Δ'} {Δ''} {A} ext (Var {α = A} hd)))) 
-}


-- (x (λ s' → lift-AExp s' {!!})))
-- projP2D _ (SApp e e₁) = {!!}
-- projP2D _ (DCst x) = {!!}
-- projP2D _ (DAdd e e₁) = {!!}
-- projP2D _ (DLam x) = {!!}
-- projP2D _ (DApp e e₁) = {!!}

-- ProjP2D : ∀ {A : AType} {Δ : ACtx} {Δ' : ACtx} {Γ : Ctx}
--             → Δ ↝ Δ'
--             → aexp (pvar Δ') A  
--             → AExp Δ A
-- ProjP2D shift (Var x) = {!!}
-- ProjP2D shift (SCst x) = {!!}
-- ProjP2D shift (SAdd e e₁) = {!!}
-- ProjP2D shift (SLam x) = ALam {!!}
-- ProjP2D shift (SApp e e₁) = {!!}
-- ProjP2D shift (DCst x) = {!!}
-- ProjP2D shift (DAdd e e₁) = {!!}
-- ProjP2D shift (DLam x) = {!!}
-- ProjP2D shift (DApp e e₁) = {!!} 

-----------------------------------------------------------------
-----translation from PHOAS term to De Bruijn term
-----------------------------------------------------------------
-- ProjP2D : ∀ {A : AType} {Δ} 
--             → (∀ Δ' → Δ' ↝ Δ) -- our typing context [Δ] has to be as 
--                               -- general as it can be meaning either 
--                               -- containing [A] as one element in case 
--                               -- of an open expression or any context in
--                               -- case a closed expression
--             → aexp pVar A  
--             → AExp Δ A
-- ProjP2D {A} {Δ} ext (Var x) = x {[]} {Δ} (ext (A ∷ []))
-- ProjP2D ext (SCst x) = SCst x
-- ProjP2D ext (SAdd e e₁) = SAdd (ProjP2D ext e) (ProjP2D ext e₁)
-- ProjP2D {SFun A B} {Δ} ext (SLam x) 
--      = SLam (ProjP2D (λ Δ' → extend (ext Δ'))
--                (x
--                 (λ {[]₁} {Δ₁} (ext₁ : (A ∷ []₁) ↝ Δ₁) →
--                    lift-AExp ext₁ (Var {α = A} hd))))
-- ProjP2D ext (SApp e e₁) = SApp (ProjP2D ext e) (ProjP2D ext e₁)
-- ProjP2D ext (DCst x) = DCst x
-- ProjP2D ext (DAdd e e₁) = DAdd (ProjP2D ext e) (ProjP2D ext e₁)
-- ProjP2D {D (Fun a b)} {Δ} ext (DLam x) 
--      = DLam (ProjP2D (λ Δ' → extend (ext Δ'))
--                (x
--                 (λ {[]₁} {Δ₁} (ext₁ : (D a ∷ []₁) ↝ Δ₁) →
--                    lift-AExp ext₁ (Var {α = D a} hd))))
-- ProjP2D ext (DApp e e₁) = DApp (ProjP2D ext e) (ProjP2D ext e₁)

-----------------------------------------------------
--note: translation from PHOAS term to De Bruijn term
--set [var : AType → Set] as [var : AType → nat] ?  
-----------------------------------------------------

-- exp2d1 : AExp ([]) (SFun SNum SNum)
-- exp2d1 = ProjP2D {!!} (SLam ((λ x → Var x) ))

-------------------------------------------------------------------
-- ProjP2D' : ∀ {A : AType} {Δ} 
--             → (∀ Δ' → Δ' ↝ Δ)
--             → aexp pVar' A  
--             → AExp Δ A
-- ProjP2D' {A} {Δ} ext (Var x) = x {Δ} {Δ} (ext Δ)
-- ProjP2D' ext (SCst x) = {!!}
-- ProjP2D' ext (SAdd e e₁) = {!!}
-- ProjP2D' {SFun A B} {Δ} ext (SLam x) 
--       = SLam {!!}
-- ProjP2D' ext (SApp e e₁) = {!!}
-- ProjP2D' ext (DCst x) = {!!}
-- ProjP2D' ext (DAdd e e₁) = {!!}
-- ProjP2D' ext (DLam x) = {!!}
-- ProjP2D' ext (DApp e e₁) = {!!}

--giving an [aexp var A] expression producing its typing context [Δ],
--producing environment instead of typing context
-- produceΔ : ∀ {A : AType}  → (Δ : ACtx) → aexp (λ A → A ∈ Δ) A → aexp (λ B → A ∈ (B ∷ Δ)) A
-- produceΔ {A} Δ (Var x) = Var hd
-- produceΔ Δ (SCst x) = {!!}
-- produceΔ Δ (SAdd e e₁) = {!!}
-- produceΔ {SFun A B} Δ (SLam x) = {!SLam (λ id → produceΔ {!!} {!!})!}
-- produceΔ Δ (SApp e e₁) = {!!}
-- produceΔ Δ (DCst x) = {!!}
-- produceΔ Δ (DAdd e e₁) = {!!}
-- produceΔ Δ (DLam x) = {!!}
-- produceΔ Δ (DApp e e₁) = {!!}

-- ------------------------------------
-----
--translation from [PHOAS] to [De Bruijn]
--alternative
-----------------------------------------
-------------------------------------
--the variable tagging function [var]
-------------------------------------
avar : AType → Set
avar _ = ℕ
----------------------------------------
--some auxilary data types and functions
----------------------------------------
data Option (A : Set) : Set where
  Some : A → Option A
  Nothing : Option A

Length : ∀ {A : Set} → List A → ℕ
Length [] = zero
Length (x ∷ ls) = suc (Length ls) 

ℕ≡? : ℕ → ℕ → Bool
ℕ≡? zero zero = true
ℕ≡? zero (suc m) = false
ℕ≡? (suc n) zero = false
ℕ≡? (suc n) (suc m) = ℕ≡? n m

Last : ∀ {A : Set} → List A → Option A
Last [] = Nothing
Last (x ∷ []) = Some x
Last (x ∷ x₁ ∷ ls) = Last (x₁ ∷ ls)

Last+ : ∀ {a : Set} {A : a} {B : a} {Δ : List a} → Last Δ ≡ Some A → Last (B ∷ Δ) ≡ Some A
Last+ {a} {A} {B} {[]} ()
Last+ {a} {A} {B} {x ∷ Δ} eq = eq

--Last∃ : ∀ {a : Set} {A : a} {Δ : List a} → Σ a \ x → Last (A ∷ Δ) ≡ Some x 

Tail : ∀ {A : Set} → List A → List A
Tail [] = []
Tail (x ∷ []) = []
Tail (x ∷ x₁ ∷ ls) = x ∷ Tail (x₁ ∷ ls)

∧-1 : ∀ {a} {b} → a ∧ b ≡ true → a ≡ true
∧-1 {true} eq = refl
∧-1 {false} () 

∧-2 : ∀ {a} {b} → a ∧ b ≡ true → b ≡ true
∧-2 {a} {true} eq = refl
∧-2 {true} {false} ()
∧-2 {false} {false} ()


eq_Type : ∀ {a : Type} {b : Type} → Bool 
eq_Type {Num} {Num} = true
eq_Type {Num} {Fun b b₁} = false
eq_Type {Fun a a₁} {Num} = false
eq_Type {Fun a a₁} {Fun b b₁} = (eq_Type {a} {b}) ∧ (eq_Type {a₁} {b₁})

open import Relation.Binary using (Decidable)
eq_Type' : Decidable {A = Type} {B = Type} (_≡_)
eq_Type' Num Num = yes refl
eq_Type' Num (Fun b b₁) = no (λ ())
eq_Type' (Fun a a₁) Num = no (λ ())
eq_Type' (Fun a a₁) (Fun b b₁) with eq_Type' a b | eq_Type' a₁ b₁ 
... | yes p1 | yes p2 = yes (cong₂ Fun p1 p2)
... | _ | no np = no f
  where f : Fun a a₁ ≡ Fun b b₁ → ⊥
        f p with a | b | a₁ | b₁ | p | np
        f p₁ | .b' | b' | .b₁' | b₁' | refl | np' = np' refl
... | no np | yes p = {!!}

   
eq_AType' : Decidable {A = AType} {B = AType} (_≡_)
eq_AType' a b = {!!}

eq_AType : {A : AType} {B : AType} → Bool
eq_AType {SNum} {SNum} = true
eq_AType {SNum} {SFun B B₁} = false
eq_AType {SNum} {D x} = false
eq_AType {SFun A A₁} {SNum} = false
eq_AType {SFun A A₁} {SFun B B₁} = (eq_AType {A} {B}) ∧ (eq_AType {A₁} {B₁}) 
eq_AType {SFun A A₁} {D x} = false
eq_AType {D x} {SNum} = false
eq_AType {D x} {SFun B B₁} = false
eq_AType {D x} {D x₁} = eq_Type {x} {x₁}

eq_Type≡ : ∀ {a} {b} → (eq_Type {a} {b} ≡ true) → a ≡ b 
eq_Type≡ = {!!}

eq_AType≡ : ∀ {A} {B} → ((eq_AType {A} {B}) ≡ true) → A ≡ B
eq_AType≡ {SNum} {SNum} eq = refl
eq_AType≡ {SNum} {SFun B B₁} ()
eq_AType≡ {SNum} {D x} ()
eq_AType≡ {SFun A A₁} {SNum} ()
eq_AType≡ {SFun A A₁} {SFun B B₁} eq = cong₂ SFun (eq_AType≡ {A} {B} eq1) (eq_AType≡ {A₁} {B₁} eq2)
  where eq1 : eq_AType {A} {B} ≡ true
        eq1 rewrite sym (∧-1 {eq_AType {A} {B}}{eq_AType {A₁} {B₁}} eq) = refl
        eq2 : eq_AType {A₁} {B₁} ≡ true
        eq2 rewrite sym (∧-2 {eq_AType {A} {B}} {eq_AType {A₁} {B₁}} eq)= refl    
      
eq_AType≡ {SFun A A₁} {D x} ()
eq_AType≡ {D x} {SNum} ()
eq_AType≡ {D x} {SFun B B₁} ()
eq_AType≡ {D x} {D x₁} eq rewrite eq_Type≡ {x} {x₁} eq = refl

---------------
--some examples
---------------
----------------------------------------------
--look-up function for "De Bruijn level index"
----------------------------------------------
-- lookUp : ℕ → ACtx → Option AType 
-- lookUp zero Δ with Last Δ 
-- ... | Nothing = Nothing
-- ... | Some x  = Some x
-- lookUp (suc n) [] = Nothing
-- lookUp (suc n) (x ∷ Δ) = lookUp n (Tail (x ∷ Δ))

-- lookUpZeroLast≡ : ∀ {Δ} {Δ'} → Last Δ ≡ Last Δ' → lookUp zero Δ ≡ lookUp zero Δ'
-- lookUpZeroLast≡ {[]} {[]} eq = refl
-- lookUpZeroLast≡ {[]} {x ∷ Δ'} eq = {!!}
-- lookUpZeroLast≡ {x ∷ Δ} {[]} eq = {!!}
-- lookUpZeroLast≡ {x ∷ Δ} {x₁ ∷ Δ'} eq = {!!}
-- --------------- 
-- --some examples
-- ---------------
-- lookup1 : ∀ {A} {l₁} {l₂} → lookUp (Length l₂) (l₁ ++ (A ∷ l₂)) ≡ Some A
-- lookup1 {A} {[]} {[]} = refl
-- lookup1 {A} {[]} {x ∷ l₂} = {!l₂!}
-- lookup1 {A} {x ∷ l₁} {l₂} = {!l₂!}

-- --------------------------------------------
--------------
--a different look-up function for "De Bruijn level index"
----------------------------------------------------------
LookUp : ℕ → ACtx → Option AType
LookUp n [] = Nothing
LookUp n (x ∷ Δ) with ℕ≡? n (Length Δ) 
... | true = Some x
... | false = LookUp n Δ

--well-formed [PHOAS] term
--------------------------
-- data wf {Δ : ACtx} : ∀ {A : AType} → aexp avar A → Set where
--   WF-Var : ∀ {A : AType} {n : ℕ} → lookUp n Δ ≡ Some A → wf {Δ} {A} (Var n)
--   WF-SCst : ∀ {n : ℕ} → wf {Δ} {SNum} (SCst n)
--   WF-SAdd : ∀ {e} {e'} → wf {Δ} {SNum} e → wf {Δ} {SNum} e' → wf {Δ} {SNum} (SAdd e e')
--   WF-SLam : ∀ {A : AType} {B : AType} {e : avar A → aexp avar B}
--               → wf {A ∷ Δ} {B} (e (Length Δ)) → wf {Δ} {SFun A B} (SLam e)
--   WF-SApp : ∀ {A : AType} {B : AType} {f : aexp avar (SFun A B)} {x : aexp avar A}
--               → wf {Δ} {SFun A B} f → wf {Δ} {A} x → wf {Δ} {B} (SApp f x)
--   WF-DCst : ∀ {n : ℕ} → wf {Δ} {D Num} (DCst n)
--   WF-DAdd : ∀ {e} {e'} → wf {Δ} {D Num} e → wf {Δ} {D Num} e' → wf {Δ} {D Num} (DAdd e e')
--   WF-DLam : ∀ {a : Type} {b : Type} {e : avar (D a) → aexp avar (D b)}
--               → wf {(D a) ∷ Δ} {D b} (e (Length Δ)) → wf {Δ} {D (Fun a b)} (DLam e)
--   WF-DApp : ∀ {a : Type} {b : Type} {f : aexp avar (D (Fun a b))} {x : aexp avar (D a)} 
--               → wf {Δ} {D (Fun a b)} f → wf {Δ} {D a} x → wf {Δ} {D b} (DApp f x)
-- --------------------------------------
--alternative well-formed [PHOAS] term
--------------------------------------
data WF {Δ : ACtx} : ∀ {A : AType} → aexp avar A → Set where
  WF-Var : ∀ {A : AType} {n : ℕ} → LookUp n Δ ≡ Some A → WF {Δ} {A} (Var n)
  WF-SCst : ∀ {n : ℕ} → WF {Δ} {SNum} (SCst n)
  WF-SAdd : ∀ {e} {e'} → WF {Δ} {SNum} e → WF {Δ} {SNum} e' → WF {Δ} {SNum} (SAdd e e')
  WF-SLam : ∀ {A : AType} {B : AType} {e : avar A → aexp avar B}
              → WF {A ∷ Δ} {B} (e (Length Δ)) → WF {Δ} {SFun A B} (SLam e)
  WF-SApp : ∀ {A : AType} {B : AType} {f : aexp avar (SFun A B)} {x : aexp avar A}
              → WF {Δ} {SFun A B} f → WF {Δ} {A} x → WF {Δ} {B} (SApp f x)
  WF-DCst : ∀ {n : ℕ} → WF {Δ} {D Num} (DCst n)
  WF-DAdd : ∀ {e} {e'} → WF {Δ} {D Num} e → WF {Δ} {D Num} e' → WF {Δ} {D Num} (DAdd e e')
  WF-DLam : ∀ {a : Type} {b : Type} {e : avar (D a) → aexp avar (D b)}
              → WF {(D a) ∷ Δ} {D b} (e (Length Δ)) → WF {Δ} {D (Fun a b)} (DLam e)
  WF-DApp : ∀ {a : Type} {b : Type} {f : aexp avar (D (Fun a b))} {x : aexp avar (D a)} 
              → WF {Δ} {D (Fun a b)} f → WF {Δ} {D a} x → WF {Δ} {D b} (DApp f x)
----------------------------------------
--"De Bruijn Level" to "De Bruijn Index"
----------------------------------------
-- DebLevel2Index : ∀ {n} {A} {Δ} → lookUp n Δ ≡ Some A → A ∈ Δ
-- DebLevel2Index {zero} {A} {[]} ()
-- DebLevel2Index {zero} {A} {x ∷ Δ} eq with eq_AType {A} {x} 
-- -- DebLevel2Index {zero} {A} {x ∷ Δ} eq | yes p = {!!}
-- -- DebLevel2Index {zero} {A} {x ∷ Δ} eq | no ¬p = tl {!DebLevel2Index {zero} {A} {Δ} {!!}!}
-- ... | true = {!hd!}
-- --... | false = tl (DebLevel2Index {zero} {A} {Δ} {!!})
-- DebLevel2Index {zero} {A} {x ∷ []} eq | false = {!!}
-- DebLevel2Index {zero} {A} {x ∷ x₁ ∷ Δ} eq | false = tl (DebLevel2Index {zero} {A} {x₁ ∷ Δ} {!!})
-- DebLevel2Index {suc n} {A} {[]} ()
-- DebLevel2Index {suc n} {A} {x ∷ Δ} eq = {!!}

---------------------------------------------------
--alternative "De Bruijn Level" → "De Bruijn Index"
---------------------------------------------------
-----------------------
--some auxiliary lemmas
--the following function [Some≡]
--corresponds to [inversion] tactic
--in Coq
-----------------------
Some≡ : ∀ {a : AType} {b : AType} → Some a ≡ Some b → a ≡ b
Some≡ {SNum} {SNum} eq = refl
Some≡ {SNum} {SFun b b₁} ()
Some≡ {SNum} {D x} ()
Some≡ {SFun a a₁} {SNum} ()
Some≡ {SFun a a₁} {SFun b b₁} eq = x
     where x : SFun a a₁ ≡ SFun b b₁
           x with a | b | a₁ | b₁ | eq 
           ... | a | .a | a₁ | .a₁ | refl = refl
Some≡ {SFun a a₁} {D x} ()
Some≡ {D x} {SNum} ()
Some≡ {D x} {SFun b b₁} ()
Some≡ {D x} {D x₁} eq = y
     where y : D x ≡ D x₁
           y with x | x₁ | eq
           ... | x | .x | refl = refl

DebLeveltoIndex : ∀ {n} {A} {Δ} → LookUp n Δ ≡ Some A → A ∈ Δ
DebLeveltoIndex {n} {A} {[]} ()
DebLeveltoIndex {n} {A} {x ∷ Δ} eq with ℕ≡? n (Length Δ) 
... | true rewrite Some≡ {x} {A} eq = hd
... | false = tl (DebLeveltoIndex {n} {A} {Δ} eq)

-----------------------------------------
--translation from [PHOAS] to [De Bruijn]
--given the variable tagging function [var]
-- avar : AType → Set
-- avar _ = ℕ
------------------------------------------
P2D : ∀ {A : AType} {Δ} 
            → (e : aexp avar A)
            → WF {Δ} {A} e 
            → AExp Δ A
P2D {A} {Δ} (Var x) (WF-Var x₁) = Var (DebLeveltoIndex x₁)
P2D (SCst x) wf-e = SCst x
P2D (SAdd e e₁) (WF-SAdd wf-e wf-e₁) = SAdd (P2D e wf-e) (P2D e₁ wf-e₁)
P2D {SFun A B} {Δ} (SLam x) (WF-SLam wf-e) = SLam (P2D {B} {A ∷ Δ} (x (Length Δ)) wf-e)
P2D (SApp e e₁) (WF-SApp wf-e wf-e₁) = SApp (P2D e wf-e) (P2D e₁ wf-e₁)
P2D (DCst x) wf-e = DCst x
P2D (DAdd e e₁) (WF-DAdd wf-e wf-e₁) = DAdd (P2D e wf-e) (P2D e₁ wf-e₁)
P2D {D (Fun A B)} {Δ} (DLam x) (WF-DLam wf-e) = DLam (P2D {D B} {D A ∷ Δ} (x (Length Δ)) wf-e)
P2D (DApp e e₁) (WF-DApp wf-e wf-e₁) = DApp (P2D e wf-e) (P2D e₁ wf-e₁)


--a. a function from a closed [PHOAS] term producing evidence that it is well-formed
---------------------
--closed [PHOAS] term
---------------------
data Closed {Δ : ACtx} : ∀ {A : AType} → aexp avar A → Set where
  closed-Var : ∀ {A : AType} {n : ℕ} → LookUp n Δ ≡ Some A → Closed {Δ} {A} (Var n)
  closed-SCst : ∀ {n : ℕ} → Closed {Δ} {SNum} (SCst n)
  closed-SAdd : ∀ {e} {e'} → Closed {Δ} {SNum} e → Closed {Δ} {SNum} e' → Closed {Δ} {SNum} (SAdd e e')
  closed-SLam : ∀ {A : AType} {B : AType} {e : avar A → aexp avar B}
              → Closed {A ∷ Δ} {B} (e (Length Δ)) → Closed {Δ} {SFun A B} (SLam e)
  closed-SApp : ∀ {A : AType} {B : AType} {f : aexp avar (SFun A B)} {x : aexp avar A}
              → Closed {Δ} {SFun A B} f → Closed {Δ} {A} x → Closed {Δ} {B} (SApp f x)
  closed-DCst : ∀ {n : ℕ} → Closed {Δ} {D Num} (DCst n)
  closed-DAdd : ∀ {e} {e'} → Closed {Δ} {D Num} e → Closed {Δ} {D Num} e' → Closed {Δ} {D Num} (DAdd e e')
  closed-DLam : ∀ {a : Type} {b : Type} {e : avar (D a) → aexp avar (D b)}
              → Closed {(D a) ∷ Δ} {D b} (e (Length Δ)) → Closed {Δ} {D (Fun a b)} (DLam e)
  closed-DApp : ∀ {a : Type} {b : Type} {f : aexp avar (D (Fun a b))} {x : aexp avar (D a)} 
              → Closed {Δ} {D (Fun a b)} f → Closed {Δ} {D a} x → Closed {Δ} {D b} (DApp f x)

--b. prove that the resulting term from [DB2PHOAS] is always well-formed

--c. isomorphism between two translations















{-

-- -------------------------------------
-------------------------------------------------
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


lift : ∀ {Γ Γ'} α → Γ ↝ Γ' → Imp Γ α → Imp Γ' α 
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


---------------------
--[lift'] and [embed]
---------------------
mutual 
  lift' : ∀ {Γ α} → liftable α → Imp Γ α → (Exp Γ (typeof α))
  lift' base v = v
  lift' {Γ} {SFun α₁ α₂} (Func l l₁) v = ELam ((λ x → lift' l₁ (v (extend {τ = typeof α₁} refl) x))
                                                 (embed l (EVar {Γ = typeof α₁ ∷ Γ} hd)))
 
  embed : ∀ {Γ α} → liftable α → Exp Γ (typeof α) → (Imp Γ α)
  embed base e = e
  embed {Γ} {SFun α₁ α₂} (Func l l₁) e = λ Γ↝Γ' v₁ → embed l₁ (EApp (liftE Γ↝Γ' e) (lift' l v₁))








 
PE : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → Imp Γ α
PE (Var x) env = lookup env x
PE (SCst x) env = x
PE (SAdd e e₁) env = PE e env + PE e₁ env
PE (SLam {α} e) env = λ Γ↝Γ' → λ y → PE e (cons {α = α} y (liftEnv Γ↝Γ' env))
PE (SApp e e₁) env = PE e env refl (PE e₁ env)
PE (DCst x) env = ECst x
PE (DAdd e e₁) env = EAdd (PE e env) (PE e₁ env)
PE (DLam {σ} e) env = ELam (PE e (consD σ env))
PE (DApp e e₁) env = EApp (PE e env) (PE e₁ env)
PE (↑ l e) env = lift' l (PE e env)

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

-------------------------
--taking care of shifting
--note:
-------------------------
-- data _⇒_↝_ {Γ} {var : Type → Set} : ∀ {Γ'} → Γ ↝ Γ' → env var Γ → env var Γ' → Set₁ where
--   refl : ∀ env → ↝-refl ⇒ env ↝ env
--   extend : ∀ {α Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'} →
--              (v : exp var α) → (Γ↝Γ' ⇒  env ↝ env')  →
--              ↝-extend {Γ = Γ} {Γ' = Γ'} {τ = α} Γ↝Γ' ⇒ env ↝ (cons v env')

-- env↝trans : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
--              {env env' env''} → 
--              Γ↝Γ' ⇒ env ↝ env' → Γ'↝Γ'' ⇒ env' ↝ env'' →
--              let Γ↝Γ'' = ↝-trans Γ↝Γ' Γ'↝Γ'' in
--              Γ↝Γ'' ⇒ env ↝ env''

data env' (Γ' : Ctx) (var : Type → Set) : Ctx → Set₁ where
  []   : env' Γ' var []
  cons : ∀ {Γ} {α : Type} → exp var α → env' Γ' var Γ → env' Γ' var (α ∷ Γ)

------
--note
------

-- data _⊢_↝_ {Γ} : ∀ {Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
--   refl : ∀ env → ↝-refl ⊢ env ↝ env
--   extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'} →
--              (v : EImp τ) → (Γ↝Γ' ⊢  env ↝ env')  →
--              ↝-extend {Γ = Γ} {Γ' = Γ'} {τ = τ} Γ↝Γ' ⊢ env ↝ (v ∷ env')

--   env↝trans : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
--                {env env' env''} → 
--                Γ↝Γ' ⊢ env ↝ env' → Γ'↝Γ'' ⊢ env' ↝ env'' →
--                let Γ↝Γ'' = ↝-trans Γ↝Γ' Γ'↝Γ'' in
--                Γ↝Γ'' ⊢ env ↝ env'' 
-- env↝trans {Γ} {.Γ''} {Γ''} {Γ↝Γ'} {.↝-refl} {env} {.env''} {env''} env↝env' (refl .env'') = env↝env'
-- env↝trans env↝env' (extend v env'↝env'') = extend v (env↝trans env↝env' env'↝env'')
    

------------------------------------
--incoporating shifting within [env]
------------------------------------
data env'' (var : Type → Set) : Ctx → Set₁ where
  []    : env'' var []
  cons  : ∀ {Γ} {α : Type} → exp var α → env'' var Γ → env'' var (α ∷ Γ)
  shift : ∀ {Γ Γ'} {α : Type} → env'' var (α ∷ Γ) → (α ∷ Γ) ↝ Γ' → env'' var Γ'
-----------------------
--some auxiliary lemmas
-----------------------
lookuprenv : ∀ {a : Type} {Γ} {var : Type → Set} → a ∈ Γ → env var Γ → var a
lookuprenv hd (cons x env) = x
lookuprenv (tl id) (cons x env) = lookuprenv id env


-- liftenv' : ∀ {Γ Γ' Γ''} {var : Type → Set}  → Γ' ↝ Γ'' → env' Γ' var Γ → env' Γ'' var Γ 
-- liftenv' Γ'↝Γ'' [] = []
-- liftenv' Γ'↝Γ'' (cons x env) = cons x (liftenv' Γ'↝Γ'' env)

-- lookuprenv' : ∀ {a : Type} {Γ} {Γ'} {var : Type → Set} → a ∈ Γ → env' Γ' var Γ → exp var a 
-- lookuprenv' hd (cons x env) = x
-- lookuprenv' (tl id) (cons x env) = lookuprenv' id env


-- lookuprenv'' : ∀ {a : Type} {Γ} {var : Type → Set} → a ∈ Γ → env'' var Γ → exp var a
-- lookuprenv'' hd (cons x env) = x
-- lookuprenv'' hd (shift (cons x env) x₁) = {!!}
-- lookuprenv'' hd (shift (shift env x) x₁) = {!!}
-- lookuprenv'' (tl id) env = {!!} 
-- -----------------------------------------------
-------------------------
--translating from residual expression in [De Bruijn] to that in [PHOAS]
------------------------------------------------------------------------
-- Exp2exp : ∀ {Γ a} {var : Type → Set} → Exp Γ a → env var Γ → exp var a
-- Exp2exp (EVar x) env = EVar (lookuprenv x env)
-- Exp2exp (EInt x) env = ECst x
-- Exp2exp (EAdd e e₁) env = EAdd (Exp2exp e env) (Exp2exp e₁ env)
-- Exp2exp (ELam e) env = ELam (λ v → Exp2exp e (cons v env))
-- Exp2exp (EApp e e₁) env = EApp (Exp2exp e env) (Exp2exp e₁ env)

-- Exp2exp' : ∀ {Γ Γ' a} {var : Type → Set} → Exp Γ a → env' Γ' var Γ → exp var a
-- Exp2exp' (EVar x) env = lookuprenv' x env
-- Exp2exp' (EInt x) env = ECst x
-- Exp2exp' (EAdd e e₁) env = EAdd (Exp2exp' e env) (Exp2exp' e₁ env)
-- Exp2exp' (ELam e) env = ELam (λ v → Exp2exp' e (cons (EVar v) env))
-- Exp2exp' (EApp e e₁) env = EApp (Exp2exp' e env) (Exp2exp' e₁ env)
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

---------------------------------------------------------
--similarity relation between [Imp Γ A] and [ATInt var A]
---------------------------------------------------------
-- liftenv : ∀ {Γ Γ'} {var : Type → Set}  → Γ ↝ Γ' → env var Γ → env var Γ' 
-- liftenv Γ↝Γ' [] = {!!}
-- liftenv Γ↝Γ' (cons x env) = {!!} 

-----------------------------------------------
--redefining equality
--note that the equality defined in the library
--requires that type [A] is a member of [Set₁]
--while in [similar] [A] a member of [Set]
-----------------------------------------------
-- data _≡_ {A : Set} (x : A) : A → Set₁ where
--   refl : x ≡ x

-- cong₂ : ∀ {A : Set} {B : Set} {C : Set}
--         (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
-- cong₂ f refl refl = refl

 

-- similar : ∀ {A Γ} {var : Type → Set} → Imp Γ A → ATInt var A → env var Γ → Set₁
-- similar {AInt} e e' env = e ≡ e'
-- similar {AFun A A₁} {Γ} {var} e e' env = ∀ {Γ' : Ctx} {v : Imp Γ' A} {v' : ATInt var A} {env'} → 
--                                        (et : Γ ↝ Γ') → (et ⇒ env ↝ env') → similar v v' env' → similar (e et v) (e' v') env'
-- similar {D x} {Γ} {var} e e' env = Exp2exp e env ≡ e' 

-- Similar : ∀ {A Γ Γ'} {var : Type → Set} → Imp Γ A → ATInt var A → env' Γ' var Γ → Set
-- Similar {AInt} e e' env = e ≡ e'
-- Similar {AFun A A₁} {Γ} {Γ'} {var} e e' env = {Γ'' : Ctx} {v : Imp Γ'' A} {v' : ATInt var A} →
--                                                 (et : Γ ↝ Γ'') → Similar {A} {Γ''} {Γ} {var} v v' {!!} → Similar (e et v) (e' v') {!!}
-- Similar {D x} {Γ} {Γ'} {var} e e' env = Exp2exp' e env ≡ e' 
------------------------------------------------------------
--defining the relation between [env : AEnv] to [env' : Env]
--a [similar] relation should be defined between [AEnv] and [Env]
------------------------------------------------------------
-- data similar-env {Γ : Ctx} {var : Type → Set} : ∀ {Δ : ACtx} → AEnv Γ Δ → Env var Δ → Set₁ where
--  []    : similar-env [] [] 
--  scons  : ∀ {A : AType} {Δ : ACtx} {e : Imp Γ A} {e' : ATInt var A} {aen : AEnv Γ Δ} {en : Env var Δ} {env : env var Γ}
--           → similar e e' env → similar-env aen en → similar-env (cons e aen) (cons e' en)

-- lift-similar-env : ∀ {Γ Γ' Δ var} {aen : AEnv Γ Δ} {en : Env var Δ} {et : Γ ↝ Γ'} → similar-env aen en → similar-env (liftEnv et aen) en 
-- lift-similar-env sim = {!!} 

-----------------------------
--now putting things together
-----------------------------
--------------------------------------------------------------
--dummy [env]
--generating any [env] and being used when [env] is irrelevant 
--------------------------------------------------------------
-- dum-type : ∀ {a var} → exp var a
-- dum-type {Int} {var} = ECst 0
-- dum-type {Fun a a₁} = ELam (λ v → dum-type {a₁})
 
-- dum-env : ∀ {Γ var} → env var Γ 
-- dum-env {[]} {var} = []
-- dum-env {Int ∷ Γ} = cons (ECst 0) (dum-env {Γ})
-- dum-env {Fun x x₁ ∷ Γ} = cons (ELam (λ v → dum-type {x₁})) (dum-env {Γ})

-- proj-correct : ∀ {Γ Δ A var} {e : AExp Δ A} {aen : AEnv Γ Δ} {en : Env var Δ} →
--                similar-env aen en → 
--                let e' = proj e en in
--                Σ (env var Γ) (λ env → similar (PE e aen) (pe e') env) 
-- proj-correct {Γ} {[]} {A} {var} {Var ()} {[]} {[]} sim
-- proj-correct {Γ} {α ∷ Δ} {.α} {var} {Var hd} {cons x₁ aen} {cons x₂ en} (scons {env = env} x sim) = env , x
-- proj-correct {Γ} {α ∷ Δ} {A} {var} {Var (tl x)} {cons x₁ aen} {cons x₂ en} (scons x₃ sim) 
--      = proj-correct {Γ} {Δ} {A} {var} {Var x} {aen} {en} sim
-- proj-correct {Γ} {Δ} {AInt} {var} {AInt x} sim = dum-env {Γ} , refl
-- proj-correct {Γ} {Δ} {AInt} {var} {AAdd e e₁} {aen} {en} sim 
--     = dum-env {Γ} ,  this
--         where this : (PE e aen + PE e₁ aen) ≡ (pe (proj e en) + pe (proj e₁ en))
--               this  = {!!} --problem with equality
-- proj-correct {Γ} {Δ} {(AFun α₁ α₂)} {var} {ALam e} {aen} {en} sim = {!!} , 
--   {!λ Γ' → (
--    λ v → (
--    λ v' → (
--    λ env''' → (
--    λ et → (
--    λ exe → (
--    λ simv → (
--    record 
--    (proj-correct {Γ'} {α₁ ∷ Δ} {α₂} {var}  {e}
--    (scons {Γ'} {var} {α₁} {Δ} {v} {v'} {liftEnv {Γ} {Γ'} {Δ} et aen} {en} {env'''} simv (lift-similar-env {Γ} {Γ'} {Δ} {var} {aen} {en} {et} sim)))
--    {
--    proj₁ = env''' 
--    } 

-- )  
-- )
-- )
-- )
-- )
-- )
-- )!} 
-- proj-correct {Γ} {Δ} {A} {var} {AApp e e₁} {aen} {en} sim = proj₁ (proj-correct sim) ,
--  --{!proj₂ (proj-correct {Γ} {Δ} {var = var} {e = e₁} {aen = aen} {en = en} sim)  !}
--  {!(proj₂ (proj-correct {Γ} {Δ} {var = var} {e = e} {aen = aen} {en = en} sim)) 
--   {Γ} {PE e₁ aen} {pe (proj e₁ en)} {proj₁ (proj-correct sim)} {↝-refl} {}  !}
-- proj-correct {Γ} {Δ} {(D Int)} {var} {DInt x} sim = (dum-env {Γ}) , refl
-- proj-correct {Γ} {Δ} {(D Int)} {var} {DAdd e e₁} sim = (dum-env {Γ}) , {!!}
-- proj-correct {Γ} {Δ} {(D (Fun τ₁ τ₂))} {var} {DLam e} sim = dum-env {Γ} , {!!}
-- proj-correct {Γ} {Δ} {(D τ₁)} {var} {DApp e e₁} sim = dum-env {Γ} , {!!} 

 
-- liftenv : ∀ {Γ Γ'} {var : Type → Set}  → Γ ↝ Γ' → env var Γ → env var Γ' 
-- liftenv Γ↝Γ' [] = {!!}
-- liftenv Γ↝Γ' (cons x env) = {!!} 

-- mutual 
--   projp1 : ∀ {Γ A} {var : Type → Set}  → ATInt var A → env var Γ → Imp Γ A
--   projp1 {Γ} {AInt} e env = e
--   projp1 {Γ} {AFun A A₁} e env = λ {Γ'} →
--                                      λ Γ↝Γ' →
--                                        λ v →
--                                          projp1 {Γ'} (e (projp2 {Γ'} v (liftenv {Γ' = Γ'} Γ↝Γ' env)))
--                                          (liftenv {Γ' = Γ'} Γ↝Γ' env)
--   projp1 {Γ} {D x} e env = {!!}

--   projp2 : ∀ {Γ A} {var : Type → Set}  → Imp Γ A →  env var Γ → ATInt var A
--   projp2 {Γ} {AInt} e env = e
--   projp2 {Γ} {AFun A A₁} e env = λ v → projp2 (e {Γ} ↝-refl (projp1 v env)) env
  -- projp2 {Γ} {D x} e env = Exp2exp e env  

---------------
--[similar-exp]
---------------
-- data similar-exp {var₁ var₂} (Γ : List (Σ Type (λ ty → (var₁ ty × var₂ ty))))
--      : ∀ {A} → exp var₁ A → exp var₂ A → Set where
--   similar-EVar : ∀ {A x₁ x₂} → (A , x₁ , x₂) ∈ Γ → similar-exp Γ (EVar x₁) (EVar x₂)
--   similar-ECst : ∀ {n} → similar-exp Γ (ECst n) (ECst n)
--   similar-EAdd : ∀ {a₁ a₂ b₁ b₂} → similar-exp Γ a₁ b₁ → similar-exp Γ a₂ b₂ → similar-exp Γ (EAdd a₁ a₂) (EAdd b₁ b₂)
--   similar-ELam : ∀ {A B} {f₁ : var₁ A → exp var₁ B} {f₂ : var₂ A → exp var₂ B} {v₁ : var₁ A} {v₂ : var₂ A} →
--                    similar-exp ((A , v₁ , v₂) ∷ Γ) (f₁ v₁) (f₂ v₂) → similar-exp Γ (ELam f₁) (ELam f₂)
--   similar-EApp : ∀ {A B} {f₁ : exp var₁ (Fun A B)} {f₂ : exp var₂ (Fun A B)} {a₁ : exp var₁ A} {a₂ : exp var₂ A} →
--                    similar-exp Γ f₁ f₂ → similar-exp Γ a₁ a₂ → similar-exp Γ (EApp f₁ a₁) (EApp f₂ a₂)


-- getΓ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} → List (Σ Type (λ ty → (var₁ ty × var₂ ty))) → Ctx
-- getΓ [] = []
-- getΓ ((proj₁ , proj₂ , proj₃) ∷ Γ) = proj₁ ∷ getΓ Γ

-- getenv1 : ∀ {var₁ : Type → Set} {var₂ : Type → Set} → (SC : List (Σ Type (λ ty → (var₁ ty × var₂ ty)))) → env var₁ (getΓ SC)
-- getenv1 [] = []
-- getenv1 ((proj₁ , proj₂ , proj₃) ∷ Γ) = cons proj₂ (getenv1 Γ) 


data similar-ℕ {A : AType} : ℕ → ℕ → Set₁ where
  ≡-ℕ : ∀ {n n'} → A ≡ SNum → n ≡ n' → similar-ℕ n n'

similar-ℕ-≡ : ∀ {A n n'} → similar-ℕ {A} n n' → n ≡ n'
similar-ℕ-≡ (≡-ℕ x x₁) = x₁

data similar-exp {var₁ var₂} {Γ} (env₁ : env var₁ Γ) (env₂ : env var₂ Γ)
     : ∀ {A} → exp var₁ A → exp var₂ A → Set₁ where
  similar-EVar : ∀ {A} → (id : A ∈ Γ) → similar-exp env₁ env₂ (EVar (lookuprenv id env₁)) (EVar (lookuprenv id env₂))
  similar-ECst : ∀ {n} → similar-exp env₁ env₂ (ECst n) (ECst n)
  similar-EAdd : ∀ {a₁ a₂ b₁ b₂} → similar-exp env₁ env₂ a₁ b₁ → similar-exp env₁ env₂ a₂ b₂ 
                   → similar-exp env₁ env₂ (EAdd a₁ a₂) (EAdd b₁ b₂)
  similar-ELam : ∀ {A B} {f₁ : var₁ A → exp var₁ B} {f₂ : var₂ A → exp var₂ B} {v₁ : var₁ A} {v₂ : var₂ A} →
                   similar-exp (cons v₁ env₁) (cons v₂ env₂) (f₁ v₁) (f₂ v₂) → similar-exp env₁ env₂ (ELam f₁) (ELam f₂)
  similar-EApp : ∀ {A B} {f₁ : exp var₁ (Fun A B)} {f₂ : exp var₂ (Fun A B)} {a₁ : exp var₁ A} {a₂ : exp var₂ A} →
                   similar-exp env₁ env₂ f₁ f₂ → similar-exp env₁ env₂ a₁ a₂ → similar-exp env₁ env₂ (EApp f₁ a₁) (EApp f₂ a₂)


----------------------
--semantic equivalence
----------------------
equiv : ∀ {a} → EImp a → TInt a → Set
equiv {Num} u v = u ≡ v
equiv {Fun a a₁} u v = {ua : EImp a} {va : TInt a} → equiv ua va → equiv (u ua) (v va)

data equiv-env : ∀ {Γ} → env EImp Γ → env TInt Γ → Set₁ where
  []   : equiv-env [] []
  cons : ∀ {Γ a v₁ v₂} {en₁ : env EImp Γ} {en₂ : env TInt Γ} →
         equiv {a} v₁ v₂ →
         equiv-env en₁ en₂ →
         equiv-env {a ∷ Γ} (cons v₁ en₁) (cons v₂ en₂)

-- ----------------------------------------------------
-- --similarity relation between the evaluation results
-- ----------------------------------------------------
-- data _⇒_↝_ {Γ} {var} : ∀ {Γ'} → Γ ↝ Γ' → env var Γ → env var Γ' → Set₁ where
--   refl : ∀ env → refl ⇒ env ↝ env
--   extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'} →
--              (v : var τ) → (Γ↝Γ' ⇒  env ↝ env')  →
--              extend {Γ = Γ} {Γ' = Γ'} {τ = τ} Γ↝Γ' ⇒ env ↝ (cons v env')



-- env↝trans : ∀ {var : Type → Set} {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
--                {en : env var Γ} {en' : env var Γ'} {en'' : env var Γ''} → 
--                Γ↝Γ' ⇒ en ↝ en' → Γ'↝Γ'' ⇒ en' ↝ en'' →
--                let Γ↝Γ'' = lem-↝-trans Γ↝Γ' Γ'↝Γ'' in
--                Γ↝Γ'' ⇒ en ↝ en'' 
-- env↝trans {var} {Γ} {.Γ''} {Γ''} {Γ↝Γ'} {.refl} {en} {.en''} {en''} Γ↝Γ'⇒en↝en' (refl .en'') = Γ↝Γ'⇒en↝en'
-- env↝trans Γ↝Γ'⇒en↝en' (extend v Γ'↝Γ''⇒en'↝en'') = extend v (env↝trans Γ↝Γ'⇒en↝en' Γ'↝Γ''⇒en'↝en'') 



-- similar : ∀ {A Γ var₁ var₂} → (en₁ : env var₁ Γ) → (en₂ : env var₂ Γ) → Imp Γ A → ATInt var₂ A → Set₁
-- similar {AInt} en₁ en₂ e e' = similar-ℕ {AInt} e e'
-- similar {AFun A A₁} {Γ} {var₁} {var₂} en₁ en₂ e e' = ∀ {Γ'} {v : Imp Γ' A} {v' : ATInt var₂  A} {en₁' : env var₁ Γ'} {en₂' : env var₂ Γ'} → 
--                                        (et : Γ ↝ Γ') → (et ⇒ en₁ ↝ en₁') → (et ⇒ en₂ ↝ en₂') 
--                                         → similar en₁' en₂' v v'  → similar en₁' en₂' (e et v) (e' v')
-- similar {D x} en₁ en₂ e e' = similar-exp en₁ en₂ (Exp2exp e en₁) e' 


-- data similar-env {Γ var₁ var₂} {en₁ : env var₁ Γ} {en₂ : env var₂ Γ} : ∀ {Δ : ACtx} → AEnv Γ Δ → Env var₂ Δ → Set₁ where
--  []    : similar-env [] [] 
--  scons  : ∀ {A : AType} {Δ : ACtx} {e : Imp Γ A} {e' : ATInt var₂ A} {aen : AEnv Γ Δ} {en : Env var₂ Δ} --{en₁ : env var₁ Γ} {en₂ : env var₂ Γ} 
--           → similar en₁ en₂ e e'  → similar-env {Γ} {var₁} {var₂} {en₁} {en₂} {Δ} aen en → similar-env (cons e aen) (cons e' en)
                   

-- lift-similar : ∀ {A Γ Γ' var₁ var₂} {et : Γ ↝ Γ'} {e : Imp Γ A} {e' : ATInt var₂ A} →  
--                  {en₁ : env var₁ Γ} {en₁' : env var₁ Γ'} {en₂ : env var₂ Γ} {en₂' : env var₂ Γ'} →
--                   et ⇒ en₁ ↝ en₁' → 
--                   et ⇒ en₂ ↝ en₂' →
--                  similar {A} {Γ} {var₁} {var₂} en₁ en₂ e e' → 
--                  similar {A} {Γ'} {var₁} {var₂} en₁' en₂' (lift A et e) e'
-- lift-similar {AInt} et⇒en₁↝en₁' et⇒en₂↝en₂' sim = sim
-- lift-similar {AFun A A₁} {Γ} {Γ'} {var₁} {var₂} {et} {e} {e'} {en₁} {en₁'} {en₂} {en₂'} et⇒en₁↝en₁' et⇒en₂↝en₂' sim 
--      = λ {Γ''} {v} {v'} {en₁''} {en₂''} et₁ et₁⇒en₁'↝en₁'' et₁⇒en₂'↝en₂''
--            simvv' →
--            sim {Γ''} {v} {v'} {en₁''} {en₂''} (↝-trans et et₁)
--            (env↝trans et⇒en₁↝en₁' et₁⇒en₁'↝en₁'')
--            (env↝trans et⇒en₂↝en₂' et₁⇒en₂'↝en₂'') simvv'
-- lift-similar {D x} {Γ} {Γ'} {var₁} {var₂} {et} {e} {e'} {en₁} {en₁'} {en₂} {en₂'} et⇒en₁↝en₁' et⇒en₂↝en₂' sim = {!!}

-- lift-similar-env : ∀ {Γ Γ' Δ var₁ var₂} {et : Γ ↝ Γ'} {aen : AEnv Γ Δ} {en : Env var₂ Δ}
--                      {en₁ : env var₁ Γ} {en₁' : env var₁ Γ'} {en₂ : env var₂ Γ} {en₂' : env var₂ Γ'} →
--                     et ⇒ en₁ ↝ en₁' → 
--                     et ⇒ en₂ ↝ en₂' → 
--                     similar-env {Γ} {var₁} {var₂} {en₁} {en₂} {Δ} aen en → 
--                     similar-env {Γ'} {var₁} {var₂} {en₁'} {en₂'} {Δ} (liftEnv et aen) en 
-- lift-similar-env et⇒en₁↝en₁' et⇒en₂↝en₂' [] = []
-- lift-similar-env {Γ} {Γ'} {A ∷ Δ} {var₁} {var₂} {et} {cons e aen} {cons e' en} {en₁} {en₁'} {en₂} {en₂'} et⇒en₁↝en₁' et⇒en₂↝en₂' (scons x sim) 
--    = scons (lift-similar et⇒en₁↝en₁' et⇒en₂↝en₂' x)
--        (lift-similar-env et⇒en₁↝en₁' et⇒en₂↝en₂' sim)
----------------------
--prove [proj] correct
----------------------
-- proj-correct : ∀ {Γ Δ A var₁ var₂} {e : AExp Δ A} {aen : AEnv Γ Δ} {en : Env var₂ Δ} {en₁ : env var₁ Γ} {en₂ : env var₂ Γ} →
--                similar-env {Γ} {var₁} {var₂} {en₁} {en₂} {Δ} aen en → 
--                let e' = proj e en in
--                similar en₁ en₂ (PE e aen) (pe e') 
-- proj-correct {Γ} {[]} {AInt} {var₁} {var₂} {Var ()} []
-- proj-correct {Γ} {.AInt ∷ Δ} {AInt} {var₁} {var₂} {Var hd} (scons x₁ sim) = x₁
-- proj-correct {Γ} {A ∷ Δ} {AInt} {var₁} {var₂} {Var (tl x)} {cons e aen} {cons e' en} (scons {.A} {.Δ} {.e} {.e'} {.aen} {.en} x₁ sim) 
--    = proj-correct {Γ} {Δ} {AInt} {var₁} {var₂} {Var x} {aen} {en} 
--        sim
-- proj-correct {Γ} {Δ} {AInt} {var₁} {var₂} {AInt x} sim = ≡-ℕ refl refl
-- proj-correct {Γ} {Δ} {AInt} {var₁} {var₂} {AAdd e e₁} {aen} {en} {en₁} {en₂} sim 
--       rewrite similar-ℕ-≡ (proj-correct {Γ} {Δ} {AInt} {var₁} {var₂} {e} {aen} {en} {en₁} {en₂}  sim) | 
--               similar-ℕ-≡ (proj-correct {Γ} {Δ} {AInt} {var₁} {var₂} {e₁} {aen} {en} {en₁} {en₂} sim)
--       = ≡-ℕ refl refl
-- proj-correct {Γ} {Δ} {AInt} {var₁} {var₂} {AApp e e₁} {aen} {en} {en₁} {en₂} sim = ≡-ℕ refl 
--     --Note,
--     --proj-correct {Γ} {Δ} {var₁ = var₁} {var₂ = var₂} {e = e₁} {aen = aen} {en = en} {en₁ = en₁} {en₂ = en₂} sim
--     --: similar en₁ en₂ (PE e₁ aen) (pe (proj e₁ en))
--      (similar-ℕ-≡
--         (proj-correct {Γ} {Δ} {var₁ = var₁} {var₂ = var₂} {e = e}
--          {aen = aen} {en = en} {en₁ = en₁} {en₂ = en₂} sim {Γ} {PE e₁ aen}
--          {pe (proj e₁ en)} {en₁} {en₂} ↝-refl (refl en₁) (refl en₂)
--          (proj-correct {Γ} {Δ} {var₁ = var₁} {var₂ = var₂} {e = e₁}
--           {aen = aen} {en = en} {en₁ = en₁} {en₂ = en₂} sim)))
-- --proj-correct {Γ} {Δ} {AFun A A₁} {var₁} {var₂} {e} {aen} {en} {en₁} {en₂} sim = 
--   --{!similar {AFun A A₁} {Γ} {var₁} {var₂} en₁ en₂ (PE e aen) (pe (proj e en)) !}
--     -- {!λ {Γ'}          →
--     --  λ {v}           →
--     --  λ {v'}          →
--     --  λ {en₁'}        →
--     --  λ {en₂'}        →
--     --  λ et            →
--     --  λ et⇒en₁↝en₁'   →
--     --  λ et⇒en₂↝en₂'   →
--     --  λ simvv'        →
--     --   --similar {AFun A A₁} {Γ} {var₁} {var₂} en₁ en₂ (PE e aen) (pe (proj e en)))
--     --   {Γ'} {v} {v'} {en₁'} {en₂'}
--     --   et et⇒en₁↝en₁' et⇒en₂↝en₂' simvv'
--     --  !}
-- proj-correct {Γ} {[]} {AFun A A₁} {var₁} {var₂} {Var ()} []
-- proj-correct {Γ} {.(AFun A A₁) ∷ Δ} {AFun A A₁} {var₁} {var₂} {Var hd} {cons e aen} {cons e' en} {en₁} {en₂} 
--      (scons {.(AFun A A₁)} {.Δ} {.e} {.e'} {.aen} {.en}  x₁ sim) = x₁
-- proj-correct {Γ} {A₂ ∷ Δ} {AFun A A₁} {var₁} {var₂} {Var (tl x)} {cons e aen} {cons e' en} (scons {.A₂} {.Δ} {.e} {.e'} {.aen} {.en} x₁ sim) = 
--      proj-correct {Γ} {Δ} {AFun A A₁} {var₁} {var₂} {Var x} sim
-- proj-correct {Γ} {Δ} {AFun A A₁} {var₁} {var₂} {ALam e} {aen} {en} {en₁} {en₂} sim = 
--      {!λ {Γ'} {v} {v'} {en₁'} {en₂'} et et⇒en₁↝en₁' et⇒en₂↝en₂' simvv' →
--       (liftEnv {Γ} {Γ'} {Δ} et aen) 
--      !}
-- proj-correct {Γ} {Δ} {AFun A A₁} {var₁} {var₂} {AApp e e₁} sim = {!!}
-- proj-correct {Γ} {Δ} {D x} sim = {!!} 

---------------------------------------------------------
--note 
--a respecification of [similar-exp] and [similar]
---------------------------------------------------------
----------------------------------------------
--put [Similar-Exp] in [Set] instead of [Set₁]
----------------------------------------------

-- data Similar-Exp {var₁ var₂} (Γ : List (Σ[ A ∈ Type ] (var₁ A × var₂ A)))
--      : ∀ {A} → exp var₁ A → exp var₂ A → Set where
--   Similar-EVar : ∀ {A x₁ x₂} → (A , x₁ , x₂) ∈ Γ → Similar-Exp Γ (EVar x₁) (EVar x₂)
--   Similar-ECst : ∀ {n} → Similar-Exp Γ (ECst n) (ECst n)
--   Similar-EAdd : ∀ {a₁ a₂ b₁ b₂} → Similar-Exp Γ a₁ b₁ → Similar-Exp Γ a₂ b₂ → Similar-Exp Γ (EAdd a₁ a₂) (EAdd b₁ b₂)
--   Similar-ELam : ∀ {A B} {f₁ : var₁ A → exp var₁ B} {f₂ : var₂ A → exp var₂ B} {v₁ : var₁ A} {v₂ : var₂ A} →
--                   Similar-Exp ((A , v₁ , v₂) ∷ Γ) (f₁ v₁) (f₂ v₂) →
--                   Similar-Exp Γ (ELam f₁) (ELam f₂)
--   Similar-EApp : ∀ {A B} {f₁ : exp var₁ (Fun A B)} {f₂ : exp var₂ (Fun A B)} {a₁ : exp var₁ A} {a₂ : exp var₂ A} →
--                   Similar-Exp Γ f₁ f₂ → Similar-Exp Γ a₁ a₂ →
--                   Similar-Exp Γ (EApp f₁ a₁) (EApp f₂ a₂)

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

-- data Similar-Exp {var₁ var₂} (Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A))))
--      : ∀ {A} → exp var₁ A → exp var₂ A → Set where
--   similar-EVar  : ∀ {A x₁ x₂ Γ'} → (Γ2Ctx Γ) ↝ (Γ2Ctx Γ') → (A , x₁ , x₂) ∈ Γ' → Similar-Exp Γ' (EVar x₁) (EVar x₂)
--   similar-ECst  : ∀ {n Γ'} → (Γ2Ctx Γ) ↝ (Γ2Ctx Γ') → Similar-Exp Γ' (ECst n) (ECst n)
--   similar-EAdd  : ∀ {a₁ a₂ b₁ b₂ Γ'} → (Γ2Ctx Γ) ↝ (Γ2Ctx Γ') → Similar-Exp Γ' a₁ b₁ → Similar-Exp Γ' a₂ b₂ 
--                     → Similar-Exp Γ' (EAdd a₁ a₂) (EAdd b₁ b₂)
--   similar-ELam  : ∀ {A B Γ'} {f₁ : var₁ A → exp var₁ B} {f₂ : var₂ A → exp var₂ B} {v₁ : var₁ A} {v₂ : var₂ A} →
--                     (Γ2Ctx Γ) ↝ (Γ2Ctx Γ') →
--                   Similar-Exp ((A , v₁ , v₂) ∷ Γ') (f₁ v₁) (f₂ v₂) →
--                   Similar-Exp Γ' (ELam f₁) (ELam f₂)
--   similar-EApp  : ∀ {A B Γ'} {f₁ : exp var₁ (Fun A B)} {f₂ : exp var₂ (Fun A B)} {a₁ : exp var₁ A} {a₂ : exp var₂ A} →
--                   (Γ2Ctx Γ) ↝ (Γ2Ctx Γ') →
--                   Similar-Exp Γ' f₁ f₂ → Similar-Exp Γ' a₁ a₂ →
--                   Similar-Exp Γ' (EApp f₁ a₁) (EApp f₂ a₂)

Γ2Ctx≡ : ∀ {var₁ var₂} {Γ :  List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} → en₁2Ctx (Γ2en₁ {var₁} {var₂} Γ) ≡ Γ2Ctx Γ
Γ2Ctx≡ {var₁} {var₂} {[]} = refl
Γ2Ctx≡ {var₁} {var₂} {x ∷ Γ} rewrite Γ2Ctx≡ {Γ = Γ} = refl 

data _⊂_ {A : Set} : List A → List A → Set where
  extend-hd  : ∀ {Γ Γ'} → Γ ↝ Γ' → Γ ⊂ Γ'
  extend-mid : ∀ {Γ Γ' τ} → Γ ⊂ Γ' → (τ ∷ Γ) ⊂ (τ ∷ Γ')

-- ⊂-trans : ∀ {A} {Γ : List A} {Γ' : List A} {Γ'' : List A} → Γ ⊂ Γ' → Γ' ⊂ Γ'' → Γ ⊂ Γ''
-- ⊂-trans Γ⊂Γ' Γ'⊂Γ'' = ?

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
         this rewrite etG2S≡ {var₁} {var₂} {Γ} {Γ'} {et}
              = refl



etG2S-trans≡ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
                {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                {Γ'' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                {et : Γ ↝ Γ'} {et₁ : Γ' ↝ Γ''} →
                lem-↝-trans (etG2S et) (etG2S et₁) ≡ etG2S (lem-↝-trans et et₁)
etG2S-trans≡ {var₁} {var₂} {Γ} {.Γ''} {Γ''} {et} {refl} = refl
etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {(τ ∷ Γ'')} {et} {extend et₁} = cong extend this
       where this : (lem-↝-trans (etG2S et) (etG2S et₁)) ≡ (etG2S (lem-↝-trans et et₁))
             this 
              rewrite etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {Γ''} {et} {et₁} 
                  = refl     

Similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set}  → (Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))) → Imp (en₁2Ctx (Γ2en₁ Γ)) A → 
            ATInt var₂ A → Set
Similar {SNum} Γ e e' = e ≡ e'
Similar {SFun A A₁} {var₁} {var₂} Γ e e' = {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {v : Imp (en₁2Ctx (Γ2en₁ {var₁} {var₂} Γ')) A} 
                                           {v' : ATInt var₂ A} →
                                           (et : Γ ↝ Γ') →
                                           Similar Γ' v v' → Similar Γ' (e (etG2S et) v) (e' v')
Similar {D x} Γ e e' = similar-Exp Γ (Exp2exp (Γ2en₁ Γ) e) e'
    

data similar-env {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
     : ∀ {Δ : ACtx} → AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ → Env var₂ Δ → Set₁ where
 []    : similar-env [] [] 
 scons  : ∀ {A : AType} {Δ : ACtx} {e : Imp (en₁2Ctx (Γ2en₁ Γ)) A} {e' : ATInt var₂ A} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} {en : Env var₂ Δ} 
          → Similar Γ e e'  → similar-env {var₁} {var₂} {Γ} {Δ} aen en → similar-env (cons e aen) (cons e' en)

-- lift-lemma1 : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} 
--                  {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
--                  {et : (en₁2Ctx (Γ2en₁ Γ)) ↝ (en₁2Ctx (Γ2en₁ Γ'))} 
--                  {e : Exp (en₁2Ctx (Γ2en₁ Γ)) A} {e' : exp var₂ A} →
--                  similar-Exp Γ (Exp2exp (Γ2en₁ Γ) e) e' → 
--                  similar-Exp Γ' (Exp2exp (Γ2en₁ Γ') (elevate (↝↝-base et) e)) e' 
     
-- lift-lemma1 {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} sim = {!!}
-- data _⊂_ {A : Set} : List A → List A → Set where
--   extend-hd  : ∀ {Γ Γ'} → Γ ↝ Γ' → Γ ⊂ Γ'
--   extend-mid : ∀ {Γ Γ' τ} → Γ ⊂ Γ' → (τ ∷ Γ) ⊂ (τ ∷ Γ')

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


-- lemmaExp2exp≡ : ∀ {τ τ'} {var : Type → Set} {v : var τ}
--                   {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ' : List (Σ[ A ∈ Type ] (var A))}
--                   {et : Γ ↝ Γ'}
--                   {e : Exp (τ ∷ en₁2Ctx Γ) τ'} →
--                   Exp2exp ((τ , v) ∷ Γ) e ≡ Exp2exp ((τ , v) ∷ Γ') (elevate (↝↝-extend (↝↝-base (etG2S' et))) e)
-- lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {Γ'} {et} {EVar x} = {!!}
-- lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {EInt x} = refl
-- lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {EAdd e e₁} 
--         rewrite lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {e} |
--                 lemmaExp2exp≡ {τ} {Int} {var} {v} {Γ} {Γ'} {et} {e₁}
--        = refl
-- lemmaExp2exp≡ {τ} {(Fun τ₁ τ')} {var} {v} {Γ} {Γ'} {et} {ELam e} 
--        = {!λ v₁ → lemmaExp2exp≡ {τ₁} {τ'} {var} {v₁} {(τ , v) ∷ Γ} {} !}
-- lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {Γ'} {et} {EApp e e₁} = {!!}

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
                 {et : Γ ↝ Γ'} {e : Imp (en₁2Ctx (Γ2en₁ Γ)) A} {e' : ATInt var₂ A} →  
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
   --= {!lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x  !}
   --= {!lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim!}
    = scons (lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x) 
            (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim) 
      -- scons (lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x) 
      --       (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim)



-- lift'≡reify : ∀ {α Γ Δ} → (l : liftable α) → (e : AExp Δ α) → (aen : AEnv Γ Δ) 
--                →  lift' l (PE e aen) ≡ PE (reify l e) aen
-- lift'≡reify {AInt} () e aen
-- lift'≡reify {AFun α α₁} l e aen = {!!}
-- lift'≡reify {D x} base e aen = refl




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
proj-correct {Δ} {.(D x)} {var₁} {var₂} {Γ} {↑ {D x} base e} sim = proj-correct {e = reify base e} sim
proj-correct {Δ} {.(D (Fun (typeof α₁) (typeof α₂)))} {var₁} {var₂} {Γ} {↑ {SFun α₁ α₂} (Func l l₁) (Var x)} sim = {!!}
proj-correct {Δ} {.(D (Fun (typeof α₁) (typeof α₂)))} {var₁} {var₂} {Γ} {↑ {SFun α₁ α₂} (Func l l₁) (SLam e)} sim = {!!}
proj-correct {Δ} {.(D (Fun (typeof α₁) (typeof α₂)))} {var₁} {var₂} {Γ} {↑ {SFun α₁ α₂} (Func l l₁) (SApp e e₁)} sim = {!!}
  --= {! proj-correct {e = reify l e} sim !} 

-}