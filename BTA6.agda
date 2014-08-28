--correctness proof of partial evaluation with liftable terms 
module BTA6 where


----------------------------------------------
-- Preliminaries: Imports and List-utilities
----------------------------------------------
open import Data.Nat hiding  (_<_;_⊔_;_*_;equal)
open import Data.Bool hiding (_∧_;_∨_) 
open import Function using (_∘_)
open import Data.List
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import Lib 


data Type : Set where
  Num : Type
  Fun : Type → Type → Type
  Prd : Type  → Type  → Type   
  Sum : Type → Type → Type

Ctx = List Type




data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ Num
  EAdd : Exp Γ Num → Exp Γ Num -> Exp Γ Num
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'
  EPair  : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (Prd τ τ')
  EInl   : ∀ {τ τ'} → Exp Γ τ → Exp Γ (Sum τ τ')
  EInr   : ∀ {τ τ'} → Exp Γ τ' → Exp Γ (Sum τ τ') 
  EFst : ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ
  ESnd : ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ'
  ECase : ∀ {τ τ' τ''} → Exp Γ (Sum τ τ') → Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''



module Exp-Eval where
  -- interpretation of Exp types
  TInt : Type → Set
  TInt Num = ℕ
  TInt (Fun ty ty₁) = TInt ty → TInt ty₁
  TInt (Prd ty ty₁) = TInt ty * TInt ty₁
  TInt (Sum ty ty₁) = TInt ty ⨄ TInt ty₁



  data Env : Ctx → Set where 
    [] : Env []
    _∷_ : ∀ {τ Γ} → TInt τ → Env Γ → Env (τ ∷ Γ)
  

  lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → TInt τ
  lookupE hd (x ∷ env) = x
  lookupE (tl v) (x ∷ env) = lookupE v env


 
  ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
  ev (EVar x) env = lookupE x env
  ev (ECst x) env = x
  ev (EAdd e e₁) env = ev e env + ev e₁ env
  ev (ELam e) env = λ x → ev e (x ∷ env)
  ev (EApp e e₁) env = ev e env (ev e₁ env)
  ev (EPair e e₁) env = ev e env , (ev e₁ env)
  ev (EInl e) env = tl (ev e env)
  ev (EInr e) env = tr (ev e env)
  ev (EFst e) env = fst (ev e env)
  ev (ESnd e) env = snd (ev e env)
  ev (ECase e e₁ e₂) env with ev e env
  ev (ECase e e₁ e₂) env | tl c  = (λ x → ev e₁ (x ∷ env)) c
  ev (ECase e e₁ e₂) env | tr c  = (λ x → ev e₂ (x ∷ env)) c


data AType : Set where
    SNum  : AType
    SFun  : AType → AType → AType
    D     : Type → AType
    SPrd   : AType → AType → AType 
    SSum   : AType → AType → AType 

ACtx = List AType




typeof : AType → Type
typeof SNum = Num
typeof (SFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
typeof (D x) = x
typeof (SPrd α₁ α₂) = Prd (typeof α₁) (typeof α₂)
typeof (SSum α₁ α₂) = Sum (typeof α₁) (typeof α₂)


ATInt : Ctx → AType → Set
ATInt Γ (SNum) = ℕ
ATInt Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (ATInt Γ' α₁ → ATInt Γ' α₂)
ATInt Γ (D σ) = Exp Γ σ
ATInt Γ (SPrd α₁ α₂) = (ATInt Γ α₁) * (ATInt Γ α₂)
ATInt Γ (SSum α₁ α₂) = (ATInt Γ α₁) ⨄ (ATInt Γ α₂)

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
elevate Γ↝Γ'↝Γ'' (EPair e e₁) =  EPair (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (EInl e) = EInl (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EInr e) = EInr (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EFst e) = EFst (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ESnd e) = ESnd (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ECase c e₁ e₂) = ECase (elevate Γ↝Γ'↝Γ'' c) (elevate (extend Γ↝Γ'↝Γ'') e₁) (elevate (extend Γ↝Γ'↝Γ'') e₂)

liftE : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
liftE Γ↝Γ' e = elevate (refl Γ↝Γ') e




-------------------------------------------
--specification of the liftable restriction
-------------------------------------------
mutual 
  data Liftable : AType → Set where
    D : ∀ τ → Liftable (D τ)
    SCst : Liftable SNum
    SSum : ∀ {α₁ α₂} → Liftable α₁ → Liftable α₂ → Liftable (SSum α₁ α₂)
    SPrd : ∀ {α₁ α₂} → Liftable α₁ → Liftable α₂ → Liftable (SPrd α₁ α₂)
    SFun : ∀ {α₁ α₂} → Liftable⁻ α₁ → Liftable α₂ → Liftable (SFun α₁ α₂)

  data Liftable⁻ : AType → Set where
    D : ∀ τ → Liftable⁻ (D τ)
    SPrd : ∀ {α₁ α₂} → Liftable⁻ α₁ → Liftable⁻ α₂ → Liftable⁻ (SPrd α₁ α₂)
    SFun : ∀ {α₁ α₂} → Liftable α₁ → Liftable⁻ α₂ → Liftable⁻ (SFun α₁ α₂)
----------------------------------------
--[AExp] with liftable terms
----------------------------------------    
data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  SCst : ℕ → AExp Δ SNum
  SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
  SLam : ∀ {α₁ α₂}   → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
  SApp : ∀ {α₁ α₂}   → AExp Δ (SFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
  DCst : ℕ → AExp Δ (D Num)
  DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
  DLam : ∀ {σ₁ σ₂}   → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)
  -- Static pairs and sums
  SPair  : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ α₂ → AExp Δ (SPrd α₁ α₂)
  SInl   : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ (SSum α₁ α₂)
  SInr   : ∀ {α₁ α₂} → AExp Δ α₂ → AExp Δ (SSum α₁ α₂)
  SFst  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₁
  SSnd  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₂
  SCase : ∀ {α₁ α₂ α₃} → AExp Δ (SSum α₁ α₂) → AExp (α₁ ∷ Δ) α₃ → AExp (α₂ ∷ Δ) α₃ → AExp Δ α₃
  -- Dynamic pairs and sums
  DPair  : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D σ₂) → AExp Δ (D (Prd σ₁ σ₂))
  DInl   : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D (Sum σ₁ σ₂))
  DInr   : ∀ {σ₁ σ₂} → AExp Δ (D σ₂) → AExp Δ (D (Sum σ₁ σ₂))
  DFst  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₁)
  DSnd  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₂)
  DCase : ∀ {σ₁ σ₂ σ₃} → AExp Δ (D (Sum σ₁ σ₂)) → AExp ((D σ₁) ∷ Δ) (D σ₃) → AExp ((D σ₂) ∷ Δ) (D σ₃) → AExp Δ (D σ₃) 
  -- Liftable static terms
  ↑     : ∀ {α} → Liftable α → AExp Δ α  → AExp Δ (D (typeof α))


lift : ∀ {Γ Γ'} α → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α 
lift SNum p v = v
lift (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (↝-trans Γ↝Γ' Γ'↝Γ'')
lift (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v
lift (SPrd α₁ α₂) Γ↝Γ' (v₁ , v₂) = (lift α₁ Γ↝Γ' v₁) , (lift α₂ Γ↝Γ' v₂)
lift (SSum α₁ α₂) Γ↝Γ' (tl v) = tl (lift α₁ Γ↝Γ' v)
lift (SSum α₁ α₂) Γ↝Γ' (tr v) = tr (lift α₂ Γ↝Γ' v)



module SimpleAEnv where
  -- A little weaker, but much simpler
  data AEnv (Γ : Ctx) : ACtx → Set where
    [] : AEnv Γ []
    cons : ∀ {Δ} {α : AType} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)
  
  lookup : ∀ {α Δ Γ} → AEnv Γ Δ → α ∈ Δ → ATInt Γ α
  lookup [] ()
  lookup {α} (cons x aenv) hd = x
  lookup {α} (cons x aenv) (tl {.α} {y} id) = lookup aenv id
  
  liftEnv : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
  liftEnv Γ↝Γ' [] = []
  liftEnv Γ↝Γ' (cons {α = α} x env) = cons {α = α} (lift α Γ↝Γ' x) (liftEnv Γ↝Γ' env)
  
  consD : ∀ {Γ Δ} σ → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
  consD σ env = (cons {α = D σ} (EVar hd) (liftEnv (extend {τ = σ} refl) env))



----------------------------------------------
-- Helper for the evaluation of liftable terms
----------------------------------------------
  mutual 
    lift' : ∀ {Γ α} → Liftable α → ATInt Γ α → (Exp Γ (typeof α))
    lift' (D τ) v = v
    lift' SCst v = ECst v
    lift' (SSum ty ty₁) (tl a) = EInl (lift' ty a)
    lift' (SSum ty ty₁) (tr b) = EInr (lift' ty₁ b)
    lift' (SPrd ty ty₁) (ffst , ssnd) = EPair (lift' ty ffst) (lift' ty₁ ssnd)
    lift' {Γ} (SFun {α₁} ty₁ ty₂) v = ELam
                                        ((λ x → lift' ty₂ (v (extend {τ = typeof α₁} refl) x))
                                         (embed ty₁ (EVar {Γ = typeof α₁ ∷ Γ} hd)))

    embed : ∀ {Γ α} → Liftable⁻ α → Exp Γ (typeof α) → (ATInt Γ α)
    embed (D τ) e = e
    embed (SPrd ty ty₁) e = embed ty (EFst e) , embed ty₁ (ESnd e)
    embed {Γ} (SFun {α} ty₁ ty₂) e = 
      λ Γ↝Γ' v₁ → embed ty₂ (EApp (liftE Γ↝Γ' e) (lift' ty₁ v₁))

--------------------
-- Partial Evaluator
--------------------
  pe : ∀ {α Δ Γ} → AExp Δ α → AEnv Γ Δ → ATInt Γ α
  pe (Var x) env = lookup env x
  pe (SCst x) env = x
  pe (SAdd e e₁) env = pe e env + pe e₁ env
  pe (SLam {α} e) env = λ Γ↝Γ' → λ y → pe e (cons {α = α} y (liftEnv Γ↝Γ' env))
  pe (SApp e e₁) env = pe e env refl (pe e₁ env)
  pe (DCst x) env = ECst x
  pe (DAdd e e₁) env = EAdd (pe e env) (pe e₁ env)
  pe (DLam {σ} e) env = ELam (pe e (consD σ env))
  pe (DApp e e₁) env = EApp (pe e env) (pe e₁ env)
  pe {Γ = Γ} (SPair e e₁) env = pe {Γ = Γ} e env , pe {Γ = Γ} e₁ env
  pe {α = SSum α₁ α₂} {Γ = Γ} (SInl e) env = tl (pe {α = α₁} {Γ = Γ} e env)
  pe {α = SSum α₁ α₂} {Γ = Γ} (SInr e) env = tr (pe {α = α₂} {Γ = Γ} e env)
  pe {Γ = Γ} (SFst e) env = fst (pe {Γ = Γ} e env)
  pe {Γ = Γ} (SSnd e) env = snd (pe {Γ = Γ} e env)
  pe {Γ = Γ} (SCase e e₁ e₂) env with pe {Γ = Γ} e env
  pe {Γ = Γ} (SCase {α₁ = α} e e₁ e₂) env | tl y = (λ Γ↝Γ' → λ y → pe e₁ (cons {α = α} y (liftEnv Γ↝Γ' env))) refl y
  pe {Γ = Γ} (SCase {α₂ = α} e e₁ e₂) env | tr y = (λ Γ↝Γ' → λ y → pe e₂ (cons {α = α} y (liftEnv Γ↝Γ' env))) refl y
  pe (DPair e e₁) env = EPair (pe e env) (pe e₁ env)
  pe (DInl e) env = EInl (pe e env)
  pe (DInr e) env = EInr (pe e env)
  pe (DFst e) env = EFst (pe e env)
  pe (DSnd e) env = ESnd (pe e env)
  pe (DCase {σ₁} {σ₂} e e₁ e₂) env = ECase (pe e env) (pe e₁ (consD σ₁ env)) (pe e₂ (consD σ₂ env))
  pe (↑ x e) env = lift' x (pe e env) 



  

-- Correctness proof

module Correctness where
  open SimpleAEnv
  open Exp-Eval

 
  stripα = typeof

  stripΔ : ACtx → Ctx
  stripΔ = map stripα

  strip-lookup : ∀ { α Δ} → α ∈ Δ → stripα α ∈ stripΔ Δ
  strip-lookup hd = hd
  strip-lookup (tl x) = tl (strip-lookup x)



  strip : ∀ {α Δ} → AExp Δ α → Exp (stripΔ Δ) (stripα α)
  strip (Var x) = EVar (strip-lookup x)
  strip (SCst x) = ECst x
  strip (SAdd e e₁) = EAdd (strip e) (strip e₁)
  strip (SLam e) = ELam (strip e)
  strip (SApp e e₁)  = EApp (strip e) (strip e₁)
  strip (DCst x)  = ECst x
  strip (DAdd e e₁) = EAdd (strip e) (strip e₁)
  strip (DLam e)  = ELam (strip e)
  strip (DApp e e₁)  = EApp (strip e) (strip e₁)
  strip (SPair e e₁)  = EPair (strip e) (strip e₁) 
  strip (SInl e)  = EInl (strip e)
  strip (SInr e)  = EInr (strip e)
  strip (SFst e)  = EFst (strip e)
  strip (SSnd e)  = ESnd (strip e)
  strip (SCase e e₁ e₂)  = ECase (strip e) (strip e₁) (strip e₂)
  strip (DPair e e₁)  = EPair (strip e) (strip e₁) 
  strip (DInl e)  = EInl (strip e)
  strip (DInr e)  = EInr (strip e)
  strip (DFst e)  = EFst (strip e)
  strip (DSnd e)  = ESnd (strip e)
  strip (DCase e e₁ e₂)  = ECase (strip e) (strip e₁) (strip e₂)
  strip (↑ x e) = strip e



  stripLift : ∀ {α Δ Γ} → stripΔ Δ ↝ Γ → AExp Δ α  → Exp Γ (stripα α)
  stripLift Δ↝Γ = liftE Δ↝Γ ∘ strip
  


  module Equiv where
    open import Relation.Binary.PropositionalEquality

    -- Extending a value environment according to an extension of a
    -- type environment
    data _⊢_↝_ {Γ} : ∀ {Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
      refl : ∀ env → refl ⊢ env ↝ env
      extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'} →
                 (v : TInt τ) → (Γ↝Γ' ⊢  env ↝ env')  →
                 extend Γ↝Γ' ⊢ env ↝ (v ∷ env')

    env↝trans : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
                  {env env' env''} → 
                  Γ↝Γ' ⊢ env ↝ env' → Γ'↝Γ'' ⊢ env' ↝ env'' →
                  let Γ↝Γ'' = ↝-trans Γ↝Γ' Γ'↝Γ'' in
                  Γ↝Γ'' ⊢ env ↝ env'' 
    env↝trans {Γ} {.Γ''} {Γ''} {Γ↝Γ'} {.refl} {env} {.env''} {env''} env↝env' (refl .env'') = env↝env'
    env↝trans env↝env' (extend v env'↝env'') = extend v (env↝trans env↝env' env'↝env'')
    

    -- Equivalent Imp Γ α and EImp τ values (where τ = stripα α). As
    -- (v : Imp Γ α) is not necessarily closed, equivalence is defined for
    -- the closure (Env Γ, ImpΓ α)
    Equiv : ∀ {α Γ} → Env Γ → ATInt Γ α → TInt (stripα α) → Set
    Equiv {SNum} env av v = av ≡ v
    Equiv {SFun α₁ α₂} {Γ} env av v = ∀ {Γ' env' Γ↝Γ'} →
                                        (Γ↝Γ' ⊢ env ↝ env') →
                                        {av' : ATInt Γ' α₁} →
                                        {v' : TInt (stripα α₁)} →
                                        Equiv env' av' v' → Equiv env' (av Γ↝Γ' av') (v v')
    Equiv {D x} env av v = ev av env ≡ v
    Equiv {SPrd α α₁} env (ffst , ssnd) (ffst₁ , ssnd₁) = Equiv {α} env ffst ffst₁ ∧ Equiv {α₁} env ssnd ssnd₁
    Equiv {SSum α α₁} env (tl a) (tl a₁) = Equiv {α} env a a₁
    Equiv {SSum α α₁} env (tl a) (tr b) = ⊥ 
    Equiv {SSum α α₁} env (tr b) (tl a) = ⊥ 
    Equiv {SSum α α₁} env (tr b) (tr b₁) = Equiv {α₁} env b b₁ 
 
    data Equiv-Env {Γ' : _} (env' : Env Γ') :
      ∀ {Δ} → let Γ = stripΔ Δ in
      AEnv Γ' Δ → Env Γ → Set where
      [] : Equiv-Env env' [] []
      cons : ∀ {α Δ} → let τ = stripα α
                           Γ = stripΔ Δ in
              {env : Env Γ} → {aenv : AEnv Γ' Δ} → 
              Equiv-Env env' aenv env →
              (va : ATInt (Γ') α) → (v : TInt τ) → 
              Equiv env' va v → 
              --Equiv-Env env' (cons α va (aenv)) (v ∷ env)
              Equiv-Env env' (cons {α = α} va (aenv)) (v ∷ env)


 
  module Proof where
    open Equiv
    open import Relation.Binary.PropositionalEquality

    -- Extensional equality as an axiom to prove the Equivalence of
    -- function values.  We could (should?) define it locally for
    -- Equiv.
    postulate ext : ∀ {τ₁ τ₂} {f g : TInt τ₁ → TInt τ₂} →
                    (∀ x → f x ≡ g x) → f ≡ g

    -- Ternary helper relation for environment extensions, analogous to _↝_↝_ for contexts
    data _⊢_↝_↝_⊣ : ∀ { Γ Γ' Γ''} → Γ ↝ Γ' ↝ Γ'' → Env Γ → Env Γ' → Env Γ'' → Set where
      refl : ∀ {Γ Γ''} {Γ↝Γ'' : Γ ↝ Γ''} { env env'' } →
             Γ↝Γ'' ⊢ env ↝ env'' →
             refl Γ↝Γ'' ⊢ env ↝ [] ↝ env'' ⊣
      extend : ∀ {Γ Γ' Γ'' τ} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''} { env env' env'' } →
               Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ →
               (v : TInt τ) → extend Γ↝Γ'↝Γ'' ⊢ (v ∷ env) ↝ (v ∷ env') ↝ (v ∷ env'') ⊣



    -- the following lemmas are strong versions of the shifting
    -- functions, proving that consistent variable renaming preserves
    -- equivalence (and not just typing).
    lookup-elevate-≡ : ∀ {τ Γ Γ'} {Γ↝Γ' : Γ ↝ Γ'}
                       {env : Env Γ} {env' : Env Γ'} →
                       Γ↝Γ' ⊢ env ↝ env' → 
                       (x : τ ∈ Γ) → lookupE x env ≡ lookupE (elevate-var Γ↝Γ' x) env'
    lookup-elevate-≡ {τ} {.Γ'} {Γ'} {.refl} {.env'} {env'} (refl .env') x = refl
    lookup-elevate-≡ (extend v env↝env') x = lookup-elevate-≡ env↝env' x

    lookup-elevate2-≡ : ∀ {τ Γ Γ' Γ''} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                       {env : Env Γ} {env' : Env Γ'} {env'' : Env Γ''} →
                       Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ → 
                       (x : τ ∈ Γ) → lookupE x env ≡ lookupE (elevate-var2 Γ↝Γ'↝Γ'' x) env''
    lookup-elevate2-≡ (refl Γ↝Γ') x = lookup-elevate-≡ Γ↝Γ' x
    lookup-elevate2-≡ (extend env↝env'↝env'' v) hd = refl
    lookup-elevate2-≡ (extend env↝env'↝env'' _) (tl x)
      rewrite lookup-elevate2-≡ env↝env'↝env'' x = refl


    lem-elevate-≡ : ∀ {τ Γ Γ' Γ''}
                      {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                      {env : Env Γ} {env' : Env Γ'} {env'' : Env Γ''} →
                      Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ →
                      (e : Exp Γ τ) →
                      ev e env ≡ ev (elevate Γ↝Γ'↝Γ'' e) env''
    lem-elevate-≡ env↝env' (EVar x) = lookup-elevate2-≡ env↝env' x
    lem-elevate-≡ env↝env' (ECst x) = refl
    lem-elevate-≡ env↝env' (EAdd e e₁) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' e₁
    ... | IA1 | IA2 = cong₂ _+_ IA1 IA2
    lem-elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''}
                  {env = env}
                  {env'' = env''}
                  env↝env' (ELam e) = ext lem-elevate-≡-body
       where lem-elevate-≡-body : ∀ x → ev e (x ∷ env) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e) (x ∷ env'')
             lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e
    lem-elevate-≡ env↝env' (EApp e e₁) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' e₁
    ... | IA1 | IA2  = cong₂ (λ f₁ x → f₁ x) IA1 IA2
    lem-elevate-≡ env↝env' (EPair e e₁) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' e₁
    ... | IA1 | IA2  = cong₂ (λ x y → x , y) IA1 IA2
    lem-elevate-≡ env↝env' (EInl e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → tl x) IA
    lem-elevate-≡ env↝env' (EInr e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → tr x) IA
    lem-elevate-≡ env↝env' (EFst e) with lem-elevate-≡ env↝env' e 
    ... | IA  = cong (λ x → fst x) IA
    lem-elevate-≡ env↝env' (ESnd e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → snd x) IA
    lem-elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''} 
                  {env = env}
                  {env'' = env''}
                  env↝env' (ECase e e₁ e₂) with ev e env | ev (elevate Γ↝Γ'↝Γ'' e) env'' | lem-elevate-≡ env↝env' e
    ... | tl c | tl c' | IA rewrite (→tl {x' = c} {y' = c'} (tl c) (tl c') IA refl refl) = lem-elevate-≡-body c'
         where lem-elevate-≡-body : ∀ x → ev e₁ (x ∷ env) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e₁) (x ∷ env'')
               lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e₁
    ... | tl c | tr c' | ()
    ... | tr c | tl c' | ()
    ... | tr c | tr c' | IA rewrite (→tr {x' = c} {y' = c'} (tr c) (tr c') IA refl refl) = lem-elevate-≡-body c'
         where lem-elevate-≡-body : ∀ x → ev e₂ (x ∷ env) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e₂) (x ∷ env'')
               lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e₂





    lem-lift-refl-id : ∀ {α Γ} → let τ = stripα α in
                       (env : Env Γ) →
                       (v : TInt τ) (va : ATInt Γ α) →
                       Equiv env va v → 
                       Equiv env (lift α refl va) v
    lem-lift-refl-id {SNum} env v va eq = eq
    lem-lift-refl-id {SFun α α₁} {Γ} env v va eq = body
        where body : ∀ {Γ'} {env' : Env Γ'} {Γ↝Γ' : Γ ↝ Γ'} →
                     Γ↝Γ' ⊢ env ↝ env' →
                     {av' : ATInt Γ' α} {v' : TInt (stripα α)} → 
                     Equiv env' av' v' → Equiv env' (va (↝-trans refl Γ↝Γ') av') (v v')
              body {Γ↝Γ' = Γ↝Γ'} env↝env' eq' rewrite sym (lem-↝-refl-id Γ↝Γ') = eq env↝env' eq' 
    
    lem-lift-refl-id {D x} env v va eq rewrite sym eq = sym (lem-elevate-≡ (refl (refl env)) va)
    lem-lift-refl-id {SPrd α α₁} env (ffst , ssnd) (ffst₁ , ssnd₁) (∧-intro x x₁) = ∧-intro (lem-lift-refl-id {α} env ffst ffst₁ x) 
                                                                                         (lem-lift-refl-id {α₁} env ssnd ssnd₁ x₁)
    lem-lift-refl-id {SSum α α₁} env (tl a) (tl a₁) eq = lem-lift-refl-id  env a a₁ eq
    lem-lift-refl-id {SSum α α₁} env (tl a) (tr b) ()
    lem-lift-refl-id {SSum α α₁} env (tr b) (tl a) () 
    lem-lift-refl-id {SSum α α₁} env (tr b) (tr b₁) eq = lem-lift-refl-id  env b b₁ eq



  
    -- lifting an Imp does not affect equivalence
    lem-lift-equiv : ∀ {α Γ Γ'} → let τ = stripα α in
                     {Γ↝Γ' : Γ ↝ Γ'} →
                     (va : ATInt Γ α) (v : TInt τ) →
                     {env : Env Γ} {env' : Env Γ'} → 
                     Γ↝Γ' ⊢ env ↝ env' → 
                     Equiv env va v →
                     Equiv env' (lift α Γ↝Γ' va) v
    lem-lift-equiv va v {.env'} {env'} (refl .env') eq = lem-lift-refl-id env' v va eq 
    lem-lift-equiv {SNum} va v (extend v₁ env↝env') eq = eq
    lem-lift-equiv {SFun α α₁} va v (extend v₁ env↝env') eq = 
      λ v₁env₁↝env' eq₁ → eq (env↝trans (extend v₁ env↝env') v₁env₁↝env') eq₁
    lem-lift-equiv {D x} va v (extend v₁ env↝env') eq rewrite sym eq = sym (lem-elevate-≡ (refl (extend v₁ env↝env')) va)
    lem-lift-equiv {SPrd α α₁} (ffst , ssnd) (ffst₁ , ssnd₁) (extend v₁ env↝env') (∧-intro x x₁) =
      ∧-intro (lem-lift-equiv {α} ffst ffst₁ (extend v₁ env↝env') x) (lem-lift-equiv {α₁} ssnd ssnd₁ (extend v₁ env↝env') x₁)
    lem-lift-equiv {SSum α α₁} (tl a) (tl a₁) (extend v₁ env↝env') eq = lem-lift-equiv  a a₁ (extend v₁ env↝env') eq
    lem-lift-equiv {SSum α α₁} (tl a) (tr b) (extend v₁ env↝env') () 
    lem-lift-equiv {SSum α α₁} (tr b) (tl a) (extend v₁ env↝env') ()
    lem-lift-equiv {SSum α α₁} (tr b) (tr b₁) (extend v₁ env↝env') eq = lem-lift-equiv  b b₁ (extend v₁ env↝env') eq




    lem-equiv-lookup : ∀ {α Δ Γ'} → let Γ = stripΔ Δ in
                       { aenv : AEnv Γ' Δ } {env : Env Γ} →
                       (env' : Env Γ') →
                       Equiv-Env env' aenv env →
                       ∀ x → Equiv {α} env' (lookup aenv x) (lookupE (strip-lookup x) env)
    lem-equiv-lookup env' [] ()
    lem-equiv-lookup env' (cons  enveq va v eq) hd = eq
    lem-equiv-lookup env' (cons  enveq va v eq) (tl x) = lem-equiv-lookup env' enveq x

    lem-equiv-env-lift-extend :
      ∀ {σ Γ' Δ} (env' : Env Γ') → let Γ = stripΔ Δ in
        {env : Env Γ} {aenv : AEnv Γ' Δ} →
        Equiv-Env env' aenv env → (x : TInt σ) →
        Equiv-Env (x ∷ env') (liftEnv (extend refl) aenv) env
    lem-equiv-env-lift-extend _ [] x = []
    lem-equiv-env-lift-extend env' (cons {α} eqenv va v x) x₁ =
      cons (lem-equiv-env-lift-extend env' eqenv x₁)
           (lift α (extend refl) va) v (lem-lift-equiv va v (extend x₁ (refl env')) x)

    lem-equiv-env-lift-lift :
      ∀ {Γ' Γ'' Δ} → let Γ = stripΔ Δ in
        {Γ↝Γ' : Γ' ↝ Γ''}
        {env' : Env Γ'} {env'' : Env Γ''}
        (env'↝env'' : Γ↝Γ' ⊢ env' ↝ env'') →
        {env : Env Γ} {aenv : AEnv Γ' Δ} →
        Equiv-Env env' aenv env → 
        Equiv-Env env'' (liftEnv Γ↝Γ' aenv) env
    lem-equiv-env-lift-lift env'↝env'' [] = []
    lem-equiv-env-lift-lift {Γ↝Γ' = Γ↝Γ'} env'↝env'' (cons {α} eqenv va v x)
      with lem-equiv-env-lift-lift env'↝env'' eqenv
    ... | IA = cons IA (lift α Γ↝Γ' va) v (lem-lift-equiv va v env'↝env'' x)

   
  --------------------------------
  --"lift-correct" equivalence lemma
  --------------------------------
    open import Data.Product
    mutual 
      lift-correct : ∀ {Γ α} (lft : Liftable α) (env : Env Γ) (av : ATInt Γ α) (v : TInt (typeof α)) →  
                     Equiv env av v → (Equiv env (lift' lft av) v)
      lift-correct (D τ) env av v eq = eq
      lift-correct SCst env av v eq = eq
      lift-correct (SSum lft lft₁) env (tl a) (tl a₁) eq with lift-correct lft env a a₁ 
      ... | IA rewrite IA eq = refl
      lift-correct (SSum lft lft₁) env (tr b) (tl a) ()
      lift-correct (SSum lft lft₁) env (tl a) (tr b) ()
      lift-correct (SSum lft lft₁) env (tr b) (tr b₁) eq with lift-correct lft₁ env b b₁ 
      ... | IA rewrite IA eq = refl
      lift-correct (SPrd lft lft₁) env (ffst , ssnd) (ffst₁ , ssnd₁) (∧-intro x x₁) 
        rewrite lift-correct lft env ffst ffst₁ x | lift-correct lft₁ env ssnd ssnd₁ x₁ = refl
      lift-correct (SFun x lft) env av v eq =  
        ext (λ x₁ →
               lift-correct lft (x₁ ∷ env)
               (av (extend refl) (embed x (EVar hd))) (v x₁) (eq (extend x₁ (refl env)) (embed-correct x (x₁ ∷ env) (EVar hd) x₁ refl)))
 
      embed-correct : ∀ {Γ α} (lft : Liftable⁻ α) (env : Env Γ) →  (e : Exp Γ (typeof α)) → (v : TInt (typeof α)) → 
                      ev e env  ≡ v → Equiv env (embed lft e) v
      embed-correct (D τ) env e v eq rewrite eq = refl
      embed-correct (SPrd lft lft₁) env e (fstv , sndv) eq  = ∧-intro (embed-correct lft env (EFst e) fstv (subst (λ x → ffst x ≡ fstv) (sym eq) refl)) 
                                                                   (embed-correct lft₁ env (ESnd e) sndv
                                                                      (subst (λ x → ssnd x ≡ sndv) (sym eq) refl))
      embed-correct {α = SFun α₁ α₂} (SFun x lft) env e v eq = f
        where 

              f : ∀ {Γ' env' Γ↝Γ'} (x₁ : Γ↝Γ' ⊢ env ↝ env') {x₂ : ATInt Γ' α₁} {x₃ : TInt (typeof α₁)}
                    (x₄ : Equiv env' x₂ x₃) →
                    Equiv env'
                    (embed lft (EApp (elevate (refl Γ↝Γ') e) (lift' x x₂))) (v x₃)
              f {Γ'} {env'} {Γext} envext {av'} {v'} eq' = 
                                                            embed-correct lft env' (EApp (elevate (refl Γext) e) (lift' x av')) (v v') 
                                                               g
                where g : ev (elevate (refl Γext) e) env' (ev (lift' x av') env') ≡ v v'
                      g rewrite lift-correct x env' av' v' eq'  
                              | sym (cong (λ f → f v') (lem-elevate-≡ (refl envext) e)) 
                              |  (cong (λ f → f v') eq) = refl
  
 

    ---------------------------------------
    --Correctness proof with liftable terms
    ---------------------------------------

    -- When we partially evaluate somthing under an environment , it
    -- will give equivalent results to a ``complete'' evaluation under
    -- an equivalent environment 
    pe-correct : ∀ { α Δ Γ' } → (e : AExp Δ α) →
                 let Γ = stripΔ Δ in 
                 {aenv : AEnv Γ' Δ} → {env : Env Γ} → 
                 (env' : Env Γ') →
                 Equiv-Env env' aenv env → 
                 Equiv env' (pe e aenv) (ev (strip e) env)
    pe-correct (Var x) env' eqenv = lem-equiv-lookup env' eqenv x
    pe-correct (SCst x) env' eqenv = refl
    pe-correct (SAdd e e₁) env' eqenv 
      rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
    pe-correct (SLam e) env' eqenv = 
     λ {_} {env''} env'↝env'' {av'} {v'} eq →
         let eqenv' : _
             eqenv' = lem-equiv-env-lift-lift env'↝env'' eqenv
             eqenv'' : _
             eqenv'' = cons eqenv' av' v' eq
         in pe-correct e env'' eqenv''
    pe-correct (SApp e e₁) env' eqenv 
      with pe-correct e env' eqenv | pe-correct e₁ env' eqenv
    ... | IAe | IAf = IAe (refl env') IAf
    pe-correct (DCst x) env' eqenv = refl
    pe-correct (DAdd e e₁) env' eqenv
      rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
    pe-correct (DLam e) env' eqenv = 
     ext
      (λ x →
         let eqenv₁ : _
             eqenv₁ = lem-equiv-env-lift-extend env' eqenv x
             eqenv₂ : _
             eqenv₂ = cons eqenv₁ (EVar hd) x refl
         in pe-correct e (x ∷ env') eqenv₂)
    pe-correct (DApp e e₁) env' eqenv 
      with pe-correct e₁ env' eqenv | pe-correct e env' eqenv
    ... | IA' | IA = cong₂ (λ f x → f x) IA IA'
    pe-correct (SPair e e₁) env' eqenv = ∧-intro (pe-correct e env' eqenv) (pe-correct e₁ env' eqenv)
    pe-correct (SInl e) env' eqenv = pe-correct e env' eqenv
    pe-correct (SInr e) env' eqenv = pe-correct e env' eqenv
    pe-correct (SFst (SPair e e₁)) env' eqenv = pe-correct e env' eqenv
    pe-correct (SFst e) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' | ∧-intro A B = A
    pe-correct (SSnd (SPair e e₁)) env' eqenv = pe-correct e₁ env' eqenv
    pe-correct (SSnd e) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' | ∧-intro A B = B
    pe-correct {α} (SCase e e₁ e₂) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | tl c | tl c' | L = pe-correct e₁ {aenv = cons c (liftEnv refl aenv)}
                               {env = c' ∷ env} env'
                               (cons (lem-equiv-env-lift-lift (refl env') eqenv) c c' L)
    ... | tr c | tr c' | R = pe-correct e₂ {aenv = cons c (liftEnv refl aenv)}
                               {env = c' ∷ env} env'
                               (cons (lem-equiv-env-lift-lift (refl env') eqenv) c c' R)
    ... | tr c | tl c' | ()
    ... | tl c | tr c' | ()
    pe-correct (DPair e e₁) env' eqenv with pe-correct e env' eqenv | pe-correct e₁ env' eqenv 
    ... | IA | IA' rewrite IA | IA' = refl
    pe-correct (DInl e) env' eqenv with pe-correct e env' eqenv
    ... | IA rewrite IA = refl
    pe-correct (DInr e) env' eqenv with pe-correct e env' eqenv 
    ... | IA rewrite IA = refl
    pe-correct (DFst e) env' eqenv with pe-correct e env' eqenv 
    ... | IA rewrite IA = refl
    pe-correct (DSnd e) env' eqenv with pe-correct e env' eqenv
    ... | IA rewrite IA = refl
    pe-correct (DCase e e₁ e₂) {aenv = aenv} {env = env} env' eqenv with ev (pe e aenv) env' | ev (strip e) env | pe-correct e env' eqenv
    ... | tl c | tl c' | IA rewrite (→tl {x' = c} {y' = c'} (tl c) (tl c') IA refl refl) = 
      pe-correct e₁
        {aenv = cons (EVar hd) (liftEnv (extend refl) aenv)}
        {env = c' ∷ env} (c' ∷ env') (cons (lem-equiv-env-lift-lift (extend c' (refl env')) eqenv) (EVar hd) c' refl)
    ... | tr c | tr c' | IA rewrite (→tr {x' = c} {y' = c'} (tr c) (tr c') IA refl refl) = 
      pe-correct e₂
        {aenv = cons (EVar hd) (liftEnv (extend refl) aenv)}
        {env = c' ∷ env} (c' ∷ env')
        (cons (lem-equiv-env-lift-lift (extend c' (refl env')) eqenv)
         (EVar hd) c' refl)
    ... | tl c | tr c' | ()  
    ... | tr c | tl c' | ()
    pe-correct (↑ x e) {aenv = aenv} {env = env} env' eqenv  
      with pe-correct e env' eqenv 
    ... | IA = lift-correct x env' (pe e aenv) (ev (strip e) env) IA


    