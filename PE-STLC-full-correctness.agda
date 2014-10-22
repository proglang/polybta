--------------------------------------------------------------------
--correctness proof of partial evaluation of recursors and iterators
--------------------------------------------------------------------
module PE-STLC-full-correctness where
open import Data.Empty
open import PE-STLC-full
open import Lib
open Auxiliaries
open TwoLevelTerms-Simp-PSRI
open import Types
open two-level-types-simp-ps


----------------------------------------------
--module "EvaBase"
--note: it includes
--a)base type interpreter [TInt];
--b)environment [Env] for base type variables;
--c)lookup function [lookupE];
--d)evaluator for base type terms [ev].
----------------------------------------------
module EvaBase where

  ----------------------------------------
  --interpretation of the base type [Exp].
  ----------------------------------------
  TInt : Type → Set
  TInt Num = ℕ
  TInt (Fun τ₁ τ₂) = TInt τ₁ → TInt τ₂
  TInt (Prd τ₁ τ₂) = TInt τ₁ × TInt τ₂
  TInt (Sum τ₁ τ₂) = TInt τ₁ ⊎ TInt τ₂
  
  --------------------------------------
  --environment for base type variables.
  --------------------------------------
  data Env : Ctx → Set where 
    [] : Env []
    _∷_ : ∀ {τ Γ} → TInt τ → Env Γ → Env (τ ∷ Γ)
  
  -----------------------------------------------------------------------
  --[lookupE] get from the environment the corresponding value of 
  --a given free variable of base type.
  -----------------------------------------------------------------------
  lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → TInt τ
  lookupE hd (x ∷ ρ) = x
  lookupE (tl v) (_ ∷ ρ) = lookupE v ρ
  
  ---------------------------------------------------------------
  --evaluation of base terms, given a suitably typed environment.
  ---------------------------------------------------------------
  ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
  ev (EVar v) ρ = lookupE v ρ
  ev (ECst x) ρ = x
  ev (ESuc e) ρ = suc (ev e ρ)
  ev (EIt e e0 es) ρ = natit (ev e ρ) (ev e0 ρ) (ev es ρ)
  ev (ERec v u n) ρ = natrec (ev n ρ) (ev v ρ) (ev u ρ)
  ev (EAdd e f) ρ = ev e ρ + ev f ρ
  ev (ELam e) ρ = λ x → ev e (x ∷ ρ)
  ev (EApp e f) ρ = ev e ρ (ev f ρ)
  ev (EPair e f) ρ = ev e ρ , ev f ρ
  ev (EFst e) ρ = proj₁ (ev e ρ)
  ev (ESnd e) ρ = proj₂ (ev e ρ)
  ev (EInl e) ρ = inj₁ (ev e ρ)
  ev (EInr e) ρ = inj₂ (ev e ρ)
  ev (ECase e e₁ e₂) ρ with ev e ρ
  ... | inj₁ v = ev e₁ (v ∷ ρ)
  ... | inj₂ v = ev e₂ (v ∷ ρ)

open EvaBase public

module Examples where
  
  module Example-Arithmetic where
    open EvaBase

    add : AExp [] (SFun SNum (D (Fun Num Num)))
    add = SLam (DLam (SIt (Var (tl hd)) (Var hd) (SLam (DSuc (Var hd)))))

    pe_add : ℕ → Exp [] (Fun Num Num)
    pe_add n = pe (SApp add (SCst n)) []

    mult : AExp [] (SFun SNum (D (Fun Num Num)))
    mult = SLam (DLam (SIt (Var (tl hd)) (DCst 0) (SLam (DAdd (Var hd) (Var (tl hd))))))

    multn : ℕ → AExp [] (D (Fun Num Num))
    multn n = SApp mult (SCst n)

    pe_mult : ℕ → Exp [] (Fun Num Num)
    pe_mult n = pe (multn n) []

    dmult : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
    dmult = DLam (DLam (DIt (Var (tl hd)) (DCst 0) (DLam (DAdd (Var hd) (Var (tl hd))))))

    pe_dmult3 : Exp [] (Fun Num Num)
    pe_dmult3 = pe (DApp dmult (DCst 3)) []

    power : AExp [] (SFun SNum (D (Fun Num Num))) 
    power = SLam (DLam (DApp (DLam
            (SIt (Var (tl (tl hd)))
                  (DCst 1)
                  (SLam (DApp (DApp (Var (tl hd)) (Var hd)) (Var (tl (tl hd))))))) dmult))

    pe_power : ℕ → Exp [] (Fun Num Num)
    pe_power n = pe (SApp power (SCst n)) []

    predecessor : AExp [] (SFun SNum SNum)
    predecessor = SLam (SFst (SIt (Var hd) (SPair (SCst 0) (SCst 0))
                                            (SLam (SPair (SSnd (Var hd))
                                                  (SSuc (SSnd (Var hd)))))))

    pe_predecessor : ℕ → ℕ
    pe_predecessor n = pe {[]} (SApp predecessor (SCst n)) []

    iter : Exp [] (Fun (Fun Num Num) (Fun Num Num))
    iter = ELam (ELam (EIt (ESuc (EVar hd)) (ECst 1) (EVar (tl hd))))

    ack : Exp [ Fun (Fun Num Num) (Fun Num Num) ] (Fun Num (Fun Num Num))
    ack = ELam (EIt (EVar hd) (ELam (ESuc (EVar hd))) (EVar (tl hd)))

    ack-m-n : ℕ → ℕ → ℕ
    ack-m-n m n = ev (EApp (EApp ack (ECst m)) (ECst n)) (ev iter [] ∷ [])
    
    siter : AExp [] (SFun (D (Fun Num Num)) (SFun SNum (D Num)))
    siter = SLam (SLam (SIt (SSuc (Var hd)) (DCst 1) (SLam (DApp (Var (tl (tl hd))) (Var hd)))))

    diter : AExp [] (SFun (D (Fun Num Num)) (D (Fun Num Num)))
    diter = SLam (DLam (DIt (DSuc (Var hd)) (DCst 1) (Var (tl hd))))

    sack : AExp [ D (Fun (Fun Num Num) (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
    sack = SLam (SIt (Var hd) (DLam (DSuc (Var hd))) (SLam (DApp (Var (tl (tl hd))) (Var hd))))

    sack-m : ℕ → Exp [] (Fun Num Num)
    sack-m m = pe (SApp sack (SCst m)) (iter ∷ [])

    sack' : AExp [ SFun (D (Fun Num Num)) (D (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
    sack' = SLam (SIt (Var hd) (DLam (DSuc (Var hd))) (Var (tl hd)))

    sack'-m : ℕ → Exp [] (Fun Num Num)
    sack'-m m = pe (SApp (SLam (SApp sack' (SCst m))) diter) []

    Add : AExp [] (SFun SNum (D (Fun Num Num)))
    Add = SLam (DLam (SRec (Var hd) (SLam (SLam (DSuc (Var hd)))) (Var (tl hd))))

    pe_Add : ℕ → Exp [] (Fun Num Num)
    pe_Add n = pe (SApp Add (SCst n)) []

    Mult : AExp [] (SFun SNum (D (Fun Num Num)))
    Mult = SLam (DLam (SRec (DCst 0) (SLam (SLam (DAdd (Var hd) (Var (tl (tl hd)))))) (Var (tl hd))))

    Multn : ℕ → AExp [] (D (Fun Num Num))
    Multn n = SApp Mult (SCst n)

    pe_Mult : ℕ → Exp [] (Fun Num Num)
    pe_Mult n = pe (Multn n) []

    dMult : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
    dMult = DLam (DLam (DRec (DCst 0) (DLam (DLam (DAdd (Var hd) (Var (tl (tl hd)))))) (Var (tl hd))))

    pe_dMult3 : Exp [] (Fun Num Num)
    pe_dMult3 = pe (DApp dMult (DCst 3)) []

    Power : AExp [] (SFun SNum (D (Fun Num Num)))
    Power = SLam (DLam (DApp (DLam
            (SIt (Var (tl (tl hd)))
                  (DCst 1)
                  (SLam (DApp (DApp (Var (tl hd)) (Var hd)) (Var (tl (tl hd))))))) dMult))

    pe_Power : ℕ → Exp [] (Fun Num Num)
    pe_Power n = pe (SApp Power (SCst n)) []

    Predecessor : AExp [] (SFun SNum SNum)
    Predecessor = SLam (SRec (SCst 0) (SLam (SLam (Var (tl hd)))) (Var hd))

    pe_Predecessor : ℕ → ℕ
    pe_Predecessor n = pe {[]} (SApp Predecessor (SCst n)) []

    Iter : Exp [] (Fun (Fun Num Num) (Fun Num Num))
    Iter = ELam (ELam (ERec (ECst 1) (ELam (EVar (tl (tl hd)))) (ESuc (EVar hd))))

    Ack : Exp [ Fun (Fun Num Num) (Fun Num Num) ] (Fun Num (Fun Num Num))
    Ack = ELam (ERec (ELam (ESuc (EVar hd))) (ELam (EVar (tl (tl hd)))) (EVar hd))

    Ack-m-n : ℕ → ℕ → ℕ
    Ack-m-n m n = ev (EApp (EApp Ack (ECst m)) (ECst n)) (ev Iter [] ∷ [])
    
    Siter : AExp [] (SFun (D (Fun Num Num)) (SFun SNum (D Num)))
    Siter = SLam (SLam (SRec (DCst 1) (SLam (SLam (DApp (Var (tl (tl (tl hd)))) (Var hd)))) (SSuc (Var hd))))

    Diter : AExp [] (SFun (D (Fun Num Num)) (D (Fun Num Num)))
    Diter = SLam (DLam (DRec (DCst 1) (DLam (Var (tl (tl hd)))) (DSuc (Var hd))))

    Sack : AExp [ D (Fun (Fun Num Num) (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
    Sack = SLam (SRec (DLam (DSuc (Var hd))) (SLam (SLam (DApp (Var (tl (tl (tl hd)))) (Var hd)))) (Var hd))

    Sack-m : ℕ → Exp [] (Fun Num Num)
    Sack-m m = pe (SApp Sack (SCst m)) (Iter ∷ [])

    Sack' : AExp [ SFun (D (Fun Num Num)) (D (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
    Sack' = SLam (SRec (DLam (DSuc (Var hd))) (SLam (Var (tl (tl hd)))) (Var hd))

    Sack'-m : ℕ → Exp [] (Fun Num Num)
    Sack'-m m = pe (SApp (SLam (SApp Sack' (SCst m))) Diter) []

  module Example-Lifting where
    open import Data.Empty
    open import Relation.Nullary.Decidable
    open import Data.Product

    lift-dec : (α : AType) → Dec (Liftable α)
    lift-dec⁻ : (α : AType) → Dec (Liftable⁻ α)

    lift-dec SNum = yes SCst
    lift-dec (SFun α α₁) with lift-dec⁻ α | lift-dec α₁
    ... | yes lm | yes l = yes (SFun lm l)
    ... | no  nlm | _   = no f
      where f : (x : Liftable (SFun α α₁)) → ⊥
            f (SFun x₁ x₂) = nlm x₁
    ... |  _ | no nl = no f
      where f : (x : Liftable (SFun α α₁)) → ⊥
            f (SFun x₁ x₂) = nl x₂
    lift-dec (SPrd α α₁) with lift-dec α | lift-dec α₁
    ... | yes lm | yes l = yes (SPrd lm l)
    ... | no  nlm | _   = no f
      where f : (x : Liftable (SPrd α α₁)) → ⊥
            f (SPrd x₁ x₂) = nlm x₁
    ... |  _ | no nl = no f
      where f : (x : Liftable (SPrd α α₁)) → ⊥
            f (SPrd x₁ x₂) = nl x₂
    lift-dec (SSum α α₁) with lift-dec α | lift-dec α₁
    ... | yes lm | yes l = yes (SSum lm l)
    ... | no  nlm | _   = no f
      where f : (x : Liftable (SSum α α₁)) → ⊥
            f (SSum x₁ x₂) = nlm x₁
    ... |  _ | no nl = no f
      where f : (x : Liftable (SSum α α₁)) → ⊥
            f (SSum x₁ x₂) = nl x₂
    lift-dec (D x) = yes (D x)
    lift-dec⁻ SNum = no (λ ())
    lift-dec⁻ (SFun α α₁) with lift-dec α | lift-dec⁻ α₁
    ... | yes lm | yes l = yes (SFun lm l)
    ... | no  nlm | _   = no f
      where f : (x : Liftable⁻ (SFun α α₁)) → ⊥
            f (SFun x₁ x₂) = nlm x₁
    ... |  _ | no nl = no f
      where f : (x : Liftable⁻ (SFun α α₁)) → ⊥
            f (SFun x₁ x₂) = nl x₂
    lift-dec⁻ (SPrd α α₁) with lift-dec⁻ α | lift-dec⁻ α₁
    ... | yes lm | yes l = yes (SPrd lm l)
    ... | no  nlm | _   = no f
      where f : (x : Liftable⁻ (SPrd α α₁)) → ⊥
            f (SPrd x₁ x₂) = nlm x₁
    ... |  _ | no nl = no f
      where f : (x : Liftable⁻ (SPrd α α₁)) → ⊥
            f (SPrd x₁ x₂) = nl x₂
    lift-dec⁻ (SSum α α₁) = no (λ ())
    lift-dec⁻ (D x) = yes (D x)

    --------------------------------- 
    -- Proving liftable by reflection
    ---------------------------------
    try-lift : ∀ {α Γ} → AExp Γ α → Dec (Liftable α)
    try-lift {α} _ = lift-dec α 

    ex-liftable1 : Liftable (SFun (D Num) (D Num))
    ex-liftable1 = from-yes (lift-dec (SFun (D Num) (D Num)))

    infer-lift' : {α : AType} {Δ : ACtx} → AExp Δ α → From-yes (lift-dec α)
    infer-lift' e = from-yes (try-lift e)

    infer-lift : ∀ {α Δ} → AExp Δ α → From-yes (lift-dec α) × AExp Δ α
    infer-lift e = infer-lift' e , e

    lift-id : AExp [] (SFun (D Num) (D Num)) → AExp [] (D (Fun Num Num))
    lift-id e = Lift (infer-lift' e) e

    ilift : ∀ {α Δ} → Liftable α × AExp Δ α → AExp Δ (D (typeof α))
    ilift p = uncurry Lift p

    -----------
    -- examples
    -----------
    e1 : AExp [] (SFun (D Num) (D Num))
    e1 = (SLam (Var hd))

    --------------------
    -- Liftable inferred
    --------------------
    e1-lifted : _
    e1-lifted = ilift (infer-lift e1)

   ----------------------------------------------------------------------
   -- liftable inferred, without type signature; the only type needed is
   -- for the function parameter (and the context)
   -----------------------------------------------------------------------
    e1-lifted' : AExp [] _
    e1-lifted' = ilift (infer-lift (SLam {α₁ = D Num} (Var hd)))

   -------------------------------------
   -- duplication of α (first parameter)
   -------------------------------------
    e2 : AExp [] (SFun (SFun (D Num) (D Num)) (SFun (D Num) (D (Prd Num Num))))
    e2 = (SLam 
          (SLam (DPair (SApp (Var (tl hd)) (Var hd))
                (DApp (ilift (infer-lift {α} (Var (tl hd))) ) (Var hd)))))
     where α = (SFun (D Num) (D Num))

 

----------------------------------------------------------------------
--module "correctness"
--note: the notion of correctness of partial evaluation
--      of a program
--a)result of evaluating the "stripped" program;
--b)evaluating the partial evaluation result of the 
--  the program;
--c)"equality" between a) and b);
--d)"equality" instead of syntactic equality because 
--  the differences of evaluating static functions
--  between a) and b),
--  TInt (stripα (SFun α₁ α₂)) = TInt (stripα α₁) → TInt (stripα α₂)
--  ATInt Γ (SFun α₁ α₂) = Γ' → Γ ↝ Γ' → (ATInt Γ' α₁ → ATInt Γ' α₂);
--e)"equality" between these two evaluation of static functions should
--  be function extensionality.
----------------------------------------------------------------------
module correctness where
  open EvaBase

  --------------------------------------------------------------
  --module "Equiv"
  --note: it specifies the "equivalence" relation between two
  --      evaluation results,including
  --a)equivalence relation between two evaluation terms [Equiv];
  --b)equivalence relation between two environments [Equiv-Env].
  --------------------------------------------------------------
  module Equiv where
    open import Data.Empty
    
    -------------------------------------------------------
    --[_⊢_↝_] Extending a base value environment according 
    --to an extension of the corresponding type environment
    -------------------------------------------------------
    data _⊢_↝_ :
      ∀ {Γ Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
      refl : ∀ {Γ} {ρ : Env Γ} → refl ⊢ ρ ↝ ρ
      extend : ∀ {τ Γ Γ' ρ ρ'} → {Γ↝Γ' : Γ ↝ Γ'} →
                 (v : TInt τ) → Γ↝Γ' ⊢ ρ ↝ ρ' →
                 extend Γ↝Γ' ⊢ ρ ↝ (v ∷ ρ')
    
    -----------------------
    --[_⊢_↝_] is transitive
    -----------------------
    env↝trans : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
             {ρ ρ' ρ''} → 
             Γ↝Γ' ⊢ ρ ↝ ρ' → Γ'↝Γ'' ⊢ ρ' ↝ ρ'' →
             let Γ↝Γ'' = Γ↝Γ' ⊕ Γ'↝Γ'' in
             Γ↝Γ'' ⊢ ρ ↝ ρ'' 
    env↝trans ρ↝ρ' (refl) = ρ↝ρ'
    env↝trans ρ↝ρ' (extend v ρ'↝ρ'') = extend v (env↝trans ρ↝ρ'  ρ'↝ρ'')


    -------------------------------------------------------------
    --[Equiv] equivalence relation between two evaluation results
    -------------------------------------------------------------
    Equiv : ∀ {α Γ} →
           (ρ : Env Γ) → (vₐ : ATInt Γ α) → (v : TInt (typeof α)) → Set
    Equiv {SNum} ρ nₐ n = nₐ ≡ n 
    Equiv {D x} ρ e v = ev e ρ ≡ v
    Equiv {SFun α₁ α₂} {Γ} ρ fₐ f =
          ∀ {Γ' ρ' Γ↝Γ'} → (Γ↝Γ' ⊢ ρ ↝ ρ') →
            {xₐ : ATInt Γ' α₁} → {x : TInt (typeof α₁)} →
            Equiv ρ' xₐ x → Equiv ρ' (fₐ Γ↝Γ' xₐ) (f x)
    Equiv {SPrd α α₁} ρ (proj₁ , proj₂) (proj₁' , proj₂') =
          Equiv ρ proj₁ proj₁' × Equiv ρ proj₂ proj₂' 
    Equiv {SSum α α₁} ρ (inj₁ a) (inj₁ a₁) = Equiv ρ a a₁
    Equiv {SSum α α₁} ρ (inj₂ b) (inj₂ b₁) = Equiv ρ b b₁ 
    Equiv {SSum α α₁} ρ (inj₁ a) (inj₂ b) = ⊥  
    Equiv {SSum α α₁} ρ (inj₂ b) (inj₁ a) = ⊥  

    --------------------------------------------------
    --[Equiv-Env] equivalence between two environments
    -------------------------------------------------- 
    stripα = typeof

    stripΔ : ACtx → Ctx
    stripΔ = map stripα

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
              Equiv-Env env' (_∷_ {α = α} va (aenv)) (v ∷ env)
  

  -------------------------------------------------------
  --module "Equiv-Elevate"
  --note: it contains lemmas necessary for proving
  --      the correctness of the partial evaluator [pe],
  --a)lemmas of various equalities involving a lifted 
  --  base value environment;
  --b)equivalences between lifted values and lifted value
  --  environments.
  -------------------------------------------------------
  module Equiv-Elevate where
    open Equiv
  
    -------------------------------
    --[ext] function extensionality
    -------------------------------
    postulate ext : ∀ {τ₁ τ₂} {f g : TInt τ₁ → TInt τ₂} →
                    (∀ x → f x ≡ g x) → f ≡ g

    ----------------------------------------------------------
    --[_⊢_↝_↝_⊣] similar to [_⊢_↝_], extension from the middle
    ---------------------------------------------------------- 
    data _⊢_↝_↝_⊣ : ∀ { Γ Γ' Γ''} → Γ ↝ Γ' ↝ Γ'' → Env Γ → Env Γ' → Env Γ'' → Set where
      refl : ∀ {Γ Γ''} {Γ↝Γ'' : Γ ↝ Γ''} { ρ ρ'' } →
             Γ↝Γ'' ⊢ ρ ↝ ρ'' →
             refl Γ↝Γ'' ⊢ ρ ↝ [] ↝ ρ'' ⊣
      extend : ∀ {Γ Γ' Γ'' τ} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''} { ρ ρ' ρ'' } →
               Γ↝Γ'↝Γ'' ⊢ ρ ↝ ρ' ↝ ρ'' ⊣ →
               (v : TInt τ) → extend Γ↝Γ'↝Γ'' ⊢ (v ∷ ρ) ↝ (v ∷ ρ') ↝ (v ∷ ρ'') ⊣

  
    -------------------------------------------------------------------------------------
    -- the following lemmas prove that "a lifted term combined with a consistently lifted 
    -- environment preserve the 'meaning' of the term"
    -------------------------------------------------------------------------------------
    lookup-elevate-≡ : ∀ {τ Γ Γ'} {Γ↝Γ' : Γ ↝ Γ'}
                       {ρ : Env Γ} {ρ' : Env Γ'} →
                       Γ↝Γ' ⊢ ρ ↝ ρ' → 
                       (x : τ ∈ Γ) → lookupE x ρ ≡ lookupE (elevate-var Γ↝Γ' x) ρ'
    lookup-elevate-≡ (refl) x = refl
    lookup-elevate-≡ (extend v ρ↝ρ') x = lookup-elevate-≡ ρ↝ρ' x

    lookup-elevate2-≡ : ∀ {τ Γ Γ' Γ''} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                       {ρ : Env Γ} {ρ' : Env Γ'} {ρ'' : Env Γ''} →
                       Γ↝Γ'↝Γ'' ⊢ ρ ↝ ρ' ↝ ρ'' ⊣ → 
                       (x : τ ∈ Γ) → lookupE x ρ ≡ lookupE (elevate-var2 Γ↝Γ'↝Γ'' x) ρ''
    lookup-elevate2-≡ (refl Γ↝Γ') x = lookup-elevate-≡ Γ↝Γ' x
    lookup-elevate2-≡ (extend ρ↝ρ'↝ρ'' v) hd = refl
    lookup-elevate2-≡ (extend ρ↝ρ'↝ρ'' _) (tl x)
      rewrite lookup-elevate2-≡ ρ↝ρ'↝ρ'' x = refl 


    elevate-≡ : ∀ {τ Γ Γ' Γ''}
                  {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                  {ρ : Env Γ} {ρ' : Env Γ'} {ρ'' : Env Γ''} →
                  Γ↝Γ'↝Γ'' ⊢ ρ ↝ ρ' ↝ ρ'' ⊣ →
                  (e : Exp Γ τ) →
                  ev e ρ ≡ ev (elevate Γ↝Γ'↝Γ'' e) ρ''
    elevate-≡ ρ↝ρ' (EVar x) = lookup-elevate2-≡ ρ↝ρ' x
    elevate-≡ ρ↝ρ' (ECst x) = refl
    elevate-≡ ρ↝ρ' (ESuc e) with elevate-≡ ρ↝ρ' e
    ... | IA = cong suc IA
    elevate-≡ ρ↝ρ' (EIt e e₀ e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₀ | elevate-≡ ρ↝ρ' e₁
    ... | IA | IA₀ | IA₁ = cong₃ natit IA IA₀ IA₁
    elevate-≡ ρ↝ρ' (ERec v u n) with elevate-≡ ρ↝ρ' v | elevate-≡ ρ↝ρ' u | elevate-≡ ρ↝ρ' n 
    ... | IV | IU | IN = cong₃ natrec IN IV IU
    elevate-≡ ρ↝ρ' (EAdd e e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₁
    ... | IA1 | IA2 = cong₂ _+_ IA1 IA2
    elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''}
              {ρ = ρ}
              {ρ'' = ρ''}
              ρ↝ρ' (ELam e) = ext elevate-≡-body
     where elevate-≡-body : ∀ x → ev e (x ∷ ρ) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e) (x ∷ ρ'')
           elevate-≡-body x = elevate-≡ (extend ρ↝ρ' x) e
    elevate-≡ ρ↝ρ' (EApp e e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₁
    ... | IA1 | IA2  = cong₂ (λ f₁ x → f₁ x) IA1 IA2
    elevate-≡ ρ↝ρ' (EPair e e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₁
    ... | IA1 | IA2  = cong₂ (λ x y → x , y) IA1 IA2
    elevate-≡ ρ↝ρ' (EInl e)  = cong inj₁ (elevate-≡ ρ↝ρ' e) 
    elevate-≡ ρ↝ρ' (EInr e) with elevate-≡ ρ↝ρ' e
    ... | IA  = cong (λ x → inj₂ x) IA
    elevate-≡ ρ↝ρ' (EFst e) with elevate-≡ ρ↝ρ' e 
    ... | IA  = cong (λ x → proj₁ x) IA
    elevate-≡ ρ↝ρ' (ESnd e) with elevate-≡ ρ↝ρ' e
    ... | IA  = cong (λ x → proj₂ x) IA
    elevate-≡ {ρ = ρ}
              {ρ'' = ρ''}
              ρ↝ρ' (ECase e e₁ e₂) rewrite sym (elevate-≡ ρ↝ρ' e)
                                       with ev e ρ
    ... | inj₁ x = elevate-≡ (extend ρ↝ρ' x) e₁
    ... | inj₂ y = elevate-≡ (extend ρ↝ρ' y) e₂ 

   
    --------------------------------------------------------------------------------------------
    --the following lemmas prove that "a lifted term or environment combined with a consistently
    --lifted base value environment preserve the equivalence relation" 
    ---------------------------------------------------------------------------------------------
    int↑-equiv : ∀ {α Γ Γ'} → 
                 {Γ↝Γ' : Γ ↝ Γ'} →
                 (va : ATInt Γ α) (v : TInt (typeof α)) →
                 {ρ : Env Γ} {ρ' : Env Γ'} → 
                 Γ↝Γ' ⊢ ρ ↝ ρ' → 
                 Equiv ρ va v →
                 Equiv ρ' (int↑ Γ↝Γ' va) v
    int↑-equiv va v {.ρ'} {ρ'} (refl) eq = eq 
    int↑-equiv {SNum} va v (extend v₁ ρ↝ρ') eq = eq
    int↑-equiv {SFun α α₁} va v (extend v₁ ρ↝ρ') eq = 
      λ v₁ρ₁↝ρ' eq₁ → eq (env↝trans (extend v₁ ρ↝ρ')  v₁ρ₁↝ρ') eq₁
    int↑-equiv {D x} va v (extend {ρ' = ρ'} {Γ↝Γ' = Γ↝Γ'} v₁ ρ↝ρ') eq
      rewrite sym (elevate-≡ (refl (extend {ρ' = ρ'} v₁ refl)) (int↑ Γ↝Γ' va)) | int↑-equiv va v ρ↝ρ' eq
        = refl 
    int↑-equiv {SPrd α α₁} (ffst , ssnd) (ffst₁ , ssnd₁) (extend v₁ ρ↝ρ') (x , x₁) =
      (int↑-equiv {α} ffst ffst₁ (extend v₁ ρ↝ρ') x) , (int↑-equiv {α₁} ssnd ssnd₁ (extend v₁ ρ↝ρ') x₁)
    int↑-equiv {SSum α α₁} (inj₁ a) (inj₁ a₁) (extend v₁ ρ↝ρ') eq = int↑-equiv  a a₁ (extend v₁ ρ↝ρ') eq
    int↑-equiv {SSum α α₁} (inj₂ b) (inj₂ b₁) (extend v₁ ρ↝ρ') eq = int↑-equiv  b b₁ (extend v₁ ρ↝ρ') eq
    int↑-equiv {SSum α α₁} (inj₁ a) (inj₂ b) (extend v₁ ρ↝ρ') () 
    int↑-equiv {SSum α α₁} (inj₂ b) (inj₁ a) (extend v₁ ρ↝ρ') ()

    strip-lookup : ∀ { α Δ} → α ∈ Δ → stripα α ∈ stripΔ Δ
    strip-lookup hd = hd
    strip-lookup (tl x) = tl (strip-lookup x)

    lem-equiv-lookup : ∀ {α Δ Γ'} → let Γ = stripΔ Δ in
                       { aenv : AEnv Γ' Δ } {env : Env Γ} →
                       (env' : Env Γ') →
                       Equiv-Env env' aenv env →
                       ∀ x → Equiv {α} env' (lookup x aenv) (lookupE (strip-lookup x) env)
    lem-equiv-lookup env' [] ()
    lem-equiv-lookup env' (cons  enveq va v eq) hd = eq
    lem-equiv-lookup env' (cons  enveq va v eq) (tl x) = lem-equiv-lookup env' enveq x

    env↑-equiv-extend :
      ∀ {σ Γ' Δ} (ρ' : Env Γ') → let Γ = Lib.map typeof Δ in
        {ρ : Env Γ} {aρ : AEnv Γ' Δ} →
        Equiv-Env ρ' aρ ρ → (x : TInt σ) →
        Equiv-Env (x ∷ ρ') (env↑ (extend refl) aρ) ρ
    env↑-equiv-extend _ [] x = []
    env↑-equiv-extend ρ' (cons {α} eqρ va v x) x₁ =
      cons (env↑-equiv-extend ρ' eqρ x₁)
           (int↑ (extend refl) va) v (int↑-equiv va v (extend x₁ (refl)) x)

    env↑-equiv :
      ∀ {Γ' Γ'' Δ} → let Γ = Lib.map typeof Δ in
        {Γ↝Γ' : Γ' ↝ Γ''}
        {ρ' : Env Γ'} {ρ'' : Env Γ''}
        (ρ'↝ρ'' : Γ↝Γ' ⊢ ρ' ↝ ρ'') →
        {ρ : Env Γ} {aρ : AEnv Γ' Δ} →
        Equiv-Env ρ' aρ ρ → 
        Equiv-Env ρ'' (env↑ Γ↝Γ' aρ) ρ
    env↑-equiv ρ'↝ρ'' [] = []
    env↑-equiv {Γ↝Γ' = Γ↝Γ'} ρ'↝ρ'' (cons eqρ va v x)
      with env↑-equiv ρ'↝ρ'' eqρ
    ... | IA = cons IA (int↑ Γ↝Γ' va) v (int↑-equiv va v ρ'↝ρ'' x)

    ----------------------------------
    --"lift-correct" equivalence lemma
    -----------------------------------
    mutual 
      lift-correct : ∀ {Γ α} (lft : Liftable α) (env : Env Γ) (av : ATInt Γ α) (v : TInt (typeof α)) →  
                    Equiv env av v → (Equiv env (lift lft av) v)
      lift-correct (D τ) env av v eq = eq
      lift-correct SCst env av v eq = eq
      lift-correct (SSum lft lft₁) env (inj₁ a) (inj₁ a₁) eq with lift-correct lft env a a₁ 
      ... | IA rewrite IA eq = refl
      lift-correct (SSum lft lft₁) env (inj₂ b) (inj₁ a) ()
      lift-correct (SSum lft lft₁) env (inj₁ a) (inj₂ b) ()
      lift-correct (SSum lft lft₁) env (inj₂ b) (inj₂ b₁) eq with lift-correct lft₁ env b b₁ 
      ... | IA rewrite IA eq = refl
      lift-correct (SPrd lft lft₁) env (ffst , ssnd) (ffst₁ , ssnd₁) (x , x₁) 
        rewrite lift-correct lft env ffst ffst₁ x | lift-correct lft₁ env ssnd ssnd₁ x₁ = refl
      lift-correct (SFun x lft) env av v eq =  
        ext (λ x₁ →
            lift-correct lft (x₁ ∷ env)
             (av (extend refl) (embed x (EVar hd))) (v x₁) (eq (extend x₁ (refl)) (embed-correct x (x₁ ∷ env) (EVar hd) x₁ refl)))

      embed-correct : ∀ {Γ α} (lft : Liftable⁻ α) (env : Env Γ) →  (e : Exp Γ (typeof α)) → (v : TInt (typeof α)) → 
                      ev e env  ≡ v → Equiv env (embed lft e) v
      embed-correct (D τ) env e v eq rewrite eq = refl
      embed-correct (SPrd lft lft₁) env e (fstv , sndv) eq  =
        (embed-correct lft env (EFst e) fstv (subst (λ x → proj₁ x ≡ fstv) (sym eq) refl)) , (embed-correct lft₁ env (ESnd e) sndv (subst (λ x → proj₂ x ≡ sndv) (sym eq) refl))
      embed-correct {α = SFun α₁ α₂} (SFun x lft) env e v eq = f
        where 
            f : ∀ {Γ' env' Γ↝Γ'} (x₁ : Γ↝Γ' ⊢ env ↝ env') {x₂ : ATInt Γ' α₁} {x₃ : TInt (typeof α₁)}
                  (x₄ : Equiv env' x₂ x₃) →
                  Equiv env'
                  (embed lft (EApp (int↑ Γ↝Γ' e) (lift x x₂))) (v x₃)
            f {Γ'} {env'} {Γext} envext {av'} {v'} eq' = 
                                                        embed-correct lft env' (EApp (int↑ Γext e) (lift x av')) (v v') 
                                                          g 
              where g : ev (int↑ Γext e) env' (ev (lift x av') env') ≡ v v'
                    g rewrite lift-correct x env' av' v' eq'  
                            | sym (cong (λ f → f v') (int↑-equiv e v (envext) eq))
                            |  (cong (λ f → f v') eq) = refl 

    -----------------------------------
    --"natit-correct" equivalence lemma
    -----------------------------------
    ---------------------------
    --strip off two-level terms
    ---------------------------
    strip : ∀ {α Δ} → AExp Δ α → Exp (stripΔ Δ) (stripα α)
    strip (Var x) = EVar (strip-lookup  x)
    strip (SCst x) = ECst x
    strip (SSuc e) = ESuc (strip e)
    strip (SIt e e₀ e₁) = EIt (strip e) (strip e₀) (strip e₁)
    strip (SRec v u n) = ERec (strip v) (strip u) (strip n)
    strip (SAdd e e₁) = EAdd (strip e) (strip e₁)
    strip (SLam e) = ELam (strip e)
    strip (SApp e e₁)  = EApp (strip e) (strip e₁)
    strip (DCst x)  = ECst x
    strip (DSuc e) = ESuc (strip e)
    strip (DIt e e₀ e₁) = EIt (strip e) (strip e₀) (strip e₁)
    strip (DRec v u n) = ERec (strip v) (strip u) (strip n)
    strip (DAdd e e₁) = EAdd (strip e) (strip e₁)
    strip (DLam e)  = ELam (strip e)
    strip (DApp e e₁)  = EApp (strip e) (strip e₁)
    strip (SPair e e₁)  = EPair (strip e)  (strip e₁)
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
    strip (Lift lftbl e) = strip e

    natit-correct :
          ∀ {Δ} → 
          (n : _) →
          (Γ' : List Type)
          (ρ' : AEnv Γ' Δ) (ρ'' : Env (Lib.map typeof Δ))
          (α : _)
          (e₀ : AExp Δ α) (e₁ : AExp Δ (SFun α α))
          (env'  : Env Γ')
          (IA₀ : Equiv env' (pe e₀ ρ') (ev (strip e₀) ρ'')) →
          (IA₁ : {Γ₁' : List Type} {ρ₁' : Env Γ₁'} {Γ↝Γ' : Γ' ↝ Γ₁'} →
                 Γ↝Γ' ⊢ env' ↝ ρ₁' →
                 {xₐ : ATInt Γ₁' α}
                 {x : TInt (typeof α)} →
                 Equiv ρ₁' xₐ x →
                 Equiv ρ₁' (pe e₁ ρ' Γ↝Γ' xₐ) (ev (strip e₁) ρ'' x)) →
          Equiv env'
          (natit n (pe e₀ ρ') (pe e₁ ρ' refl))
          (natit n (ev (strip e₀) ρ'') (ev (strip e₁) ρ''))
    natit-correct zero Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ = IA₀
    natit-correct (suc n) Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
      with natit-correct n Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
    ... | IA = IA₁ refl IA


    ------------------------------------
    --"natrec-correct" equivalence lemma
    ------------------------------------
    natrec-correct :
          ∀ {Δ} → 
          (n : _) →
          (Γ' : List Type)
          (ρ' : AEnv Γ' Δ) (ρ'' : Env (Lib.map typeof Δ))
          (α : _)
          (e₀ : AExp Δ α) (e₁ : AExp Δ (SFun SNum (SFun α α)))
          (env'  : Env Γ')
          (IA₀ : Equiv env' (pe e₀ ρ') (ev (strip e₀) ρ'')) →
          (IA₁ : {m₁ : _} → {m₂ : _} → m₁ ≡ m₂ → 
                 {Γ₁' : List Type} {ρ₁' : Env Γ₁'} {Γ↝Γ' : Γ' ↝ Γ₁'} →
                 Γ↝Γ' ⊢ env' ↝ ρ₁' →
                 {xₐ : ATInt Γ₁' α}
                 {x : TInt (typeof α)} →
                 Equiv ρ₁' xₐ x →
                 Equiv ρ₁' (pe e₁ ρ' Γ↝Γ' m₁ refl xₐ) (ev (strip e₁) ρ'' m₂  x)) →
          Equiv env'
          (natrec n (pe e₀ ρ') (λ n₁ → pe {Γ'} e₁ ρ' {Γ'} refl n₁ {Γ'} refl))
          (natrec n (ev (strip e₀) ρ'') (ev (strip e₁) ρ''))
    natrec-correct zero Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ =  IA₀
    natrec-correct (suc n) Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
      with natrec-correct n Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
    ... | IA = IA₁ refl refl IA



  ----------------------------------------
  --module "Proof"
  --note: the proof of correctness of [pe]
  ----------------------------------------
  module Proof where
    open Equiv
    open Equiv-Elevate

    pe-correct : ∀ { α Δ Γ' } →
      (e : AExp Δ α) →
      (ρ : Env Γ') →
      {ρ' : AEnv Γ' Δ} → {ρ'' : Env (stripΔ Δ)} → 
      Equiv-Env ρ ρ' ρ'' → 
      Equiv ρ (pe e ρ') (ev (strip e) ρ'')
    pe-correct (Var x) env' eqenv = lem-equiv-lookup env' eqenv x
    pe-correct (SCst x) env' eqenv = refl
    pe-correct (SSuc e) env' eqenv rewrite pe-correct e env' eqenv = refl
    pe-correct {Δ = Δ} {Γ' = Γ'} (SIt {α} e e₀ e₁) env' {ρ'} {ρ''} eqenv
      with pe-correct e env' eqenv | pe-correct e₀ env' eqenv | pe-correct e₁ env' eqenv
    ... | IA | IA₀ | IA₁ rewrite IA = natit-correct (ev (strip e) ρ'') Γ' ρ' ρ'' α e₀ e₁ env' IA₀
                                    IA₁
    pe-correct {Δ = Δ} {Γ' = Γ'} (SRec {α} v u n) env' {ρ'} {ρ''} eqenv 
      with pe-correct n env' eqenv | pe-correct v env' eqenv | pe-correct u env' eqenv 
    ... | IN | IV | IU rewrite IN = natrec-correct (ev (strip n) ρ'') Γ' ρ' ρ'' α v u env' IV 
      (λ {m₁} {m₂} m₁≡m₂ {Γ₁'} {ρ₁'} {Γ↝Γ'} Γ↝Γ'⊢env'↝ρ₁' → 
       IU {Γ₁'} {ρ₁'} {Γ↝Γ'} Γ↝Γ'⊢env'↝ρ₁' {m₁} {m₂} m₁≡m₂ {Γ₁'} {ρ₁'}
         {refl} refl)
     


    pe-correct (SAdd e e₁) env' eqenv 
      rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
    pe-correct (SLam e) env' eqenv = 
     λ {_} {env''} env'↝env'' {av'} {v'} eq →
       let eqenv' : _
           eqenv' = env↑-equiv env'↝env'' eqenv
           eqenv'' : _
           eqenv'' = cons eqenv' av' v' eq
       in pe-correct e env'' eqenv''
    pe-correct (SApp e e₁) env' eqenv 
      with pe-correct e env' eqenv | pe-correct e₁ env' eqenv
    ... | IAe | IAf = IAe (refl) IAf
    pe-correct (DCst x) env' eqenv = refl
    pe-correct (DSuc e) env' eqenv rewrite pe-correct e env' eqenv = refl
    pe-correct (DIt e e₀ e₁) env' eqenv rewrite pe-correct e env' eqenv | pe-correct e₀ env' eqenv | pe-correct e₁ env' eqenv = refl
    pe-correct (DRec v u n) env' eqenv rewrite pe-correct n env' eqenv | pe-correct v env' eqenv | pe-correct u env' eqenv = refl
    pe-correct (DAdd e e₁) env' eqenv
      rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
    pe-correct (DLam e) env' eqenv = 
     ext
      (λ x →
         let eqenv₁ : _
             eqenv₁ = env↑-equiv-extend env' eqenv x
             eqenv₂ : _
             eqenv₂ = cons eqenv₁ (EVar hd) x refl
         in pe-correct e (x ∷ env') eqenv₂)
    pe-correct (DApp e e₁) env' eqenv 
      with pe-correct e₁ env' eqenv | pe-correct e env' eqenv
    ... | IA' | IA = cong₂ (λ f x → f x) IA IA'
    pe-correct (SPair e e₁) env' eqenv = (pe-correct e env' eqenv) , (pe-correct e₁ env' eqenv)
    pe-correct (SInl e) env' eqenv = pe-correct e env' eqenv
    pe-correct (SInr e) env' eqenv = pe-correct e env' eqenv
    pe-correct (SFst e) env' {ρ' = aenv} {ρ'' = env} eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' |  A , B = A
    pe-correct (SSnd e) env' {aenv} {env} eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' | A , B = B
    pe-correct {α} (SCase e e₁ e₂) env' {aenv} {env} eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | inj₁ c | inj₁ c' | L = pe-correct e₁ env' (cons eqenv c c' L)
    ... | inj₂ c | inj₂ c' | R = pe-correct e₂ env' (cons eqenv c c' R)
    ... | inj₂ c | inj₁ c' | ()
    ... | inj₁ c | inj₂ c' | ()
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
    pe-correct (DCase e e₁ e₂) env' {aenv} {env} eqenv with ev (pe e aenv) env' | ev (strip e) env | pe-correct e env' eqenv
    ... | inj₁ .c' | inj₁ c' | refl = pe-correct e₁ (c' ∷ env') (cons (env↑-equiv (extend c' (refl)) eqenv) (EVar hd) c' refl)
    ... | inj₂ .c' | inj₂ c' | refl = pe-correct e₂ (c' ∷ env')
                                    (cons (env↑-equiv (extend c' (refl)) eqenv) (EVar hd) c' refl)
    ... | inj₁ c | inj₂ c' | ()  
    ... | inj₂ c | inj₁ c' | ()
    pe-correct (Lift x e) env' {aenv} {env} eqenv  
      with pe-correct e env' eqenv 
    ... | IA = lift-correct x env' (pe e aenv) (ev (strip e) env) IA 


    pe-correct-dyn :
      ∀ { τ } → (e : AExp [] (D τ)) →
      ev (pe e []) [] ≡ (ev (strip e) [])
    pe-correct-dyn e = pe-correct e [] []