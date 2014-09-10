---------------------------------------------------------------
--correctness proof of partial evaluation of liftable terms of
--static integer type 
---------------------------------------------------------------
module BTA4 where

open import BTA3-Lift
open import Lib
open Auxiliaries
open TwoLevelTypes-Simp
open TwoLevelTerms-Simp-Lift


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
  lookupE hd (x ∷ env) = x
  lookupE (tl v) (x ∷ env) = lookupE v env

  ---------------------------------------------------------------
  --evaluation of base terms, given a suitably typed environment.
  ---------------------------------------------------------------
  ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
  ev (EVar x) env = lookupE x env
  ev (ECst x) env = x
  ev (EAdd e f) env = ev e env + ev f env
  ev (ELam e) env = λ x → ev e (x ∷ env)
  ev (EApp e f) env = ev e env (ev f env)



----------------------------------------------------------------------
--module "Correctness"
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

    -------------------------------------------------------
    --[_⊢_↝_] Extending a base value environment according 
    --to an extension of the corresponding type environment
    -------------------------------------------------------
    data _⊢_↝_ {Γ} : ∀ {Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
      refl : ∀ env → refl ⊢ env ↝ env
      extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'} →
                 (v : TInt τ) → (Γ↝Γ' ⊢  env ↝ env')  →
                 extend Γ↝Γ' ⊢ env ↝ (v ∷ env')


    -----------------------
    --[_⊢_↝_] is transitive
    -----------------------
    env↝trans : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
                  {env env' env''} → 
                  Γ↝Γ' ⊢ env ↝ env' →
                  Γ'↝Γ'' ⊢ env' ↝ env'' →
                  let Γ↝Γ'' = lem-↝-trans Γ↝Γ' Γ'↝Γ'' in
                  Γ↝Γ'' ⊢ env ↝ env'' 
    env↝trans {.Γ'} {Γ'} {Γ''} {.refl} {Γ'↝Γ''} {.env'} {env'} (refl .env') env'↝env''
      rewrite sym (lem-↝-refl-id  Γ'↝Γ'') = env'↝env'' 
    env↝trans (extend v env↝env') env'↝env'' = env↝trans (extend v env↝env') env'↝env''

    
    -------------------------------------------------------------
    --[Equiv] equivalence relation between two evaluation results
    -------------------------------------------------------------
    Equiv : ∀ {α Γ} → Env Γ → ATInt Γ α → TInt (stripα α) → Set 
    Equiv {SNum} env av v = av ≡ v
    Equiv {SFun α₁ α₂} {Γ} env af f = 
        ∀ {Γ' env' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ env') →
        {ax : ATInt Γ' α₁} → {x : TInt (stripα α₁)} →
        Equiv env' ax x → Equiv env' (af Γ↝Γ' ax) (f x)
    Equiv {D x} {Γ} env av v = ev av env ≡ v 

    --------------------------------------------------
    --[Equiv-Env] equivalence between two environments
    --------------------------------------------------
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
       refl : ∀ {Γ Γ''} {Γ↝Γ'' : Γ ↝ Γ''} { env env'' } →
              Γ↝Γ'' ⊢ env ↝ env'' →
              refl Γ↝Γ'' ⊢ env ↝ [] ↝ env'' ⊣
       extend : ∀ {Γ Γ' Γ'' τ} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''} { env env' env'' } →
                Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ →
                (v : TInt τ) → extend Γ↝Γ'↝Γ'' ⊢ (v ∷ env) ↝ (v ∷ env') ↝ (v ∷ env'') ⊣


     -------------------------------------------------------------------------------------
     -- the following lemmas prove that "a lifted term combined with a consistently lifted 
     -- environment preserve the 'meaning' of the term"
     -------------------------------------------------------------------------------------
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
     lem-elevate-≡ env↝env' (EAdd e f) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' f
     ... | IA1 | IA2 = cong₂ _+_ IA1 IA2
     lem-elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''}
                   {env = env}
                   {env'' = env''}
                   env↝env' (ELam e) = ext lem-elevate-≡-body
       where lem-elevate-≡-body : ∀ x → ev e (x ∷ env) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e) (x ∷ env'')
             lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e
     lem-elevate-≡ env↝env' (EApp e f) with lem-elevate-≡ env↝env' e | lem-elevate-≡ env↝env' f
     ... | IA1 | IA2 = cong₂ (λ f₁ x → f₁ x) IA1 IA2

     --------------------------------------------------------------------------------------------
     --the following lemmas prove that "a lifted term or environment combined with a consistently
     --lifted base value environment preserve the equivalence relation" 
     ---------------------------------------------------------------------------------------------
     lem-lift-refl-id : ∀ {α Γ} → let τ = stripα α in
                        (env : Env Γ) →
                        (v : TInt τ) (va : ATInt Γ α) →
                        Equiv env va v → 
                        Equiv env (int↑ α refl va) v
     lem-lift-refl-id {SNum} env v va eq = eq
     lem-lift-refl-id {SFun α α₁} {Γ} env v va eq = body  
       where body : ∀ {Γ'} {env' : Env Γ'} {Γ↝Γ' : Γ ↝ Γ'} →
                    Γ↝Γ' ⊢ env ↝ env' →
                    {av' : ATInt Γ' α} {v' : TInt (stripα α)} → 
                    Equiv env' av' v' → Equiv env' (va (lem-↝-trans refl Γ↝Γ') av') (v v')
             body {Γ↝Γ' = Γ↝Γ'} env↝env' eq' rewrite sym (lem-↝-refl-id Γ↝Γ') = eq env↝env' eq' 
     lem-lift-refl-id {D x} env v e eq rewrite sym eq = sym (lem-elevate-≡ (refl (refl env)) e) 

    
     lem-lift-equiv : ∀ {α Γ Γ'} → let τ = stripα α in
                      {Γ↝Γ' : Γ ↝ Γ'} →
                      (va : ATInt Γ α) (v : TInt τ) →
                      {env : Env Γ} {env' : Env Γ'} → 
                      Γ↝Γ' ⊢ env ↝ env' → 
                      Equiv env va v →
                      Equiv env' (int↑ α Γ↝Γ' va) v
     lem-lift-equiv va v {.env'} {env'} (refl .env') eq = lem-lift-refl-id env' v va eq 
     lem-lift-equiv {SNum} va v (extend v₁ env↝env') eq = eq
     lem-lift-equiv {SFun α α₁} va v (extend v₁ env↝env') eq =
       λ v₁env₁↝env' eq₁ → eq (env↝trans (extend v₁ env↝env') v₁env₁↝env') eq₁
     lem-lift-equiv {D x} va v (extend v₁ env↝env') eq
       rewrite sym eq = sym (lem-elevate-≡ (refl (extend v₁ env↝env')) va)

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
         Equiv-Env (x ∷ env') (env↑ (extend refl) aenv) env
     lem-equiv-env-lift-extend _ [] x = []
     lem-equiv-env-lift-extend env' (cons {α} eqenv va v x) x₁ =
       cons (lem-equiv-env-lift-extend env' eqenv x₁)
            (int↑ α (extend refl) va) v (lem-lift-equiv va v (extend x₁ (refl env')) x)

     lem-equiv-env-lift-lift :
       ∀ {Γ' Γ'' Δ} → let Γ = stripΔ Δ in
         {Γ↝Γ' : Γ' ↝ Γ''}
         {env' : Env Γ'} {env'' : Env Γ''}
         (env'↝env'' : Γ↝Γ' ⊢ env' ↝ env'') →
         {env : Env Γ} {aenv : AEnv Γ' Δ} →
         Equiv-Env env' aenv env → 
         Equiv-Env env'' (env↑ Γ↝Γ' aenv) env
     lem-equiv-env-lift-lift env'↝env'' [] = []
     lem-equiv-env-lift-lift {Γ↝Γ' = Γ↝Γ'} env'↝env'' (cons {α} eqenv va v x)
       with lem-equiv-env-lift-lift env'↝env'' eqenv
     ... | IA = cons IA (int↑ α Γ↝Γ' va) v (lem-lift-equiv va v env'↝env'' x)
    

  ----------------------------------------
  --module "Proof"
  --note: the proof of correctness of [pe]
  ---------------------------------------- 
  module Proof where
    open Equiv
    open Equiv-Elevate
   
    pe-correct : ∀ { α Δ Γ' } → (e : AExp Δ α) →
                 let Γ = stripΔ Δ in 
                 {aenv : AEnv Γ' Δ} → {env : Env Γ} → 
                 (env' : Env Γ') →
                 Equiv-Env env' aenv env → 
                 Equiv env' (pe e aenv) (ev (strip e) env)
    pe-correct (Var x) env' eqenv = lem-equiv-lookup env' eqenv x
    pe-correct (SCst x) env' eqenv = refl
    pe-correct (SAdd e f) env' eqenv
      rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    pe-correct (SLam e) env' eqenv =
      λ {_} {env''} env'↝env'' {av'} {v'} eq →
        let eqenv' = (lem-equiv-env-lift-lift env'↝env'' eqenv)
            eqenv'' = (cons eqenv' av' v' eq)
        in pe-correct e env'' eqenv''
    pe-correct (SApp e f) env' eqenv
      with pe-correct e env' eqenv | pe-correct f env' eqenv
    ... | IAe | IAf = IAe (refl env') IAf
    pe-correct (DCst x) env' eqenv = refl
    pe-correct (DAdd e f) env' eqenv 
      rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    pe-correct (DLam e) env' eqenv =
      ext (λ x → let eqenv' = (lem-equiv-env-lift-extend env' eqenv x)
                     eqenv'' = (cons eqenv' (EVar hd) x refl)
                 in pe-correct e (x ∷ env') eqenv'')
    pe-correct (DApp e f) {env = env} env' eqenv
      with pe-correct f env' eqenv | pe-correct e env' eqenv 
    ... | IA' | IA = cong₂ (λ f x → f x) IA IA'
    pe-correct (Lift e) env' eqenv
      with pe-correct e env' eqenv
    ... | IA = IA




