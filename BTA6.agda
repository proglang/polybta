-------------------------------------------------------------
--correctness proof of partial evaluation with liftable terms
------------------------------------------------------------- 
module BTA6 where

open import BTA5
open import Lib 
open Auxiliaries
open TwoLevelTypes-Simp-PS
open TwoLevelTerms-Simp-PS


----------------------------------------------
--module "EvaBase"
--note: it includes
--a)base type interpreter [TInt];
--b)environment [Env] for base type variables;
--c)lookup function [lookupE];
--d)evaluator for base type terms [ev].
----------------------------------------------
module EvaBase where

  TInt : Type → Set
  TInt Num = ℕ
  TInt (Fun ty ty₁) = TInt ty → TInt ty₁
  TInt (Prd ty ty₁) = TInt ty × TInt ty₁
  TInt (Sum ty ty₁) = TInt ty ⊎ TInt ty₁



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
  ev (EInl e) env = inj₁ (ev e env)
  ev (EInr e) env = inj₂ (ev e env)
  ev (EFst e) env = proj₁ (ev e env)
  ev (ESnd e) env = proj₂ (ev e env)
  ev (ECase e e₁ e₂) env with ev e env
  ev (ECase e e₁ e₂) env | inj₁ c  = (λ x → ev e₁ (x ∷ env)) c
  ev (ECase e e₁ e₂) env | inj₂ c  = (λ x → ev e₂ (x ∷ env)) c


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
                  Γ↝Γ' ⊢ env ↝ env' → Γ'↝Γ'' ⊢ env' ↝ env'' →
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
    Equiv {SFun α₁ α₂} {Γ} env av v = ∀ {Γ' env' Γ↝Γ'} →
                                        (Γ↝Γ' ⊢ env ↝ env') →
                                        {av' : ATInt Γ' α₁} →
                                        {v' : TInt (stripα α₁)} →
                                        Equiv env' av' v' → Equiv env' (av Γ↝Γ' av') (v v')
    Equiv {D x} env av v = ev av env ≡ v
    Equiv {SPrd α α₁} env (ffst , ssnd) (ffst₁ , ssnd₁) = (Equiv {α} env ffst ffst₁) × (Equiv {α₁} env ssnd ssnd₁)
    Equiv {SSum α α₁} env (inj₁ a) (inj₁ a₁) = Equiv {α} env a a₁
    Equiv {SSum α α₁} env (inj₁ a) (inj₂ b) = ⊥ 
    Equiv {SSum α α₁} env (inj₂ b) (inj₁ a) = ⊥ 
    Equiv {SSum α α₁} env (inj₂ b) (inj₂ b₁) = Equiv {α₁} env b b₁ 

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
    ... | IA  = cong (λ x → inj₁ x) IA
    lem-elevate-≡ env↝env' (EInr e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → inj₂ x) IA
    lem-elevate-≡ env↝env' (EFst e) with lem-elevate-≡ env↝env' e 
    ... | IA  = cong (λ x → proj₁ x) IA
    lem-elevate-≡ env↝env' (ESnd e) with lem-elevate-≡ env↝env' e
    ... | IA  = cong (λ x → proj₂ x) IA
    lem-elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''} 
                  {env = env}
                  {env'' = env''}
                  env↝env' (ECase e e₁ e₂) with ev e env | ev (elevate Γ↝Γ'↝Γ'' e) env'' | lem-elevate-≡ env↝env' e
    ... | inj₁ c | inj₁ c' | IA rewrite (→tl {x' = c} {y' = c'} (inj₁ c) (inj₁ c') IA refl refl) = lem-elevate-≡-body c'
         where lem-elevate-≡-body : ∀ x → ev e₁ (x ∷ env) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e₁) (x ∷ env'')
               lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e₁
    ... | inj₁ c | inj₂ c' | ()
    ... | inj₂ c | inj₁ c' | ()
    ... | inj₂ c | inj₂ c' | IA rewrite (→tr {x' = c} {y' = c'} (inj₂ c) (inj₂ c') IA refl refl) = lem-elevate-≡-body c'
         where lem-elevate-≡-body : ∀ x → ev e₂ (x ∷ env) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e₂) (x ∷ env'')
               lem-elevate-≡-body x = lem-elevate-≡ (extend env↝env' x) e₂

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
    
    lem-lift-refl-id {D x} env v va eq rewrite sym eq = sym (lem-elevate-≡ (refl (refl env)) va)
    lem-lift-refl-id {SPrd α α₁} env (ffst , ssnd) (ffst₁ , ssnd₁) (x , x₁) = (lem-lift-refl-id {α} env ffst ffst₁ x) , 
                                                                             (lem-lift-refl-id {α₁} env ssnd ssnd₁ x₁)
    lem-lift-refl-id {SSum α α₁} env (inj₁ a) (inj₁ a₁) eq = lem-lift-refl-id  env a a₁ eq
    lem-lift-refl-id {SSum α α₁} env (inj₁ a) (inj₂ b) ()
    lem-lift-refl-id {SSum α α₁} env (inj₂ b) (inj₁ a) () 
    lem-lift-refl-id {SSum α α₁} env (inj₂ b) (inj₂ b₁) eq = lem-lift-refl-id  env b b₁ eq


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
    lem-lift-equiv {D x} va v (extend v₁ env↝env') eq rewrite sym eq = sym (lem-elevate-≡ (refl (extend v₁ env↝env')) va)
    lem-lift-equiv {SPrd α α₁} (ffst , ssnd) (ffst₁ , ssnd₁) (extend v₁ env↝env') (x , x₁) =
         (lem-lift-equiv {α} ffst ffst₁ (extend v₁ env↝env') x) , (lem-lift-equiv {α₁} ssnd ssnd₁ (extend v₁ env↝env') x₁)
    lem-lift-equiv {SSum α α₁} (inj₁ a) (inj₁ a₁) (extend v₁ env↝env') eq = lem-lift-equiv  a a₁ (extend v₁ env↝env') eq
    lem-lift-equiv {SSum α α₁} (inj₁ a) (inj₂ b) (extend v₁ env↝env') () 
    lem-lift-equiv {SSum α α₁} (inj₂ b) (inj₁ a) (extend v₁ env↝env') ()
    lem-lift-equiv {SSum α α₁} (inj₂ b) (inj₂ b₁) (extend v₁ env↝env') eq = lem-lift-equiv  b b₁ (extend v₁ env↝env') eq


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

   
    --------------------------------
    --"lift-correct" equivalence lemma
    --------------------------------
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
               (av (extend refl) (embed x (EVar hd))) (v x₁) (eq (extend x₁ (refl env)) (embed-correct x (x₁ ∷ env) (EVar hd) x₁ refl)))
 
      embed-correct : ∀ {Γ α} (lft : Liftable⁻ α) (env : Env Γ) →  (e : Exp Γ (typeof α)) → (v : TInt (typeof α)) → 
                      ev e env  ≡ v → Equiv env (embed lft e) v
      embed-correct (D τ) env e v eq rewrite eq = refl
      embed-correct (SPrd lft lft₁) env e (fstv , sndv) eq  = (embed-correct lft env (EFst e) fstv (subst (λ x → proj₁ x ≡ fstv) (sym eq) refl)) 
                                                               ,    (embed-correct lft₁ env (ESnd e) sndv
                                                                      (subst (λ x → proj₂ x ≡ sndv) (sym eq) refl))
      embed-correct {α = SFun α₁ α₂} (SFun x lft) env e v eq = f
        where 

              f : ∀ {Γ' env' Γ↝Γ'} (x₁ : Γ↝Γ' ⊢ env ↝ env') {x₂ : ATInt Γ' α₁} {x₃ : TInt (typeof α₁)}
                    (x₄ : Equiv env' x₂ x₃) →
                    Equiv env'
                    (embed lft (EApp (elevate (refl Γ↝Γ') e) (lift x x₂))) (v x₃)
              f {Γ'} {env'} {Γext} envext {av'} {v'} eq' = 
                                                            embed-correct lft env' (EApp (elevate (refl Γext) e) (lift x av')) (v v') 
                                                               g
                where g : ev (elevate (refl Γext) e) env' (ev (lift x av') env') ≡ v v'
                      g rewrite lift-correct x env' av' v' eq'  
                              | sym (cong (λ f → f v') (lem-elevate-≡ (refl envext) e)) 
                              |  (cong (λ f → f v') eq) = refl
  
 
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
    pe-correct (SPair e e₁) env' eqenv = (pe-correct e env' eqenv) , (pe-correct e₁ env' eqenv)
    pe-correct (SInl e) env' eqenv = pe-correct e env' eqenv
    pe-correct (SInr e) env' eqenv = pe-correct e env' eqenv
    pe-correct (SFst (SPair e e₁)) env' eqenv = pe-correct e env' eqenv
    pe-correct (SFst e) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' | A , B = A
    pe-correct (SSnd (SPair e e₁)) env' eqenv = pe-correct e₁ env' eqenv
    pe-correct (SSnd e) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | e₁ , e₂ | e₁' , e₂' | A , B = B
    pe-correct {α} (SCase e e₁ e₂) {aenv = aenv} {env = env} env' eqenv with pe e aenv | ev (strip e) env | pe-correct e env' eqenv
    ... | inj₁ c | inj₁ c' | L = pe-correct e₁ {aenv =  c ∷ (env↑ refl aenv)}
                               {env = c' ∷ env} env'
                               (cons (lem-equiv-env-lift-lift (refl env') eqenv) c c' L)
    ... | inj₂ c | inj₂ c' | R = pe-correct e₂ {aenv = c ∷ (env↑ refl aenv)}
                               {env = c' ∷ env} env'
                               (cons (lem-equiv-env-lift-lift (refl env') eqenv) c c' R)
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
    pe-correct (DCase e e₁ e₂) {aenv = aenv} {env = env} env' eqenv with ev (pe e aenv) env' | ev (strip e) env | pe-correct e env' eqenv
    ... | inj₁ c | inj₁ c' | IA rewrite (→tl {x' = c} {y' = c'} (inj₁ c) (inj₁ c') IA refl refl) = 
      pe-correct e₁
          {aenv = (EVar hd) ∷ (env↑ (extend refl) aenv)}
          {env = c' ∷ env} (c' ∷ env') (cons (lem-equiv-env-lift-lift (extend c' (refl env')) eqenv) (EVar hd) c' refl)
    ... | inj₂ c | inj₂ c' | IA rewrite (→tr {x' = c} {y' = c'} (inj₂ c) (inj₂ c') IA refl refl) = 
      pe-correct e₂
        {aenv = (EVar hd) ∷ (env↑ (extend refl) aenv)}
        {env = c' ∷ env} (c' ∷ env')
        (cons (lem-equiv-env-lift-lift (extend c' (refl env')) eqenv)
         (EVar hd) c' refl)
    ... | inj₁ c | inj₂ c' | ()  
    ... | inj₂ c | inj₁ c' | ()
    pe-correct (↑ x e) {aenv = aenv} {env = env} env' eqenv  
      with pe-correct e env' eqenv 
    ... | IA = lift-correct x env' (pe e aenv) (ev (strip e) env) IA


    