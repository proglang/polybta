module PE-STLCfix-correctness where
open import PE-STLCfix
open import Lib
open Auxiliaries
open import Data.Maybe
open import Data.Empty

------------------
--some auxiliaries
------------------
stripα : AType → Type
stripα (D x) = x
stripα (SFun aty aty₁) = Fun (stripα aty) (stripα aty₁)
stripα SNum = Num

stripΔ : ACtx → Ctx
stripΔ = map stripα

strip-lookup : ∀ { α Δ} → α ∈ Δ → stripα α ∈ stripΔ Δ
strip-lookup hd = hd
strip-lookup (tl x) = tl (strip-lookup x)

-------------------------------------------------------
--[_⊢_↝_] Extending a base value environment according 
--to an extension of the corresponding type environment
-------------------------------------------------------
data _⊢_↝_ {Γ} : ∀ {Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
  refl   : ∀ env → refl ⊢ env ↝ env
  extend : ∀ {τ Γ' env env'} →  {Γ↝Γ' : Γ ↝ Γ'}   →
             (v : Maybe (Int τ)) → (Γ↝Γ' ⊢  env ↝ env')   →
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
env↝trans env'↝env'' (refl _) = env'↝env''
env↝trans env'↝env'' (extend v env↝env') = extend v (env↝trans env'↝env'' env↝env')


----------------------------------------------------------
--[_⊢_↝_↝_⊣] similar to [_⊢_↝_], extension from the middle
---------------------------------------------------------- 
data _⊢_↝_↝_⊣ : ∀ { Γ Γ' Γ''} → Γ ↝ Γ' ↝ Γ'' → Env Γ → Env Γ' → Env Γ'' → Set where
  refl : ∀ {Γ Γ''} {Γ↝Γ'' : Γ ↝ Γ''} { env env'' } →
           Γ↝Γ'' ⊢ env ↝ env'' →
           refl Γ↝Γ'' ⊢ env ↝ [] ↝ env'' ⊣
  extend : ∀ {Γ Γ' Γ'' τ} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''} { env env' env'' } →
             Γ↝Γ'↝Γ'' ⊢ env ↝ env' ↝ env'' ⊣ →
             (v : Maybe (Int τ)) → extend Γ↝Γ'↝Γ'' ⊢ (v ∷ env) ↝ (v ∷ env') ↝ (v ∷ env'') ⊣


-----------------------------------------------------
--equivalence relation between two evaluation results
-----------------------------------------------------
    -- Equiv : ∀ {α Γ} → Env Γ → ATInt Γ α → TInt (stripα α) → Set 
    -- Equiv {SNum} env av v = av ≡ v
    -- Equiv {SFun α₁ α₂} {Γ} env af f = 
    --     ∀ {Γ' env' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ env') →
    --     {ax : ATInt Γ' α₁} → {x : TInt (stripα α₁)} →
    --     Equiv env' ax x → Equiv env' (af Γ↝Γ' ax) (f x)
    -- Equiv {D x} {Γ} env av v = ev av env ≡ v 


Equiv : ∀ {α Γ} {n : ℕ} → Env Γ → ATInt Γ α  → Maybe (Int (stripα α)) → Set

Equiv {D x} {n = n} env ae e = ev n ae env ≡ e
--note: the result of [pe] of evaluation a dynamic term will always be the same
--      as the "stripped-off" version of the same term, therefore given the same
--      "n" the evaluation reslut of the two terms of [ev] should be the same

--note: an existential quantifier should be used here, considering the case 
--      where the expression under consideration is a static dispatch with dynamic
--      branches, see below case in [pe-correct]

Equiv {SFun α α₁} {Γ} {n} env f f' with f'
... | just f'' = ∀ {Γ' env' Γ↝Γ'} →
                   Γ↝Γ' ⊢ env ↝ env' →
                   {x : ATInt Γ' α} →
                   {x'' : Maybe (Int (stripα α))} →
                   Equiv {α} {Γ'} {n} env' x x'' →
                   Equiv {α₁} {Γ'} {n} env' (f Γ↝Γ' x) (f'' x'')
... | nothing  = 0 ≡ 0 
--note: in case of terms of static types, the choice of "n" matters in that
--      on the one hand *)result of [pe] of evaluating such a term can never
--      be non-sensical, *)the result of [ev] of evaluating its stripped-off
--      counterpart can be "nothing" depending upon the choice of "n".
--      what is interesting to our correctness proof in this case is to ask
--      "whether or not there exists a large enough n such that the result from
--      [ev] is the same as that from [pe]."

--note: currently all cases where non-sensical results are generated by [ev] due
--      a small n are excluded in the correctness-proof by offering "free-lunch" 

          
Equiv {SNum}      env ae e  with e 
... | just e' = just ae ≡ e
... | nothing = 0 ≡ 0 
--note: similar to the above case






                     --note:
                     --a) if we use [⊥] then we have to prove that such cases 
                     --   shall never happen. Perhaps [Pe-Correct] is more
                     --   appropriate
                     --b) if we use [⊤] then we simply ignore such cases 
                     --   ,which seems not to be the right choice. 
                     --note:
                     --   it is intuitively wrong to consider use [⊥] to denote
                     --   cases in [Equiv] where the evaluation of the stripped
                     --   term boils down to [nothing] due to a [n] not big enough  

--note: some intuition regarding the "equivalence relation"
--a)regarding terms of dynamic types
--  it is straight forward to think that for a given n
--  both the LHS,ev of the result of pe and the RHS,
--  ev of the stripped-off term are equal
--b)it is tricky to deal with terms of static types for
--  on the one hand the pe result of the terms should always be
--  values while ev of the stripped-off terms can be "nothing"
--  if our choice of n is not big enough

------------------------------------------------------
--an alternative specification of equivalence relation
------------------------------------------------------
equiv : ∀ {α Γ} → Env Γ → ATInt Γ α  → Maybe (Int (stripα α)) → Set
equiv {D x} env ae e = {n : ℕ} → ev n ae env ≡ e --for the "same n" ev of the stripped-off term
                                                 --equal to ev of the result of the pe
equiv {SFun α α₁} env ae e = {!!}
equiv {SNum} env ae e = {!!}
 

--------------------------------------------------
--[Equiv-Env] equivalence between two environments
-------------------------------------------------- 
data Equiv-Env {Γ' : _} {n : ℕ} (env' : Env Γ') :
     ∀ {Δ} → let Γ = stripΔ Δ in
       AEnv Γ' Δ → Env Γ → Set where
  [] : Equiv-Env env' [] []
  cons : ∀ {α Δ} → let σ = stripα α
                       Γ = stripΔ Δ in
              {env : Env Γ} → {aenv : AEnv Γ' Δ} → 
              Equiv-Env {Γ'} {n} env' aenv env →
              (va : ATInt (Γ') α) → (v : Maybe (Int σ)) → 
              Equiv {α} {Γ'} {n} env' va v → 
              Equiv-Env env' (_∷_ {α = α} va (aenv)) (v ∷ env)

 


---------------------------
--strip off two-level terms
---------------------------
strip : ∀ {α Δ} → AExp Δ α → Exp (stripΔ Δ) (stripα α)
strip (Var x) = Var (strip-lookup x)
strip (SC x) = C x
strip (DC x) = C x
strip (SDspℕ e e₁ e₂) = Dspℕ (strip e) (strip e₁) (strip e₂)
strip (DDspℕ e e₁ e₂) = Dspℕ (strip e) (strip e₁) (strip e₂)
strip (SSuc e) = Suc (strip e)
strip (DSuc e) = Suc (strip e)
strip (SLam α₁ e) = Lam (stripα α₁) (strip e)
strip (DLam σ₁ e) = Lam σ₁ (strip e)
strip (SApp e e₁) = App (strip e) (strip e₁)
strip (DApp e e₁) = App (strip e) (strip e₁)
strip (SRec e e₁ e₂) = Rec (strip e) (strip e₁) (strip e₂)
--------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------
-- strip {α} {Δ} (SRec e e₁ e₂) =  App (App (App 
--                                  (recursor {stripα α} {stripΔ Δ}) (strip e₁)) --function to be recursively applied 
--                                  (strip e₂)) --number of recursive calls
--                                  (strip e)   --default 
-- -- note : in the presence of low level recursor, the introduction of the intermediate term "recursor" is unnecessary
--------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------
strip (DFix e) = Fix (strip e)

--------------------------------------------
--correctness proof of the partial evaluator
--------------------------------------------
    -- pe-correct : ∀ { α Δ Γ' } → (e : AExp Δ α) →
    --              let Γ = stripΔ Δ in 
    --              {aenv : AEnv Γ' Δ} → {env : Env Γ} → 
    --              (env' : Env Γ') →
    --              Equiv-Env env' aenv env → 
    --              Equiv env' (pe e aenv) (ev (strip e) env)
    -- pe-correct (Var x) env' eqenv = lem-equiv-lookup env' eqenv x
    -- pe-correct (SCst x) env' eqenv = refl
    -- pe-correct (SAdd e f) env' eqenv
    --   rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    -- pe-correct (SLam e) env' eqenv =
    --   λ {_} {env''} env'↝env'' {av'} {v'} eq →
    --     let eqenv' = (lem-equiv-env-lift-lift env'↝env'' eqenv)
    --         eqenv'' = (cons eqenv' av' v' eq)
    --     in pe-correct e env'' eqenv''
    -- pe-correct (SApp e f) env' eqenv
    --   with pe-correct e env' eqenv | pe-correct f env' eqenv
    -- ... | IAe | IAf = IAe (refl env') IAf
    -- pe-correct (DCst x) env' eqenv = refl
    -- pe-correct (DAdd e f) env' eqenv 
    --   rewrite pe-correct e env' eqenv | pe-correct f env' eqenv = refl
    -- pe-correct (DLam e) env' eqenv =
    --   ext (λ x → let eqenv' = (lem-equiv-env-lift-extend env' eqenv x)
    --                  eqenv'' = (cons eqenv' (EVar hd) x refl)
    --              in pe-correct e (x ∷ env') eqenv'')
    -- pe-correct (DApp e f) {env = env} env' eqenv
    --   with pe-correct f env' eqenv | pe-correct e env' eqenv 
    -- ... | IA' | IA = cong₂ (λ f x → f x) IA IA'
    -- pe-correct (Lift e) env' eqenv
    --   with pe-correct e env' eqenv
    -- ... | IA = IA

-----------------------
--some auxiliary lemmas
-----------------------
lem-equiv-lookup : ∀ {n α Δ Γ'} → let Γ = stripΔ Δ in
                        { aenv : AEnv Γ' Δ } {env : Env Γ} →
                        (env' : Env Γ') →
                        Equiv-Env {n = n} env' aenv env →
                        ∀ x → Equiv {α} {n = n} env' (Lookup x aenv) (lookup (strip-lookup x) env)
lem-equiv-lookup env' [] ()
lem-equiv-lookup env' (cons  enveq va v eq) hd = eq
lem-equiv-lookup env' (cons  enveq va v eq) (tl x) = lem-equiv-lookup env' enveq x






-----------------------------------------------------------------------------------------
--note: some remarks regarding the following correctness theorem of 
--      the partial evaluator
--1) partial evaluator [pe] of two-level term [e] is considered correct
--   given A.) a two-level environment [aenv] and its corresponding equivalent
--   projection [env] and B.) [n] indicating the upper bound for unfolding the
--   fix-point constructor under base-level evaluation iff
--1.1)the exists an "equivalence relation" between 
--    *)the partial evaluation result of the two level term [e] under environment
--      [aenv] and *)the evaluation result of the corresponding low-level term [strip e]
--      under [env] and [n]
--1.2)the "equivalence relation" is defined similarly to that without fix-point operators 
-----------------------------------------------------------------------------------------
pe-correct : ∀ { α Δ Γ' n} →
            (e : AExp Δ α) →
            (env' : Env Γ') →
            {aenv : AEnv Γ' Δ} → {env : Env (stripΔ Δ)} → 
            Equiv-Env {Γ'} {n} env' aenv env → 
            Equiv {α} {Γ'} {n} env' (pe e aenv) (ev n (strip e) env)
pe-correct {n = n} (Var x) env' eqenv = lem-equiv-lookup {n = n} env' eqenv x
pe-correct (SC x) env' eqenv = refl
pe-correct (DC x) env' eqenv = refl

pe-correct {n = n} (SDspℕ e e₁ e₂) env' {aenv = aenv} {env = env} eqenv 
     with pe-correct {n = n} e env' {aenv = aenv} {env = env} eqenv
pe-correct {n = n} (SDspℕ e e₁ e₂) env' {aenv = aenv} {env = env} eqenv | evd with ev n (strip e) env 
pe-correct (SDspℕ e e₁ e₂) env' eqenv | evd | just x = {!!}  --note: now prove that [pe e aenv ≡ x]
                                                             --      using [evd] in the environment 

pe-correct {D x} (SDspℕ e e₁ e₂) env' eqenv | refl | nothing = {!!} --note: this case examplifies another difficulty
                                                                    --      involved in the correctness proof: if n
                                                                    --      is not big enough then the result from [ev]
                                                                    --      is [nothing] due to [ev n e env'] while on the
                                                                    --      other hand it is possible that n is big enough
                                                                    --      for the evaluation of either [e₁] or [e₂] and 
                                                                    --      as a result the equality can not be established.

pe-correct {SFun α α₁} (SDspℕ e e₁ e₂) env' eqenv | evd | nothing = refl
pe-correct {SNum} (SDspℕ e e₁ e₂) env' eqenv | evd | nothing = refl
                                                            

--  with pe e aenv | ev n (strip e) env 
-- ... | m | just m'  = {!pe-correct {n = n} e env' {aenv = aenv} {env = env} eqenv !} -- prove [m ≡ m'] when [ev n (strip e) env ≡ just m']
-- ... | _ | nothing = {!!}  -- nothing produced due to a small n
--                           -- how can we exclude this case from [pe-correct]


-- with pe e aenv | ev n (strip e) env 
-- pe-correct (SDspℕ e e₁ e₂) env' eqenv | zero | just zero = pe-correct e₁ env' eqenv
-- pe-correct (SDspℕ e e₁ e₂) env' eqenv | zero | just (suc m') = {!!}  --impossible
-- pe-correct (SDspℕ e e₁ e₂) env' eqenv | suc m | just zero = {!!}     --impossible 
-- pe-correct (SDspℕ e e₁ e₂) env' eqenv | suc m | just (suc m') = pe-correct e₂ env' {!!} --note: m = m'
-- ... | _     | nothing = {!!}

pe-correct (DDspℕ e e₁ e₂) env' eqenv = {!!}
pe-correct {n = n} (SSuc e) env' {env = env} eqenv with ev n (strip e) env 
... | just m  = {!pe-correct e env' eqenv!}
... | nothing = {!!} -- note:
                     -- this difficulty lies in the fact that terms of static type when stripped off and
                     -- being evaluated with certain n can result in [nothing] while it is impossible via
                     -- a partial evaluation 
pe-correct (DSuc e) env' eqenv = {!!}
pe-correct (SLam α₁ e) env' eqenv = {!!}
pe-correct (DLam σ₁ e) env' eqenv = {!!}
pe-correct (SApp e e₁) env' eqenv = {!!}
pe-correct (DApp e e₁) env' eqenv = {!!}
pe-correct (SRec e e₁ e₂) env' eqenv = {!!}
-------------------------------------------
-------------------------------------------
pe-correct {n = n} (DFix e) env' {aenv = aenv} {env = env} eqenv with n 
... | 0     = refl
... | suc m with ev m (pe e aenv) env' | ev m (strip e) env 
pe-correct (DFix e) env' eqenv | suc m | just x | just x₁ = {!pe-correct {n = m} e env' eqenv!}
pe-correct (DFix e) env' eqenv | suc m | just x | nothing = {!!}
pe-correct (DFix e) env' eqenv | suc m | nothing | just x = {!!}
pe-correct (DFix e) env' eqenv | suc m | nothing | nothing = refl
--note: the type signature of the goal as follows
--      ev n (Fix (pe e aenv)) env' ≡ ev n (Fix (strip e)) env
--some difficulties involved to construct the corresponding terms
--a)what is the intuition behind the equivalence relation in case
--  of fix-point combinator:
--  a.1)in cases where e is a closed term, [strip e] must be equal
--      to [pe e *] due to both the type of the term is dynamic and
--      it is closed,then the equivalence relation holds;
--  a.2)in cases where e is open and therefore environment comes into
--      play in the evaluation process and then we have to guarantee
--      that the introduction of the terms coming from the environment
--      does not such equivalence relation which is assured by the 
--      equivalence relation between environments, [Equiv-Env env' aenv env].

--b)the relation between [env'] and [env] which seems to be important
--  here is not clear
--c)some concrete examples

----------------------------------------------------
--alternative specification of the correctness lemma
----------------------------------------------------
Pe-Correct : ∀ { α Δ Γ' n} →
            (e : AExp Δ α) →
            (env' : Env Γ') →
            {aenv : AEnv Γ' Δ} → {env : Env (stripΔ Δ)} → 
            Equiv-Env {Γ'} {n} env' aenv env → 
            Σ ℕ (λ m → Equiv {α} {Γ'} {m} env' (pe e aenv) (ev m (strip e) env))
Pe-Correct = {!!}

----------------------------------------------------------------
--yet another alternative specification of the correctness lemma
----------------------------------------------------------------
Pe-correct : ∀ { α Δ Γ' n m} →
            (e : AExp Δ α) →
            (env' : Env Γ') →
            {aenv : AEnv Γ' Δ} → {env : Env (stripΔ Δ)} → 
            Equiv-Env {Γ'} {n} env' aenv env → 
            Equiv {α} {Γ'} {m} env' (pe e aenv) (ev m (strip e) env)
Pe-correct (Var x) env' eqenv = {!!}
Pe-correct (SC x) env' eqenv = {!!}
Pe-correct (DC x) env' eqenv = {!!}
Pe-correct (SDspℕ e e₁ e₂) env' eqenv = {!!}
Pe-correct (DDspℕ e e₁ e₂) env' eqenv = {!!}
Pe-correct (SSuc e) env' eqenv = {!!}
Pe-correct (DSuc e) env' eqenv = {!!}
Pe-correct (SLam α₁ e) env' eqenv = {!!}
Pe-correct (DLam σ₁ e) env' eqenv = {!!}
Pe-correct (SApp e e₁) env' eqenv = {!!}
Pe-correct (DApp e e₁) env' eqenv = {!!}
Pe-correct (SRec e e₁ e₂) env' eqenv = {!!}
Pe-correct {n = n} {m = m} (DFix e) env' eqenv with n 
... | 0      = {!Pe-correct {}!}
... | suc n' = {!!}

-------------------------------------------------------------------
--to deal with the difficulty in specifying an equivalence relation
--of terms of static types the signature of [pe-correct] is changed
--to the following
-------------------------------------------------------------------
PE-CORRECT : ∀ {α Δ Γ' n} →
               (e : AExp Δ α) →
               (env' : Env Γ') → 
               {aenv : AEnv Γ' Δ} → {env : Env (stripΔ Δ)} →
               Equiv-Env {Γ'} {n} env' aenv env → 
               Σ ℕ (λ m → Equiv {α} {Γ'} {m} env' (pe e aenv) (ev m (strip e) env))
PE-CORRECT = {!!} 