{- Correctness of the partial evaluator.
    ev ∘ pe ≡ ev ∘ residualize -}
module Correctness where
open import Lib
open import Base
open import TwoLevel
open import CtxExtension
open import Data.Empty


residualize : ∀ {α Δ} → AExp Δ α → Exp (map erase Δ) (erase α)
residualize (Var x) = EVar (mapIdx erase  x)
residualize (SCst x) = ECst x
residualize (SSuc e) = ESuc (residualize e)
residualize (SIt e e₀ e₁) = EIt (residualize e) (residualize e₀) (residualize e₁)
--static recursor
residualize (SRec v u n) = ERec (residualize v) (residualize u) (residualize n)
residualize (SAdd e e₁) = EAdd (residualize e) (residualize e₁)
residualize (SLam e) = ELam (residualize e)
residualize (SApp e e₁)  = EApp (residualize e) (residualize e₁)
residualize (DCst x)  = ECst x
residualize (DSuc e) = ESuc (residualize e)
residualize (DIt e e₀ e₁) = EIt (residualize e) (residualize e₀) (residualize e₁)
--dynamic recursor
residualize (DRec v u n) = ERec (residualize v) (residualize u) (residualize n)
residualize (DAdd e e₁) = EAdd (residualize e) (residualize e₁)
residualize (DLam e)  = ELam (residualize e)
residualize (DApp e e₁)  = EApp (residualize e) (residualize e₁)
residualize (SPair e e₁)  = EPair (residualize e)  (residualize e₁)
residualize (SInl e)  = EInl (residualize e)
residualize (SInr e)  = EInr (residualize e)
residualize (SFst e)  = EFst (residualize e)
residualize (SSnd e)  = ESnd (residualize e)
residualize (SCase e e₁ e₂)  = ECase (residualize e) (residualize e₁) (residualize e₂)
residualize (DPair e e₁)  = EPair (residualize e) (residualize e₁)
residualize (DInl e)  = EInl (residualize e)
residualize (DInr e)  = EInr (residualize e)
residualize (DFst e)  = EFst (residualize e)
residualize (DSnd e)  = ESnd (residualize e)
residualize (DCase e e₁ e₂)  = ECase (residualize e) (residualize e₁) (residualize e₂)
residualize (Lift lftbl e) = residualize e

-- Extending a value environment according to an extension of a
-- type environment

data _⊢_↝_ :
  ∀ {Γ Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
  refl : ∀ {Γ} {ρ : Env Γ} → refl ⊢ ρ ↝ ρ
  extend : ∀ {τ Γ Γ' ρ ρ'} → {Γ↝Γ' : Γ ↝ Γ'} →
             (v : TInt τ) → Γ↝Γ' ⊢ ρ ↝ ρ' →
             extend Γ↝Γ' ⊢ ρ ↝ (v ∷ ρ')
_⊕ρ_ : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
  {ρ ρ' ρ''} → 
  Γ↝Γ' ⊢ ρ ↝ ρ' → Γ'↝Γ'' ⊢ ρ' ↝ ρ'' →
  let Γ↝Γ'' = Γ↝Γ' ⊕ Γ'↝Γ'' in
  Γ↝Γ'' ⊢ ρ ↝ ρ'' 
_⊕ρ_ ρ↝ρ' (refl) = ρ↝ρ'
_⊕ρ_ ρ↝ρ' (extend v ρ'↝ρ'') = extend v (ρ↝ρ' ⊕ρ ρ'↝ρ'')

-- Equivalent Imp Γ α and EImp τ values (where τ = sinj₂ipα α). As
-- (v : Imp Γ α) is not necessarily closed, equivalence is defined for
-- the closure (Env Γ, ImpΓ α)
postulate ext : ∀ {τ₁ τ₂} {f g : TInt τ₁ → TInt τ₂} →
                (∀ x → f x ≡ g x) → f ≡ g
Equiv : ∀ {α Γ} →
  (ρ : Env Γ) → (vₐ : ATInt Γ α) → (v : TInt (erase α)) → Set
Equiv {SNum} ρ nₐ n = nₐ ≡ n 
Equiv {D x} ρ e v = ev e ρ ≡ v
Equiv {SFun α₁ α₂} {Γ} ρ fₐ f =
  ∀ {Γ' ρ' Γ↝Γ'} → (Γ↝Γ' ⊢ ρ ↝ ρ') →
     {xₐ : ATInt Γ' α₁} → {x : TInt (erase α₁)} →
     Equiv ρ' xₐ x → Equiv ρ' (fₐ Γ↝Γ' xₐ) (f x)
Equiv {SPrd α α₁} ρ (proj₁ , proj₂) (proj₁' , proj₂') =
  Equiv ρ proj₁ proj₁' × Equiv ρ proj₂ proj₂' 
Equiv {SSum α α₁} ρ (inj₁ a) (inj₁ a₁) = Equiv ρ a a₁
Equiv {SSum α α₁} ρ (inj₂ b) (inj₂ b₁) = Equiv ρ b b₁ 
Equiv {SSum α α₁} ρ (inj₁ a) (inj₂ b) = ⊥  
Equiv {SSum α α₁} ρ (inj₂ b) (inj₁ a) = ⊥  


-- Equivalence of AEnv and Env environments. They need to provide
-- Equivalent bindings for a context Δ/sinj₂ipΔ Δ. Again, the
-- equivalence is defined for a closure (Env Γ', AEnv Γ' Δ).
data Env-Equiv {Γ' : _} (ρ : Env Γ') :
  ∀ {Δ} → (ρ' : AEnv Γ' Δ) → (ρ'' : Env (map erase Δ))
  → Set where
-- ...
  [] : Env-Equiv ρ [] []
  cons : ∀ {α Δ} → let τ = erase α
                       Γ = map erase Δ in
          {ρ'' : Env Γ} → {ρ' : AEnv Γ' Δ} → 
          Env-Equiv ρ ρ' ρ'' →
          (va : ATInt Γ' α) → (v : TInt τ) → 
          Equiv ρ va v → 
              Env-Equiv ρ (va ∷ ρ') (v ∷ ρ'')

-- Ternary helper relation for environment extensions, analogous to _↝_↝_ for contexts
data _⊢_↝_↝_⊣ : ∀ { Γ Γ' Γ''} → Γ ↝ Γ' ↝ Γ'' → Env Γ → Env Γ' → Env Γ'' → Set where
  refl : ∀ {Γ Γ''} {Γ↝Γ'' : Γ ↝ Γ''} { ρ ρ'' } →
         Γ↝Γ'' ⊢ ρ ↝ ρ'' →
         refl Γ↝Γ'' ⊢ ρ ↝ [] ↝ ρ'' ⊣
  extend : ∀ {Γ Γ' Γ'' τ} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''} { ρ ρ' ρ'' } →
           Γ↝Γ'↝Γ'' ⊢ ρ ↝ ρ' ↝ ρ'' ⊣ →
           (v : TInt τ) → extend Γ↝Γ'↝Γ'' ⊢ (v ∷ ρ) ↝ (v ∷ ρ') ↝ (v ∷ ρ'') ⊣

-- the following lemmas are sinj₂ong versions of the shifting
-- functions, proving that consistent variable renaming preserves
-- equivalence (and not just typing).
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




int↑-equiv : ∀ {α Γ Γ'} → 
                 {Γ↝Γ' : Γ ↝ Γ'} →
                 (va : ATInt Γ α) (v : TInt (erase α)) →
                 {ρ : Env Γ} {ρ' : Env Γ'} → 
                 Γ↝Γ' ⊢ ρ ↝ ρ' → 
                 Equiv ρ va v →
                 Equiv ρ' (int↑ Γ↝Γ' va) v
int↑-equiv va v {.ρ'} {ρ'} (refl) eq = eq 
int↑-equiv {SNum} va v (extend v₁ ρ↝ρ') eq = eq
int↑-equiv {SFun α α₁} va v (extend v₁ ρ↝ρ') eq = 
  λ v₁ρ₁↝ρ' eq₁ → eq ((extend v₁ ρ↝ρ') ⊕ρ v₁ρ₁↝ρ') eq₁
int↑-equiv {D x} va v (extend {ρ' = ρ'} {Γ↝Γ' = Γ↝Γ'} v₁ ρ↝ρ') eq
  rewrite sym (elevate-≡ (refl (extend {ρ' = ρ'} v₁ refl)) (int↑ Γ↝Γ' va)) | int↑-equiv va v ρ↝ρ' eq
    = refl 
int↑-equiv {SPrd α α₁} (ffst , ssnd) (ffst₁ , ssnd₁) (extend v₁ ρ↝ρ') (x , x₁) =
  (int↑-equiv {α} ffst ffst₁ (extend v₁ ρ↝ρ') x) , (int↑-equiv {α₁} ssnd ssnd₁ (extend v₁ ρ↝ρ') x₁)
int↑-equiv {SSum α α₁} (inj₁ a) (inj₁ a₁) (extend v₁ ρ↝ρ') eq = int↑-equiv  a a₁ (extend v₁ ρ↝ρ') eq
int↑-equiv {SSum α α₁} (inj₂ b) (inj₂ b₁) (extend v₁ ρ↝ρ') eq = int↑-equiv  b b₁ (extend v₁ ρ↝ρ') eq
int↑-equiv {SSum α α₁} (inj₁ a) (inj₂ b) (extend v₁ ρ↝ρ') () 
int↑-equiv {SSum α α₁} (inj₂ b) (inj₁ a) (extend v₁ ρ↝ρ') ()

lookup-equiv : ∀ {α Δ Γ'} → let Γ = map erase Δ in
                   { aρ : AEnv Γ' Δ } {ρ : Env Γ} →
                   (ρ' : Env Γ') →
                   Env-Equiv ρ' aρ ρ →
                   ∀ x → Equiv {α} ρ' (lookup x aρ ) (lookupE (mapIdx erase x) ρ)
lookup-equiv ρ' [] ()
lookup-equiv ρ' (cons  ρeq va v eq) hd = eq
lookup-equiv ρ' (cons  ρeq va v eq) (tl x) = lookup-equiv ρ' ρeq x

env↑-equiv-extend :
  ∀ {σ Γ' Δ} (ρ' : Env Γ') → let Γ = map erase Δ in
    {ρ : Env Γ} {aρ : AEnv Γ' Δ} →
    Env-Equiv ρ' aρ ρ → (x : TInt σ) →
    Env-Equiv (x ∷ ρ') (env↑ (extend refl) aρ) ρ
env↑-equiv-extend _ [] x = []
env↑-equiv-extend ρ' (cons {α} eqρ va v x) x₁ =
  cons (env↑-equiv-extend ρ' eqρ x₁)
       (int↑ (extend refl) va) v (int↑-equiv va v (extend x₁ (refl)) x)

env↑-equiv :
  ∀ {Γ' Γ'' Δ} → let Γ = map erase Δ in
    {Γ↝Γ' : Γ' ↝ Γ''}
    {ρ' : Env Γ'} {ρ'' : Env Γ''}
    (ρ'↝ρ'' : Γ↝Γ' ⊢ ρ' ↝ ρ'') →
    {ρ : Env Γ} {aρ : AEnv Γ' Δ} →
    Env-Equiv ρ' aρ ρ → 
    Env-Equiv ρ'' (env↑ Γ↝Γ' aρ) ρ
env↑-equiv ρ'↝ρ'' [] = []
env↑-equiv {Γ↝Γ' = Γ↝Γ'} ρ'↝ρ'' (cons eqρ va v x)
  with env↑-equiv ρ'↝ρ'' eqρ
... | IA = cons IA (int↑ Γ↝Γ' va) v (int↑-equiv va v ρ'↝ρ'' x)


mutual 
  lift-correct : ∀ {Γ α} (lft : Liftable α) (env : Env Γ) (av : ATInt Γ α) (v : TInt (erase α)) →  
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

  embed-correct : ∀ {Γ α} (lft : Liftable⁻ α) (env : Env Γ) →  (e : Exp Γ (erase α)) → (v : TInt (erase α)) → 
                  ev e env  ≡ v → Equiv env (embed lft e) v
  embed-correct (D τ) env e v eq rewrite eq = refl
  embed-correct (SPrd lft lft₁) env e (fstv , sndv) eq  =
    (embed-correct lft env (EFst e) fstv (subst (λ x → proj₁ x ≡ fstv) (sym eq) refl)) , (embed-correct lft₁ env (ESnd e) sndv (subst (λ x → proj₂ x ≡ sndv) (sym eq) refl))
  embed-correct {α = SFun α₁ α₂} (SFun x lft) env e v eq = f
    where 
          f : ∀ {Γ' env' Γ↝Γ'} (x₁ : Γ↝Γ' ⊢ env ↝ env') {x₂ : ATInt Γ' α₁} {x₃ : TInt (erase α₁)}
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

natit-correct :
          ∀ {Δ} → 
          (n : _) →
          (Γ' : List Type)
          (ρ' : AEnv Γ' Δ) (ρ'' : Env (map erase Δ))
          (α : _)
          (e₀ : AExp Δ α) (e₁ : AExp Δ (SFun α α))
          (env'  : Env Γ')
          (IA₀ : Equiv env' (pe e₀ ρ') (ev (residualize e₀) ρ'')) →
          (IA₁ : {Γ₁' : List Type} {ρ₁' : Env Γ₁'} {Γ↝Γ' : Γ' ↝ Γ₁'} →
                 Γ↝Γ' ⊢ env' ↝ ρ₁' →
                 {xₐ : ATInt Γ₁' α}
                 {x : TInt (erase α)} →
                 Equiv ρ₁' xₐ x →
                 Equiv ρ₁' (pe e₁ ρ' Γ↝Γ' xₐ) (ev (residualize e₁) ρ'' x)) →
          Equiv env'
          (natit n (pe e₀ ρ') (pe e₁ ρ' refl))
          (natit n (ev (residualize e₀) ρ'') (ev (residualize e₁) ρ''))
natit-correct zero Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ = IA₀
natit-correct (suc n) Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
  with natit-correct n Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
... | IA = IA₁ refl IA



natrec-correct :
          ∀ {Δ} → 
          (n : _) →
          (Γ' : List Type)
          (ρ' : AEnv Γ' Δ) (ρ'' : Env (map erase Δ))
          (α : _)
          (e₀ : AExp Δ α) (e₁ : AExp Δ (SFun SNum (SFun α α)))
          (env'  : Env Γ')
          (IA₀ : Equiv env' (pe e₀ ρ') (ev (residualize e₀) ρ'')) →
          (IA₁ : {m₁ : _} → {m₂ : _} → m₁ ≡ m₂ → 
                 {Γ₁' : List Type} {ρ₁' : Env Γ₁'} {Γ↝Γ' : Γ' ↝ Γ₁'} →
                 Γ↝Γ' ⊢ env' ↝ ρ₁' →
                 {xₐ : ATInt Γ₁' α}
                 {x : TInt (erase α)} →
                 Equiv ρ₁' xₐ x →
                 Equiv ρ₁' (pe e₁ ρ' Γ↝Γ' m₁ refl xₐ) (ev (residualize e₁) ρ'' m₂  x)) →
          Equiv env'
          (natrec n (pe e₀ ρ') (λ n₁ → pe {Γ'} e₁ ρ' {Γ'} refl n₁ {Γ'} refl))
          (natrec n (ev (residualize e₀) ρ'') (ev (residualize e₁) ρ''))
natrec-correct zero Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ =  IA₀
natrec-correct (suc n) Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
  with natrec-correct n Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
... | IA = IA₁ refl refl IA



pe-correct : ∀ { α Δ Γ' } →
  (e : AExp Δ α) →
  (ρ : Env Γ') →
  {ρ' : AEnv Γ' Δ} → {ρ'' : Env (map erase Δ)} → 
  Env-Equiv ρ ρ' ρ'' → 
  Equiv ρ (pe e ρ') (ev (residualize e) ρ'')
pe-correct (Var x) env' eqenv = lookup-equiv env' eqenv x
pe-correct (SCst x) env' eqenv = refl
pe-correct (SSuc e) env' eqenv rewrite pe-correct e env' eqenv = refl
pe-correct {Δ = Δ} {Γ' = Γ'} (SIt {α} e e₀ e₁) env' {ρ'} {ρ''} eqenv
  with pe-correct e env' eqenv | pe-correct e₀ env' eqenv | pe-correct e₁ env' eqenv
... | IA | IA₀ | IA₁ rewrite IA = natit-correct (ev (residualize e) ρ'') Γ' ρ' ρ'' α e₀ e₁ env' IA₀
                                    IA₁
pe-correct {Δ = Δ} {Γ' = Γ'} (SRec {α} v u n) env' {ρ'} {ρ''} eqenv 
  with pe-correct n env' eqenv | pe-correct v env' eqenv | pe-correct u env' eqenv 
... | IN | IV | IU rewrite IN = natrec-correct (ev (residualize n) ρ'') Γ' ρ' ρ'' α v u env' IV 
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
pe-correct (SFst e) env' {ρ' = aenv} {ρ'' = env} eqenv with pe e aenv | ev (residualize e) env | pe-correct e env' eqenv
... | e₁ , e₂ | e₁' , e₂' |  A , B = A
pe-correct (SSnd e) env' {aenv} {env} eqenv with pe e aenv | ev (residualize e) env | pe-correct e env' eqenv
... | e₁ , e₂ | e₁' , e₂' | A , B = B
pe-correct {α} (SCase e e₁ e₂) env' {aenv} {env} eqenv with pe e aenv | ev (residualize e) env | pe-correct e env' eqenv
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
pe-correct (DCase e e₁ e₂) env' {aenv} {env} eqenv with ev (pe e aenv) env' | ev (residualize e) env | pe-correct e env' eqenv
... | inj₁ .c' | inj₁ c' | refl = pe-correct e₁ (c' ∷ env') (cons (env↑-equiv (extend c' (refl)) eqenv) (EVar hd) c' refl)
... | inj₂ .c' | inj₂ c' | refl = pe-correct e₂ (c' ∷ env')
                                    (cons (env↑-equiv (extend c' (refl)) eqenv) (EVar hd) c' refl)
... | inj₁ c | inj₂ c' | ()  
... | inj₂ c | inj₁ c' | ()
pe-correct (Lift x e) env' {aenv} {env} eqenv  
  with pe-correct e env' eqenv 
... | IA = lift-correct x env' (pe e aenv) (ev (residualize e) env) IA 


pe-correct-dyn :
  ∀ { τ } → (e : AExp [] (D τ)) →
  ev (pe e []) [] ≡ (ev (residualize e) [])
pe-correct-dyn e = pe-correct e [] []

