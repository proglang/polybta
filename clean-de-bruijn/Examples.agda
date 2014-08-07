module Examples where
open import Lib
open import Base
open import TwoLevel

--application of iterators

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

--application for recursors
--basic operations defined by recursor
-- data _↝_ : List type → List type → Set where
--   ↝-refl   : ∀ {Γ}      → Γ ↝ Γ
--   ↝-extend : ∀ {Γ Γ' τ} → Γ ↝ Γ' → Γ ↝ (τ ∷ Γ')

-- data _↝_↝_ : List type → List type → List type → Set where
--   ↝↝-base   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ'' 
--   ↝↝-extend : ∀ {Γ Γ' Γ'' τ} →
--                  Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'')

-- var↝nat : ∀ {τ Γ Γ'} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
-- var↝nat ↝-refl id = id
-- var↝nat (↝-extend Γ↝Γ') id = var↝nat (↝-extend Γ↝Γ') id  

-- var↝↝nat : ∀ {τ τ' Γ Γ' Γ''} → τ ∈ (τ' ∷ Γ) → Γ ↝ Γ' ↝ Γ'' → τ ∈ (τ' ∷ Γ'')
-- var↝↝nat hd Γ↝Γ'↝Γ'' = hd
-- var↝↝nat (tl id) (↝↝-base x) = tl (var↝nat x id)
-- var↝↝nat (tl id) (↝↝-extend Γ↝Γ'↝Γ'') = tl (var↝↝nat id Γ↝Γ'↝Γ'')

-- ↝↝extend : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → exp Γ τ → exp Γ'' τ
-- ↝↝extend (↝↝-base x) (var x₁) = var (var↝nat x x₁)
-- ↝↝extend (↝↝-extend Γ↝Γ'↝Γ'') (var x) = var (var↝↝nat x Γ↝Γ'↝Γ'')
-- ↝↝extend Γ↝Γ'↝Γ'' z = z
-- ↝↝extend Γ↝Γ'↝Γ'' T = T
-- ↝↝extend Γ↝Γ'↝Γ'' F = F
-- ↝↝extend Γ↝Γ'↝Γ'' (S e) = S (↝↝extend Γ↝Γ'↝Γ'' e)
-- ↝↝extend Γ↝Γ'↝Γ'' (lam e) = lam (↝↝extend (↝↝-extend Γ↝Γ'↝Γ'') e)
-- ↝↝extend Γ↝Γ'↝Γ'' (app e e₁) = app (↝↝extend Γ↝Γ'↝Γ'' e) (↝↝extend Γ↝Γ'↝Γ'' e₁)
-- ↝↝extend Γ↝Γ'↝Γ'' (rec e e₁ e₂) = rec (↝↝extend Γ↝Γ'↝Γ'' e) (↝↝extend Γ↝Γ'↝Γ'' e₁) (↝↝extend Γ↝Γ'↝Γ'' e₂)
-- ↝↝extend Γ↝Γ'↝Γ'' (if e₁ e₂ b) = if (↝↝extend Γ↝Γ'↝Γ'' e₁) (↝↝extend Γ↝Γ'↝Γ'' e₂) (↝↝extend Γ↝Γ'↝Γ'' b)
-- ↝↝extend Γ↝Γ'↝Γ'' (it e f n) = it (↝↝extend Γ↝Γ'↝Γ'' e) (↝↝extend Γ↝Γ'↝Γ'' f) (↝↝extend Γ↝Γ'↝Γ'' n)
-- ↝↝extend Γ↝Γ'↝Γ'' (l , r) = ↝↝extend Γ↝Γ'↝Γ'' l , ↝↝extend Γ↝Γ'↝Γ'' r
-- ↝↝extend Γ↝Γ'↝Γ'' (fst e) = fst (↝↝extend Γ↝Γ'↝Γ'' e)
-- ↝↝extend Γ↝Γ'↝Γ'' (snd e) = snd (↝↝extend Γ↝Γ'↝Γ'' e)
-- ↝nat : ∀ {Γ Γ' τ} → Γ ↝ Γ' → exp Γ τ → exp Γ' τ
-- ↝nat Γ↝Γ' e = ↝↝extend (↝↝-base Γ↝Γ') e 
-- --n + m
-- add : ∀ {Γ} → exp Γ nat → exp Γ nat → exp Γ nat
-- add m n = rec m (lam (lam (S (var hd)))) n
-- --n ∗ m
-- mul : ∀ {Γ} → exp Γ nat → exp Γ nat → exp Γ nat
-- mul {Γ} m n = rec z (lam (lam (add {nat ∷ nat ∷ Γ} (↝nat (↝-extend (↝-extend ↝-refl)) m) (var hd)))) n
-- --mⁿ
-- expo : ∀ {Γ} → exp Γ nat → exp Γ nat → exp Γ nat
-- expo m n = rec (S z) (lam (lam (mul (↝nat (↝-extend (↝-extend ↝-refl)) m) (var hd)))) n 
-- --pre
-- pre : ∀ {Γ} → exp Γ nat → exp Γ nat
-- pre n = rec z (lam (lam (var (tl hd)))) n
-- -- n - m
-- minus : ∀ {Γ} → exp Γ nat → exp Γ nat → exp Γ nat
-- minus m n = rec m (lam (lam (pre (var hd)))) n
-- -- %
-- % : ∀ {Γ} → exp Γ nat → exp Γ nat → exp Γ nat
-- % m n = {!!}
-- --Ackermann's function
-- --note:fixpoint
-- int : ∀ {Γ} → exp Γ (fun nat nat) → exp Γ (fun nat nat)
-- int f = lam (rec (S z) (lam (lam (app (↝↝extend (↝↝-base (↝-extend (↝-extend (↝-extend ↝-refl)))) f) (var hd)))) (var hd)) 

-- ack : ∀ {Γ} → exp Γ (fun nat nat) → exp Γ nat → exp Γ (fun nat nat)
-- ack f₀ n = rec f₀ (lam (lam (int (var hd)))) n
-- --some logical connectors
-- --¬ u
-- neg : ∀ {Γ} → exp Γ bool → exp Γ bool
-- neg u = if F T u
-- --u ∧ v
-- conj : ∀ {Γ} → exp Γ bool → exp Γ bool → exp Γ bool
-- conj u v = if v F u
-- --u ∨ v
-- disj : ∀ {Γ} → exp Γ bool → exp Γ bool → exp Γ bool
-- disj u v = if T v u

---------------------------------------------------
-- TODO: examples for higher order lifting
---------------------------------------------------
open import Data.Empty

-- a decidable Liftable may help in constructing the proofs... Lu
-- doesn't know how yet (Reflection? smart constructors? both?)
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


----------------
-- Proving liftable by reflection
----------------

open import Relation.Nullary.Decidable
open import Data.Product
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

ilift : ∀ {α Δ} → Liftable α × AExp Δ α → AExp Δ (D (erase α))
ilift p = uncurry Lift p

-- examples
e1 : AExp [] (SFun (D Num) (D Num))
e1 = (SLam (Var hd))

-- Liftable inferred
e1-lifted : _
e1-lifted = ilift (infer-lift e1)  -- liftable inferred

-- liftable inferred, without type signature; the only type needed is
-- for the function parameter (and the context)
e1-lifted' : AExp [] _
e1-lifted' = ilift (infer-lift (SLam {α₁ = D Num} (Var hd)))

-- TODO: It does not work as conventient as expected. Try to avoid the
-- duplication of α (first parameter)
e2 : AExp [] (SFun (SFun (D Num) (D Num)) (SFun (D Num) (D (Prd Num Num))))
e2 = (SLam 
       (SLam (DPair (SApp (Var (tl hd)) (Var hd))
             (DApp (ilift (infer-lift {α} (Var (tl hd))) ) (Var hd)))))
  where α = (SFun (D Num) (D Num))
             -- Arrr.. we still need α! 

