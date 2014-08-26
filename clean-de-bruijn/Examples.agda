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

--application of recursors


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

