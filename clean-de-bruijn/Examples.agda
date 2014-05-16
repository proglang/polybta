module Examples where
open import Lib
open import Base
open import TwoLevel

add : AExp [] (SFun SNum (D (Fun Num Num)))
add = SLam (DLam (SRec (Var (tl hd)) (Var hd) (SLam (DSuc (Var hd)))))

pe_add : ℕ → Exp [] (Fun Num Num)
pe_add n = pe (SApp add (SCst n)) []

mult : AExp [] (SFun SNum (D (Fun Num Num)))
mult = SLam (DLam (SRec (Var (tl hd)) (DCst 0) (SLam (DAdd (Var hd) (Var (tl hd))))))

multn : ℕ → AExp [] (D (Fun Num Num))
multn n = SApp mult (SCst n)

pe_mult : ℕ → Exp [] (Fun Num Num)
pe_mult n = pe (multn n) []

dmult : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
dmult = DLam (DLam (DRec (Var (tl hd)) (DCst 0) (DLam (DAdd (Var hd) (Var (tl hd))))))

pe_dmult3 : Exp [] (Fun Num Num)
pe_dmult3 = pe (DApp dmult (DCst 3)) []

power : AExp [] (SFun SNum (D (Fun Num Num)))
power = SLam (DLam (DApp (DLam
        (SRec (Var (tl (tl hd)))
              (DCst 1)
              (SLam (DApp (DApp (Var (tl hd)) (Var hd)) (Var (tl (tl hd))))))) dmult))

pe_power : ℕ → Exp [] (Fun Num Num)
pe_power n = pe (SApp power (SCst n)) []

predecessor : AExp [] (SFun SNum SNum)
predecessor = SLam (SFst (SRec (Var hd) (SPair (SCst 0) (SCst 0))
                                        (SLam (SPair (SSnd (Var hd))
                                              (SSuc (SSnd (Var hd)))))))

pe_predecessor : ℕ → ℕ
pe_predecessor n = pe {[]} (SApp predecessor (SCst n)) []


iter : Exp [] (Fun (Fun Num Num) (Fun Num Num))
iter = ELam (ELam (ERec (ESuc (EVar hd)) (ECst 1) (EVar (tl hd))))

ack : Exp [ Fun (Fun Num Num) (Fun Num Num) ] (Fun Num (Fun Num Num))
ack = ELam (ERec (EVar hd) (ELam (ESuc (EVar hd))) (EVar (tl hd)))

ack-m-n : ℕ → ℕ → ℕ
ack-m-n m n = ev (EApp (EApp ack (ECst m)) (ECst n)) (ev iter [] ∷ [])
    
siter : AExp [] (SFun (D (Fun Num Num)) (SFun SNum (D Num)))
siter = SLam (SLam (SRec (SSuc (Var hd)) (DCst 1) (SLam (DApp (Var (tl (tl hd))) (Var hd)))))

diter : AExp [] (SFun (D (Fun Num Num)) (D (Fun Num Num)))
diter = SLam (DLam (DRec (DSuc (Var hd)) (DCst 1) (Var (tl hd))))

sack : AExp [ D (Fun (Fun Num Num) (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
sack = SLam (SRec (Var hd) (DLam (DSuc (Var hd))) (SLam (DApp (Var (tl (tl hd))) (Var hd))))

sack-m : ℕ → Exp [] (Fun Num Num)
sack-m m = pe (SApp sack (SCst m)) (iter ∷ [])

sack' : AExp [ SFun (D (Fun Num Num)) (D (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
sack' = SLam (SRec (Var hd) (DLam (DSuc (Var hd))) (Var (tl hd)))

sack'-m : ℕ → Exp [] (Fun Num Num)
sack'-m m = pe (SApp (SLam (SApp sack' (SCst m))) diter) []

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

try-lift : ∀ {α Γ} → AExp Γ α → Dec (Liftable α)
try-lift {α} _ = lift-dec α 

