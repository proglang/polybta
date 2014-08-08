module ExamplesAppendix where
open import Lib
open import BaseFull
open import TwoLevelFull
open import Correctness using (residualize)

--------
-- Preliminaries
----

-- residual let
elet : ∀ {Γ τ τ'} → Exp Γ τ → Exp (τ ∷ Γ) τ' → Exp Γ τ'
-- dynamic let
dlet : ∀ {Δ τ τ'} → AExp Δ (D τ) → AExp (D τ ∷ Δ) (D τ') → AExp Δ (D τ')
efoldN : ∀ {Γ τ} → Exp Γ Num → Exp Γ τ → Exp Γ (Fun τ τ)→ Exp Γ τ
sfoldN : ∀ {Δ τ} → AExp Δ SNum → AExp Δ τ → AExp Δ (SFun τ τ)→ AExp Δ τ
dfoldN : ∀ {Δ τ} → AExp Δ (D Num) → AExp Δ (D τ) → AExp Δ (D (Fun τ τ))→ AExp Δ (D τ)
pe[] : ∀ {α} → AExp [] α → ATInt [] α
econst : ∀ {Γ τ τ'} → Exp Γ (Fun τ (Fun τ' τ))
sconst : ∀ {Δ τ τ'} → AExp Δ (SFun τ (SFun τ' τ))
dconst : ∀ {Δ τ τ'} → AExp Δ (D (Fun τ (Fun τ' τ)))
-- utilities


elet e e' = EApp (ELam e') e
dlet e e' = DApp (DLam e') e
econst = ELam (ELam (EVar (tl hd)))
sconst = SLam (SLam (Var (tl hd)))
dconst = DLam (DLam (Var (tl hd)))
efoldN eₙ e₀ eₛ = ERec eₙ e₀ (EApp econst eₛ) 
sfoldN eₙ e₀ eₛ = SRec eₙ e₀ (SApp sconst eₛ) 
dfoldN eₙ e₀ eₛ = DRec eₙ e₀ (DApp dconst eₛ) 


pe[] e = pe {[]} e []
-- mult n m = m*n
emult : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))


dmult : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
emult {Γ} = pe {Γ} dmult []



dmult = DLam (DLam (dfoldN (Var (tl hd))
                   (DCst 0)
                   (DLam (DAdd (Var hd)
                         (Var (tl hd))))))
mult : AExp [] (SFun SNum (D (Fun Num Num)))
mult = SLam (DLam (sfoldN (Var (tl hd)) -- n
                  (DCst 0)
                  (SLam (DAdd (Var hd) -- mult (n-1) m
                              (Var (tl hd)))))) -- m
ex-mult-pe1 :


  pe[] (SApp mult (SCst 1))
  ≡ ELam (EAdd (ECst zero) (EVar hd))


ex-mult-pe1 = refl

ex-mult-pe2 :


  pe[] (SApp mult (SCst 3))
    ≡ ELam (EAdd (EAdd (EAdd (ECst 0)
      (EVar hd)) --m
      (EVar hd)) -- m
      (EVar hd)) -- m


ex-mult-pe2 = refl
ex-mult-pe3 : pe {[]} (SApp mult (SCst 5)) []
              ≡ ELam (EAdd
                       (EAdd
                       (EAdd (EAdd
                             (EAdd (ECst 0) (EVar hd))
                             (EVar hd))
                        (EVar hd))
                       (EVar hd))
                       (EVar hd))
ex-mult-pe3 = refl





power : AExp [] (SFun SNum (D (Fun Num Num)))
power = SLam {- n -} (DLam {- m -}
        (dlet dmult (sfoldN (Var (tl (tl hd))) {- n -} (DCst 1)
                (SLam (DApp (DApp (Var (tl hd)) {- dmult -}
                            (Var hd)) {- power (n-1) m -}
                            (Var (tl (tl hd)))))))) {- m -}


ex-power-pe2 :


  pe[] (SApp power (SCst 2))
               ≡ ELam {- m -}
                 (elet emult (EApp (EApp (EVar hd) {- emult -}
                     (EApp (EApp (EVar hd) {- emult -}
                           (ECst 1))
                           (EVar (tl hd)))) {- m -}
                           (EVar (tl hd)))) {- m -}


ex-power-pe1 : pe[] (SApp power (SCst 0)) ≡
               ELam (elet emult (ECst 1))
                       
ex-power-pe1 = refl
ex-power-pe2 = refl
-- Ackermann
-- efoldN : Exp [] (Fun (Fun Num Num) (Fun Num Num))
-- efoldN = ELam (ELam (ERec (ESuc (EVar hd)) (ECst 1) (EVar (tl hd))))

eack : Exp [ Fun (Fun Num Num) (Fun Num Num) ] (Fun Num (Fun Num Num))
eack = ELam (efoldN (EVar hd) (ELam (ESuc (EVar hd))) (EVar (tl hd)))

-- dfoldN : AExp [] (SFun (D (Fun Num Num)) (D (Fun Num Num)))
-- dfoldN = SLam (DLam (DRec (DSuc (Var hd)) (DCst 1) (Var (tl hd))))

-- ack m n === Ack(m, n)


ack : AExp [] (SFun SNum (D (Fun Num Num)))
ack = SLam {- m -}
        (sfoldN (Var hd) {- m -} (DLam (DSuc (Var hd))) iter) 
  where iter = SLam {- f -} (DLam {- n -}
          (dfoldN (DSuc (Var hd){- n -}) 
                (DCst 1)
                (Var (tl hd)))) {- f -}
  
ex-ack-0 : pe[] (SApp ack (SCst 0)) ≡ ELam (ESuc (EVar hd))
ex-ack-2 : pe[] (SApp ack (SCst 2)) ≡
            ELam (efoldN (ESuc (EVar hd)) (ECst 1)
              (ELam (efoldN (ESuc (EVar hd)) (ECst 1)
                  (ELam (ESuc (EVar hd))))))


ex-ack-2 = refl
ex-ack-0 = refl

ack-m-n : ℕ → ℕ → ℕ
ack-m-n m n = ev (EApp (pe[] (SApp ack (SCst m))) (ECst n)) []

test-ack-2-0 : ack-m-n 2 0 ≡ 3
test-ack-2-0 = refl

test-ack-2-1 : ack-m-n 2 1 ≡ 5
test-ack-2-1 = refl

test-ack-1-4 : ack-m-n 1 4 ≡ 6
test-ack-1-4 = refl



