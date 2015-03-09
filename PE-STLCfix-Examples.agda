module PE-STLCfix-Examples where
open import PE-STLCfix
open import Data.Maybe


--some examples of base-level terms
--addition(recursive)
--Fix λ f. λ n n'. match n | 0    => n'
--                         | S n  => S (f n n')
                    
--addition(iterative)
--Fix λ f. λ n n'. match n | 0    => n'
--                         | S n  => f (n (S n'))

add : Exp [] (Fun Num (Fun Num Num))
add = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) --dispatch upon the first argument
                     (Var hd)      
                     (Suc (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd)))))))) 





aDD : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
aDD {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
                   (Lam Num 
                   (Lam Num 
                   (Dspℕ (Var (tl hd)) 
                         (Var hd) 
                         (Suc (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd))))))))

add' : Exp [] (Fun Num (Fun Num Num))
add' = Fix (Lam (Fun Num (Fun Num Num)) 
                (Lam Num 
                (Lam Num 
                (Dspℕ (Var (tl hd)) 
                      (Var hd) 
                      (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Suc (Var (tl hd))))))))

aDD' : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
aDD' {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
                (Lam Num 
                (Lam Num 
                (Dspℕ (Var (tl hd)) 
                      (Var hd) 
                      (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Suc (Var (tl hd))))))))

--multiplication(recursive)
--Fix λ f. λ n n'. match n | 0       => 0
--                         | 1       => n'
--                         | S (S n) => n' + (f (S n) n')



mul : Exp [] (Fun Num (Fun Num Num))
mul = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                     (Var (tl hd)) 
                     (App (App aDD (Var (tl (tl hd)))) 
                          (App (App (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

mUL : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
mUL {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                     (Var (tl hd)) 
                     (App (App aDD (Var (tl (tl hd)))) 
                          (App (App (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

mUL' : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
mUL' {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                     (Var (tl hd)) 
                     (App (App aDD' (Var (tl (tl hd)))) 
                          (App (App (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

--factorial(recursive)
--Fix λ f. λ n. match n | 0   => 1
--                      | S n' => n * (f n')

fact : Exp [] (Fun Num Num)
fact = Fix (Lam (Fun Num Num) 
                (Lam Num 
                (Dspℕ (Var hd) 
                      (C 1) 
                      (App (App mUL (Var (tl hd))) 
                           ((App (Var (tl (tl hd))) (Var hd)))))))

--nth Fibonacci number(recursive)
--Fix λ f. λ n. match n | 0        => 0
--                      | 1        => 1
--                      | S (S n') => f (S n') + f n'

fib : Exp [] (Fun Num Num)
fib = Fix (Lam (Fun Num Num) 
               (Lam Num 
               (Dspℕ (Var hd) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                           (C 1) 
                           (App (App aDD (App (Var (tl (tl (tl hd)))) (Var (tl hd)))) (App (Var (tl (tl (tl hd)))) (Var hd)))))))



--some evaluation examples
------------------------------------------------
--note:given sufficient amount of "fuel"
--     evaluator [ev] is expected to return
--     correct result in case recursive function
--     application
------------------------------------------------

--a)sum(recursive)
ex1 : ev 3000 (App (App add (C 1)) (C 6)) [] ≡ just 7
ex1 = refl

--b)sum(iterative)
ex2 : ev 3000 (App (App add' (C 1)) (C 6)) [] ≡ just 7
ex2 = refl

--c)multiplication(recursive)
ex3 : ev 3000 (App (App mul (C 5)) (C 6)) [] ≡ just 30
ex3 = refl

--d)factorial
ex5 : ev 3000 (App fact (C 6)) [] ≡ just 720
ex5 = refl

--e)nth Fibonacci number
ex6 : ev 3000 (App fib (C 9)) [] ≡ just 34
ex6 = refl



--examples of two-level terms
--some examples
--addition
ADDD : AExp [] (D (Fun Num (Fun Num Num)))
ADDD = DFix (DLam (Fun Num (Fun Num Num)) 
               (DLam Num 
               (DLam Num 
               (DDspℕ (Var (tl hd)) 
                     (Var hd)      
                     (DSuc (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd)))))))) 

                     

AddD : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
AddD {Δ} = DFix (DLam (Fun Num (Fun Num Num)) 
                   (DLam Num 
                   (DLam Num 
                   (DDspℕ (Var (tl hd)) 
                         (Var hd) 
                         (DSuc (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd))))))))


ADDD' : AExp [] (D (Fun Num (Fun Num Num)))
ADDD' = DFix (DLam (Fun Num (Fun Num Num)) 
                (DLam Num 
                (DLam Num 
                (DDspℕ (Var (tl hd)) 
                      (Var hd) 
                      (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (DSuc (Var (tl hd))))))))



AddD' : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
AddD' {Δ} = DFix (DLam (Fun Num (Fun Num Num)) 
                (DLam Num 
                (DLam Num 
                (DDspℕ (Var (tl hd)) 
                      (Var hd) 
                      (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (DSuc (Var (tl hd))))))))





MULD : AExp [] (D (Fun Num (Fun Num Num)))
MULD = DFix (DLam (Fun Num (Fun Num Num)) 
               (DLam Num 
               (DLam Num 
               (DDspℕ (Var (tl hd)) 
                     (DC 0) 
                     (DDspℕ (Var hd) 
                     (Var (tl hd)) 
                     (DApp (DApp AddD (Var (tl (tl hd)))) 
                          (DApp (DApp (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))



MulD : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
MulD {Δ} = DFix (DLam (Fun Num (Fun Num Num)) 
               (DLam Num 
               (DLam Num 
               (DDspℕ (Var (tl hd)) 
                     (DC 0) 
                     (DDspℕ (Var hd) 
                     (Var (tl hd)) 
                     (DApp (DApp AddD (Var (tl (tl hd)))) 
                          (DApp (DApp (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))



FACTD : AExp [] (D (Fun Num Num))
FACTD = DFix (DLam (Fun Num Num) 
                (DLam Num 
                (DDspℕ (Var hd) 
                      (DC 1) 
                      (DApp (DApp MulD (Var (tl hd))) 
                           ((DApp (Var (tl (tl hd))) (Var hd)))))))





FIBD : AExp [] (D (Fun Num Num))
FIBD = DFix (DLam (Fun Num Num) 
               (DLam Num 
               (DDspℕ (Var hd) 
                     (DC 0) 
                     (DDspℕ (Var hd) 
                           (DC 1) 
                           (DApp (DApp AddD (DApp (Var (tl (tl (tl hd)))) (Var (tl hd)))) (DApp (Var (tl (tl (tl hd)))) (Var hd)))))))





--some evaluation examples
EX1 : pe (DApp (DApp ADDD (DC 1)) (DC 6)) [] ≡ App (App add (C 1)) (C 6)
EX1 = refl

EX3 : pe (DApp (DApp ADDD' (DC 1)) (DC 6)) [] ≡ App (App add' (C 1)) (C 6)
EX3 = refl

EX5 : pe (DApp (DApp MULD (DC 5)) (DC 6)) [] ≡ App (App mul (C 5)) (C 6)
EX5 = refl

EX7 : pe (DApp FACTD (DC 6)) [] ≡ App fact (C 6)
EX7 = refl

EX9 : pe (DApp FIBD (DC 9)) [] ≡ App fib (C 9)
EX9 = refl



--residual let
elet : ∀ {Γ σ σ'} → Exp Γ σ → Exp (σ ∷ Γ) σ' → Exp Γ σ'
-- dynamic let
dlet : ∀ {Δ σ σ'} → AExp Δ (D σ) → AExp (D σ ∷ Δ) (D σ') → AExp Δ (D σ')
sfoldN : ∀ {Δ α} → AExp Δ SNum → AExp Δ α → AExp Δ (SFun α α)→ AExp Δ α
pe[] : ∀ {α} → AExp [] α → ATInt [] α
econst : ∀ {Γ σ σ'} → Exp Γ (Fun σ (Fun σ' σ))
sconst : ∀ {Δ α α'} → AExp Δ (SFun α (SFun α' α))
dconst : ∀ {Δ σ σ'} → AExp Δ (D (Fun σ (Fun σ' σ)))

elet e e' = App (Lam _ e') e
dlet e e' = DApp (DLam _ e') e
econst = Lam _ (Lam _ (Var (tl hd)))
sconst = SLam _ (SLam _ (Var (tl hd)))
dconst = DLam _ (DLam _ (Var (tl hd)))
sfoldN eₙ e₀ eₛ = SRec e₀ (SApp sconst eₛ) eₙ 
pe[] e = pe {Γ = []} {Δ = []} e []



-- n * m
--note:
--a)dynamic addition is defined by fix-point operator
--b)so is the base-level addition

MULS : AExp [] (SFun SNum (D (Fun Num Num)))
MULS = SLam SNum (DLam Num (sfoldN (Var (tl hd)) (DC 0) (SLam (D Num) (DApp (DApp AddD (Var hd)) (Var (tl hd))))))

ex-MULS-pe1 : pe[] (SApp MULS (SC 1)) ≡ Lam Num (App (App aDD (C 0)) (Var hd))
ex-MULS-pe1 = refl

ex-MULS-pe2 : pe[] (SApp MULS (SC 3)) ≡ Lam Num (App (App aDD 
                                         ((App (App aDD 
                                          ((App (App aDD (C 0)) (Var hd)))
                                          ) (Var hd)))              
                                        ) (Var hd))
ex-MULS-pe2 = refl

ex-MULS-pe3 : pe[] (SApp MULS (SC 5)) ≡ Lam Num (App (App aDD (
                                          App (App aDD (
                                          App (App aDD (
                                          App (App aDD (
                                          App (App aDD (C 0)) 
                                            (Var hd)
                                         )) (Var hd)
                                         )) (Var hd)
                                         )) (Var hd)               
                                         )) (Var hd))
ex-MULS-pe3 = refl

--mⁿ

POWERS : AExp [] (SFun SNum (D (Fun Num Num)))
POWERS = SLam SNum (DLam Num 
         (dlet MulD (sfoldN (Var (tl (tl hd))) (DC 1)
                       (SLam (D Num)
                        (DApp (DApp (Var (tl hd)) (Var hd)) (Var (tl (tl hd))))))))

ex-POWERS-pe1 : pe[] (SApp POWERS (SC 0)) ≡ Lam Num (elet mUL (C 1))
ex-POWERS-pe1 = refl


ex-POWERS-pe2 : pe[] (SApp POWERS (SC 2)) ≡ Lam Num (elet mUL 
                                            (App (App (Var hd) (App (App (Var hd) (C 1)) 
                                           (Var (tl hd)))) 
                                           (Var (tl hd))))
ex-POWERS-pe2 = refl


--ack
ACKS : AExp [] (SFun SNum (D (Fun Num Num)))
ACKS = SLam SNum (sfoldN (Var hd) (DLam Num (DSuc (Var hd))) 
       iter)
    where iter = SLam _ (DLam _ 
                 {!!})

