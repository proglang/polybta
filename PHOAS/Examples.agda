module Examples where
open import Lib
open import Base
open import TwoLevel

-- terms
AExpSid : ∀ {A} → AExp (SFun A A)
AExpSid = SLam (λ x → Var x)

AExpDid : ∀ {A} → AExp (D (Fun A A))
AExpDid = DLam (λ x -> Var x)

AExpS3 : AExp SNum
AExpS3 = SCst 3

AExpD3 : AExp (D Num)
AExpD3 = DCst 3

AExp1 : AExp SNum
AExp1 = SApp AExpSid AExpS3

AExp2 : AExp (D Num)
AExp2 = SApp AExpSid AExpD3

AExp3 : AExp (D Num)
AExp3 = DApp AExpDid AExpD3

AExp4 : ∀ {A} → AExp (D (Fun A A))
AExp4 = DLam (λ x → SApp AExpSid (Var x))

-- examples in the paper
Ex0 : AExp (D (Fun Num Num))
Ex0 = DApp (DLam (λ x → DLam (λ y →
             DAdd (Lift (SAdd (SCst 5) (SCst 6))) (Var x))))
           (DCst 31)

Ex0-spec : Exp (Fun Num Num)
Ex0-spec = EApp (ELam (λ x → ELam (λ y →
                  EAdd (ECst 11) (EVar x))))
                (ECst 31)

Ex1 : AExp (D (Fun Num (Fun Num Num)))
Ex1 = DLam (λ z → SApp (SLam (λ y → DLam (λ x →
                           DAdd (Var z) (Var y))))
                         (DAdd (Var z) (DCst 5)))

Ex1-spec : Exp (Fun Num (Fun Num Num))
Ex1-spec = ELam (λ z → ELam (λ x →
                  EAdd (EVar z) (EAdd (EVar z) (ECst 5))))

Ex : AExp (D (Fun Num (Fun Num Num)))
Ex = DLam (λ z → SApp (SLam (λ y → DLam (λ x →
                          DAdd (Var z) (SApp (Var y) (DCst 5)))))
                        (SLam (λ x0 → Var z)))

Ex-spec : Exp (Fun Num (Fun Num Num))
Ex-spec = ELam (λ z → ELam (λ x → EAdd (EVar z) (EVar z)))

Ex' : AExp (D (Fun Num Num))
Ex' = DLam (λ z → SApp (SLam (λ y →
                           (DApp (DLam (λ x →
                                   DAdd (Var z) (SApp (Var y) (DCst 5))))
                                 (SApp (Var y) (DCst 6)))))
                         (SLam (λ x0 → Var z)))

Ex'-spec : Exp (Fun Num Num)
Ex'-spec = ELam (λ z → EApp (ELam (λ x → EAdd (EVar z) (EVar z))) (EVar z))

-- partial evaluation
test1 : Exp (Fun Num Num)
test1 = Pe AExpDid

test2 : Exp Num
test2 = Pe AExpD3

test3 : Exp Num
test3 = Pe AExp2

test4 : Exp Num
test4 = Pe AExp3

test5 : Exp (Fun Num Num)
test5 = Pe AExp4

-- examples in the paper
ex0-test : Pe {TInt} Ex0 ≡ Ex0-spec
ex0-test = refl

ex1-test : Pe {TInt} Ex1 ≡ Ex1-spec
ex1-test = refl

ex-test : Pe {TInt} Ex ≡ Ex-spec
ex-test = refl

ex'-test : Pe {TInt} Ex' ≡ Ex'-spec
ex'-test = refl

-- Rec examples
add : AExp (SFun SNum (D (Fun Num Num)))
add = SLam (λ m → DLam (λ n → SRec (Var m) (Var n) (SLam (λ l → DSuc (Var l)))))

Pe-add-test : Pe {TInt} (SApp add (SCst 5)) ≡ ELam (λ n → ESuc (ESuc (ESuc (ESuc (ESuc (EVar n))))))
Pe-add-test = refl

mult : AExp (SFun SNum (D (Fun Num Num)))
mult = SLam (λ m → DLam (λ n → SRec (Var m) (DCst 0) (SLam (λ l → DAdd (Var l) (Var n)))))

Pe-mult-test : Pe {TInt} (SApp mult (SCst 3))
                       ≡ ELam (λ l → EAdd (EAdd (EAdd (ECst 0) (EVar l)) (EVar l)) (EVar l))
Pe-mult-test = refl

dmult : AExp (D (Fun Num (Fun Num Num)))
dmult = DLam (λ m → DLam (λ n → DRec (Var m) (DCst 0) (DLam (λ l → DAdd (Var l) (Var n)))))

Pe-dmult-test : Pe {TInt} (DApp dmult (DCst 3))
                        ≡ EApp (ELam (λ m → ELam (λ n →
                                 ERec (EVar m) (ECst 0) (ELam (λ l → EAdd (EVar l) (EVar n))))))
                               (ECst 3)
Pe-dmult-test = refl

power : AExp (SFun SNum (D (Fun Num Num)))
power = SLam (λ m → DLam (λ n → DApp (DLam (λ dmult →
          SRec (Var m)
               (DCst 1)
               (SLam (λ l → DApp (DApp (Var dmult) (Var l)) (Var n)))))
        dmult))

Pe-power-test : Pe {TInt} (SApp power (SCst 3))
              ≡ ELam (λ n → EApp (ELam (λ mult →
                     EApp (EApp (EVar mult) (EApp (EApp (EVar mult) (EApp (EApp (EVar mult) (ECst 1))
                                                                          (EVar n)))
                                                  (EVar n)))
                          (EVar n)))
                (Residualize mult))
Pe-power-test = refl

predecessor : AExp (SFun SNum SNum)
predecessor = SLam (λ n → SFst (
                SRec (Var n)
                     (SPair (SCst 0) (SCst 0))
                     (SLam (λ p → SPair (SSnd (Var p))
                                          (SSuc (SSnd (Var p)))))))
Pe-predecessor-test : Pe {TInt} (SApp predecessor (SCst 5)) ≡ 4
Pe-predecessor-test = refl
