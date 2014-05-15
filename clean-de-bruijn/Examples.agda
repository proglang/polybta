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
