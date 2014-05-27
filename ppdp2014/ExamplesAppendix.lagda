\agdaIgnore{
\begin{code}
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
pe[] : ∀ {α} → AExp [] α → ATInt [] α
\end{code}}
\agdaSnippet\btaExPrelude{
\begin{code}
elet e e' = EApp (ELam e') e
dlet e e' = DApp (DLam e') e
\end{code}}
\agdaIgnore{
\begin{code}
pe[] e = pe {[]} e []
-- mult n m = m*n
emult : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
\end{code}}
\agdaSnippet\btaDMult{
\begin{code}
dmult : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
emult {Γ} = pe {Γ} dmult []
\end{code}}
\agdaIgnore{
\begin{code}

dmult = DLam (DLam (DRec (Var (tl hd))
                   (DCst 0)
                   (DLam (DAdd (Var hd)
                         (Var (tl hd))))))
mult : AExp [] (SFun SNum (D (Fun Num Num)))
mult = SLam (DLam (SRec (Var (tl hd)) -- n
                  (DCst 0)
                  (SLam (DAdd (Var hd) -- mult (n-1) m
                              (Var (tl hd)))))) -- m
ex-mult-pe1 :
\end{code}}
\agdaSnippet\btaExMultOne{
\begin{code}
  pe[] (SApp mult (SCst 1))
  ≡ ELam (EAdd (ECst zero) (EVar hd))
\end{code}}
\agdaIgnore{
\begin{code}
ex-mult-pe1 = refl

ex-mult-pe2 :
\end{code}}
\agdaSnippet\btaExMultTwo{
\begin{code}
  pe[] (SApp mult (SCst 3))
    ≡ ELam (EAdd (EAdd (EAdd (ECst 0)
      (EVar hd)) --m
      (EVar hd)) -- m
      (EVar hd)) -- m
\end{code}}
\agdaIgnore{
\begin{code}
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



\end{code}}
\agdaSnippet\btaPower{
\begin{code}
power : AExp [] (SFun SNum (D (Fun Num Num)))
power = SLam {- n -} (DLam {- m -}
        (dlet dmult (SRec (Var (tl (tl hd))) {- n -} (DCst 1)
                (SLam (DApp (DApp (Var (tl hd)) {- dmult -}
                            (Var hd)) {- power (n-1) m -}
                            (Var (tl (tl hd)))))))) {- m -}
\end{code}}
\agdaIgnore{
\begin{code}
ex-power-pe2 :
\end{code}
}
\agdaSnippet\btaPowerEx{
\begin{code}
  pe[] (SApp power (SCst 2))
               ≡ ELam {- m -}
                 (elet emult (EApp (EApp (EVar hd) {- emult -}
                     (EApp (EApp (EVar hd) {- emult -}
                           (ECst 1))
                           (EVar (tl hd)))) {- m -}
                           (EVar (tl hd)))) {- m -}
\end{code}}


\agdaIgnore{
\begin{code}
ex-power-pe1 : pe[] (SApp power (SCst 0)) ≡
               ELam (elet emult (ECst 1))
                       
ex-power-pe1 = refl
ex-power-pe2 = refl
-- Ackermann
eiter : Exp [] (Fun (Fun Num Num) (Fun Num Num))
eiter = ELam (ELam (ERec (ESuc (EVar hd)) (ECst 1) (EVar (tl hd))))

eack : Exp [ Fun (Fun Num Num) (Fun Num Num) ] (Fun Num (Fun Num Num))
eack = ELam (ERec (EVar hd) (ELam (ESuc (EVar hd))) (EVar (tl hd)))

-- diter : AExp [] (SFun (D (Fun Num Num)) (D (Fun Num Num)))
-- diter = SLam (DLam (DRec (DSuc (Var hd)) (DCst 1) (Var (tl hd))))

-- ack m n === Ack(m, n)
\end{code}}
\agdaSnippet\btaAck{
\begin{code}
ack : AExp [] (SFun SNum (D (Fun Num Num)))
ack = SLam (SRec (Var hd) (DLam (DSuc (Var hd))) iter) where
  iter = SLam (DLam (DRec (DSuc (Var hd)) (DCst 1) (Var (tl hd)))) 
  
ex-ack-0 : pe[] (SApp ack (SCst 0)) ≡ ELam (ESuc (EVar hd))
ex-ack-2 : pe[] (SApp ack (SCst 2)) ≡
            ELam (ERec (ESuc (EVar hd)) (ECst 1)
              (ELam (ERec (ESuc (EVar hd)) (ECst 1)
                  (ELam (ESuc (EVar hd))))))
\end{code}}
\agdaIgnore{
\begin{code}
ex-ack-2 = refl
ex-ack-0 = refl
\end{code}}

