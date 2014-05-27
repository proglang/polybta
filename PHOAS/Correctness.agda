module Correctness where
open import Lib
open import Base
open import TwoLevel
open import Data.Empty

-- logical relation
Equiv : ∀ {A} → ATInt TInt A → TInt (erase A) → Set
Equiv {SNum}     u v = u ≡ v
Equiv {SFun A B} u v = ∀ {u' v'} → Equiv u' v' → Equiv (u u') (v v')
Equiv {SPrd A B} (u1 , u2) (v1 , v2) = Equiv u1 v1 × Equiv u2 v2
Equiv {SSum A B} (inj₁ u) (inj₁ v) = Equiv u v
Equiv {SSum A B} (inj₁ u) (inj₂ v) = ⊥
Equiv {SSum A B} (inj₂ u) (inj₁ v) = ⊥
Equiv {SSum A B} (inj₂ u) (inj₂ v) = Equiv u v
Equiv {D t}      u v = ev u ≡ v

-- functional extensionality
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g

-- correctness
data similar-aexp {var1 var2} (Γ : List (Σ[ A ∈ AType ] (var1 A × var2 A)))
                  : ∀ {A} → aexp var1 A → aexp var2 A → Set where
  similar-Var : ∀ {A x1 x2} → (A , x1 , x2) ∈ Γ → similar-aexp Γ (Var x1) (Var x2)
  similar-SCst : ∀ {n} → similar-aexp Γ (SCst n) (SCst n)
  similar-SSuc : ∀ {e1 e2} → similar-aexp Γ e1 e2 →
                 similar-aexp Γ (SSuc e1) (SSuc e2)
  similar-SRec : ∀ {α} {e1 e2} {z1 : aexp var1 α} {z2} {s1 s2} →
                 similar-aexp Γ e1 e2 →
                 similar-aexp Γ z1 z2 →
                 similar-aexp Γ s1 s2 →
                 similar-aexp Γ (SRec e1 z1 s1) (SRec e2 z2 s2)
  similar-SAdd : ∀ {e11 e12 e21 e22} →
                 similar-aexp Γ e11 e21 → similar-aexp Γ e12 e22 →
                 similar-aexp Γ (SAdd e11 e12) (SAdd e21 e22)
  similar-SLam : ∀ {A B} {f1 : var1 A → aexp var1 B} {f2 : var2 A → aexp var2 B} →
                 (∀ {v1 v2} → similar-aexp ((A , v1 , v2) ∷ Γ) (f1 v1) (f2 v2)) →
                 similar-aexp Γ (SLam f1) (SLam f2)
  similar-SApp : ∀ {A B} {e1f : aexp var1 (SFun A B)} {e1a : aexp var1 A} {e2f e2a} →
                 similar-aexp Γ e1f e2f → similar-aexp Γ e1a e2a →
                 similar-aexp Γ (SApp e1f e1a) (SApp e2f e2a)
  similar-SPair : ∀ {A B e11 e12 e21 e22} →
                 similar-aexp Γ {A} e11 e21 → similar-aexp Γ {B} e12 e22 →
                 similar-aexp Γ (SPair e11 e12) (SPair e21 e22)
  similar-SFst : ∀ {A B e1 e2} →
                 similar-aexp Γ {SPrd A B} e1 e2 →
                 similar-aexp Γ (SFst e1) (SFst e2)
  similar-SSnd : ∀ {A B e1 e2} →
                 similar-aexp Γ {SPrd A B} e1 e2 →
                 similar-aexp Γ (SSnd e1) (SSnd e2)
  similar-SInl : ∀ {A B e1 e2} → similar-aexp Γ e1 e2 →
                 similar-aexp Γ {SSum A B} (SInl e1) (SInl e2)
  similar-SInr : ∀ {A B e1 e2} → similar-aexp Γ e1 e2 →
                 similar-aexp Γ {SSum A B} (SInr e1) (SInr e2)
  similar-SCase : ∀ {A B C e1 e2 e11 e12 e21 e22} →
                 similar-aexp Γ e1 e2 →
                 (∀ {v1 v2} → similar-aexp ((A , v1 , v2) ∷ Γ) {C} (e11 v1) (e21 v2)) →
                 (∀ {v1 v2} → similar-aexp ((B , v1 , v2) ∷ Γ) {C} (e12 v1) (e22 v2)) →
                 similar-aexp Γ (SCase e1 e11 e12) (SCase e2 e21 e22)
  similar-DCst : ∀ {n} → similar-aexp Γ (DCst n) (DCst n)
  similar-DSuc : ∀ {e1 e2} → similar-aexp Γ e1 e2 →
                 similar-aexp Γ (DSuc e1) (DSuc e2)
  similar-DRec : ∀ {α} {e1 e2} {z1 : aexp var1 (D α)} {z2} {s1 s2} →
                 similar-aexp Γ e1 e2 →
                 similar-aexp Γ z1 z2 →
                 similar-aexp Γ s1 s2 →
                 similar-aexp Γ (DRec e1 z1 s1) (DRec e2 z2 s2)
  similar-DAdd : ∀ {e11 e12 e21 e22} →
                 similar-aexp Γ e11 e21 → similar-aexp Γ e12 e22 →
                 similar-aexp Γ (DAdd e11 e12) (DAdd e21 e22)
  similar-DLam : ∀ {A B} {f1 : var1 (D A) → aexp var1 (D B)} {f2 : var2 (D A) → aexp var2 (D B)} →
                 (∀ {v1 v2} → similar-aexp ((D A , v1 , v2) ∷ Γ) (f1 v1) (f2 v2)) →
                 similar-aexp Γ (DLam f1) (DLam f2)
  similar-DApp : ∀ {A B} {e1f : aexp var1 (D (Fun A B))} {e1a : aexp var1 (D A)} {e2f e2a} →
                 similar-aexp Γ e1f e2f → similar-aexp Γ e1a e2a →
                 similar-aexp Γ (DApp e1f e1a) (DApp e2f e2a)
  similar-DPair : ∀ {A B e11 e12 e21 e22} →
                 similar-aexp Γ {D A} e11 e21 → similar-aexp Γ {D B} e12 e22 →
                 similar-aexp Γ (DPair e11 e12) (DPair e21 e22)
  similar-DFst : ∀ {A B e1 e2} →
                 similar-aexp Γ {D (Prd A B)} e1 e2 →
                 similar-aexp Γ (DFst e1) (DFst e2)
  similar-DSnd : ∀ {A B e1 e2} →
                 similar-aexp Γ {D (Prd A B)} e1 e2 →
                 similar-aexp Γ (DSnd e1) (DSnd e2)
  similar-DInl : ∀ {A B e1 e2} → similar-aexp Γ e1 e2 →
                 similar-aexp Γ {D (Sum A B)} (DInl e1) (DInl e2)
  similar-DInr : ∀ {A B e1 e2} → similar-aexp Γ e1 e2 →
                 similar-aexp Γ {D (Sum A B)} (DInr e1) (DInr e2)
  similar-DCase : ∀ {A B C e1 e2 e11 e12 e21 e22} →
                 similar-aexp Γ e1 e2 →
                 (∀ {v1 v2} → similar-aexp ((D A , v1 , v2) ∷ Γ) {D C} (e11 v1) (e21 v2)) →
                 (∀ {v1 v2} → similar-aexp ((D B , v1 , v2) ∷ Γ) {D C} (e12 v1) (e22 v2)) →
                 similar-aexp Γ (DCase e1 e11 e12) (DCase e2 e21 e22)
  similar-Lift : ∀ {e1 e2} → similar-aexp Γ e1 e2 →
                 similar-aexp Γ (Lift e1) (Lift e2)

data Equiv-Env : List (Σ[ A ∈ AType ] (ATInt TInt A × exp TInt (erase A))) → Set where
  [] : Equiv-Env []
  cons : ∀ {Γ A v1 v2} →
         Equiv {A} v1 (ev v2) →
         Equiv-Env Γ →
         Equiv-Env ((A , v1 , v2) ∷ Γ)

pe-correct : ∀ {A Γ} → (t1 : aexp (ATInt TInt) A) → (t2 : aexp (λ B → exp TInt (erase B)) A) →
              similar-aexp Γ t1 t2 → Equiv-Env Γ → Equiv (pe t1) (ev (residualize t2))
pe-correct {A} {.[]} .(Var {_} {A} x1) .(Var {_} {A} x2) (similar-Var {.A} {x1} {x2} ()) []
pe-correct {.A} {.((A , v1 , v2) ∷ Γ)} .(Var {_} {A} v1) .(Var {_} {A} v2) (similar-Var {.A} {.v1} {.v2} (hd {.(A , v1 , v2)} {.Γ})) (cons {Γ} {A} {v1} {v2} x₁ p) = x₁
pe-correct {A} {.((A₁ , v1 , v2) ∷ Γ)} .(Var {_} {A} x1) .(Var {_} {A} x2) (similar-Var {.A} {x1} {x2} (tl {.(A , x1 , x2)} {.(A₁ , v1 , v2)} {.Γ} x)) (cons {Γ} {A₁} {v1} {v2} x₁ p) = pe-correct (Var x1) (Var x2) (similar-Var x) p
pe-correct {.SNum} {Γ} .(SCst n) .(SCst n) (similar-SCst {n}) p = refl
pe-correct {.SNum} {Γ} .(SSuc e1) .(SSuc e2) (similar-SSuc {e1} {e2} s) l = cong suc (pe-correct e1 e2 s l)
pe-correct {A} {Γ} .(SRec {_} {A} e1 z1 s1) .(SRec {_} {A} e2 z2 s2) (similar-SRec {.A} {e1} {e2} {z1} {z2} {s1} {s2} s s₁ s₂) l with pe-correct e1 e2 s l
... | IA rewrite IA = natrec-correct (ev (residualize e2))
  where
    natrec-correct : ∀ (n : ℕ) →
      Equiv (natrec n (pe z1) (pe s1))
            (natrec n (ev (residualize z2)) (ev (residualize s2)))
    natrec-correct zero = pe-correct z1 z2 s₁ l
    natrec-correct (suc n) = (pe-correct s1 s2 s₂ l) (natrec-correct n)
pe-correct {.SNum} {Γ} .(SAdd e11 e12) .(SAdd e21 e22) (similar-SAdd {e11} {e12} {e21} {e22} s s₁) l = cong₂ _+_ (pe-correct e11 e21 s l) (pe-correct e12 e22 s₁ l)
pe-correct {.(SFun A B)} {Γ} .(SLam {_} {A} {B} f1) .(SLam {_} {A} {B} f2) (similar-SLam {A} {B} {f1} {f2} x) p = λ {u'} {v'} x₁ → pe-correct (f1 u') (f2 (EVar v')) x (cons x₁ p)
pe-correct {A} {Γ} .(SApp {_} {A₁} {A} e1f e1a) .(SApp {_} {A₁} {A} e2f e2a) (similar-SApp {A₁} {.A} {e1f} {e1a} {e2f} {e2a} g g₁) p = (pe-correct e1f e2f g p) (pe-correct e1a e2a g₁ p)
pe-correct {.(SPrd A B)} {Γ} .(SPair {_} {A} {B} e11 e12) .(SPair {_} {A} {B} e21 e22) (similar-SPair {A} {B} {e11} {e12} {e21} {e22} s1 s2) p = (pe-correct e11 e21 s1 p , pe-correct e12 e22 s2 p)
pe-correct {A} {Γ} .(SFst {_} {A} {B} e1) .(SFst {_} {A} {B} e2) (similar-SFst {.A} {B} {e1} {e2} s) p with pe-correct e1 e2 s p
... | (v1 , v2) = v1
pe-correct {A} {Γ} .(SSnd {_} {A₁} {A} e1) .(SSnd {_} {A₁} {A} e2) (similar-SSnd {A₁} {.A} {e1} {e2} s) p with pe-correct e1 e2 s p
... | (v1 , v2) = v2
pe-correct {.(SSum A B)} {Γ} .(SInl {_} {A} {B} e1) .(SInl {_} {A} {B} e2) (similar-SInl {A} {B} {e1} {e2} s) p = pe-correct e1 e2 s p
pe-correct {.(SSum A B)} {Γ} .(SInr {_} {A} {B} e1) .(SInr {_} {A} {B} e2) (similar-SInr {A} {B} {e1} {e2} s) p = pe-correct e1 e2 s p
pe-correct {C} {Γ} .(SCase {_} {A} {B} {C} e1 e11 e12) .(SCase {_} {A} {B} {C} e2 e21 e22) (similar-SCase {A} {B} {.C} {e1} {e2} {e11} {e12} {e21} {e22} s s1 s2) p with pe e1 | ev (residualize e2) | pe-correct e1 e2 s p
... | inj₁ v1 | inj₁ v2 | p1 = pe-correct (e11 v1) (e21 (EVar v2)) s1 (cons p1 p)
... | inj₁ v1 | inj₂ v2 | ()
... | inj₂ v1 | inj₁ v2 | ()
... | inj₂ v1 | inj₂ v2 | p2 = pe-correct (e12 v1) (e22 (EVar v2)) s2 (cons p2 p)
pe-correct {.(D Num)} {Γ} .(DCst n) .(DCst n) (similar-DCst {n}) p = refl
pe-correct {.(D Num)} {Γ} .(DSuc e1) .(DSuc e2) (similar-DSuc {e1} {e2} s) l = cong suc (pe-correct e1 e2 s l)
pe-correct {.(D α)} {Γ} .(DRec {_} {α} e1 z1 s1) .(DRec {_} {α} e2 z2 s2) (similar-DRec {α} {e1} {e2} {z1} {z2} {s1} {s2} s s₁ s₂) l = cong₃ natrec (pe-correct e1 e2 s l) (pe-correct z1 z2 s₁ l) (pe-correct s1 s2 s₂ l)
pe-correct {.(D Num)} {Γ} .(DAdd e11 e12) .(DAdd e21 e22) (similar-DAdd {e11} {e12} {e21} {e22} s s₁) l = cong₂ _+_ (pe-correct e11 e21 s l) (pe-correct e12 e22 s₁ l)
pe-correct {.(D (Fun A B))} {Γ} .(DLam {_} {A} {B} f1) .(DLam {_} {A} {B} f2) (similar-DLam {A} {B} {f1} {f2} x) p = extensionality (λ a → pe-correct (f1 (EVar a)) (f2 (EVar a)) x (cons refl p))
pe-correct {.(D B)} {Γ} .(DApp {_} {A} {B} e1f e1a) .(DApp {_} {A} {B} e2f e2a) (similar-DApp {A} {B} {e1f} {e1a} {e2f} {e2a} g g₁) p = cong₂ (λ x y → x y) (pe-correct e1f e2f g p) (pe-correct e1a e2a g₁ p)
pe-correct {.(D (Prd A B))} {Γ} .(DPair {_} {A} {B} e11 e12) .(DPair {_} {A} {B} e21 e22) (similar-DPair {A} {B} {e11} {e12} {e21} {e22} s1 s2) p = cong₂ (λ x y → (x , y)) (pe-correct e11 e21 s1 p) (pe-correct e12 e22 s2 p)
pe-correct {.(D A)} {Γ} .(DFst {_} {A} {B} e1) .(DFst {_} {A} {B} e2) (similar-DFst {A} {B} {e1} {e2} s) p = cong proj₁ (pe-correct e1 e2 s p)
pe-correct {.(D B)} {Γ} .(DSnd {_} {A} {B} e1) .(DSnd {_} {A} {B} e2) (similar-DSnd {A} {B} {e1} {e2} s) p = cong proj₂ (pe-correct e1 e2 s p)
pe-correct {.(D (Sum A B))} {Γ} .(DInl {_} {A} {B} e1) .(DInl {_} {A} {B} e2) (similar-DInl {A} {B} {e1} {e2} s) p = cong inj₁ (pe-correct e1 e2 s p)
pe-correct {.(D (Sum A B))} {Γ} .(DInr {_} {A} {B} e1) .(DInr {_} {A} {B} e2) (similar-DInr {A} {B} {e1} {e2} s) p = cong inj₂ (pe-correct e1 e2 s p)
pe-correct {.(D C)} {Γ} .(DCase {_} {A} {B} {C} e1 e11 e12) .(DCase {_} {A} {B} {C} e2 e21 e22) (similar-DCase {A} {B} {C} {e1} {e2} {e11} {e12} {e21} {e22} s s1 s2) p with ev (pe e1) | ev (residualize e2) | pe-correct e1 e2 s p
... | .(inj₁ v) | inj₁ v | refl = pe-correct (e11 (EVar v)) (e21 (EVar v)) s1 (cons refl p)
... | .(inj₂ v) | inj₂ v | refl = pe-correct (e12 (EVar v)) (e22 (EVar v)) s2 (cons refl p)
pe-correct {.(D Num)} {Γ} .(Lift e1) .(Lift e2) (similar-Lift {e1} {e2} s) p = pe-correct e1 e2 s p

pe-correct-dyn : ∀ {A} → (T : AExp (D A)) → similar-aexp [] T T →
                  ev (pe T) ≡ ev (residualize T)
pe-correct-dyn T p = pe-correct T T p []
