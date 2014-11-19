module PE-STLC-DBL-a where
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality

--simple two-level types
data Type : Set where
  Num : Type
  Fun : Type → Type → Type

data AType : Set where
  SNum  : AType
  SFun  : AType → AType → AType
  D     : Type → AType


Ctx  = List Type
ACtx = List AType

  
data _↝_ {A : Set} : List A → List A → Set where
  refl   : {l : List A} → l ↝ l
  extend : ∀ {l₁ l₂ τ} → l₁ ↝ l₂ → l₁ ↝ (τ ∷ l₂)

data _↝_↝_ {A : Set} : List A → List A → List A → Set where
  refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ''
  extend : ∀ {Γ Γ' Γ'' τ} →
               Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'')

lem-↝-trans : ∀ {A : Set}{Γ Γ' Γ'' : List A} → Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
lem-↝-trans Γ↝Γ' refl = Γ↝Γ'
lem-↝-trans Γ↝Γ' (extend Γ'↝Γ'') = extend (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
    
data Option (A : Set) : Set where
  Some : A → Option A
  Nothing : Option A

 
Length : ∀ {A : Set} → List A → ℕ
Length [] = zero
Length (x ∷ ls) = suc (Length ls) 

ℕ≡? : ℕ → ℕ → Bool
ℕ≡? zero zero = true
ℕ≡? zero (suc m) = false
ℕ≡? (suc n) zero = false
ℕ≡? (suc n) (suc m) = ℕ≡? n m

  
LookUp : ∀ {A : Set} → ℕ → List A → Option A 
LookUp n [] = Nothing
LookUp n (x ∷ Δ) with ℕ≡? n (Length Δ) 
... | true = Some x
... | false = LookUp n Δ

ℕ≡true : ∀ {A : Set} {Γ : List A} → ℕ≡? (Length Γ) (Length Γ) ≡ true
ℕ≡true {A} {[]} = refl
ℕ≡true {A} {x ∷ Γ} = ℕ≡true {A} {Γ}  

ℕ≡false : ∀ {A : Set} {Γ : List A} → ℕ≡? (Length Γ) (suc (Length Γ)) ≡ false
ℕ≡false {A} {[]} = refl
ℕ≡false {A} {x ∷ Γ} = ℕ≡false {A} {Γ}

lemma≡ : ∀ {A : Set} {τ : A} {Γ : List A} → LookUp (Length Γ) (τ ∷ Γ) ≡ Some τ
lemma≡ {A} {τ} {[]} = refl
lemma≡ {A} {τ} {x ∷ Γ} rewrite ℕ≡true {A} {Γ} = refl 

  
   
 
 
data exp (Γ : Ctx) : Type → Set where
  evar : ∀ {τ} → (n : ℕ) → LookUp n Γ ≡ Some τ → exp Γ τ
  ecst : ℕ → exp Γ Num
  eadd : exp Γ Num → exp Γ Num -> exp Γ Num
  elam : ∀ {τ τ'} → exp (τ ∷ Γ) τ' → exp Γ (Fun τ τ')
  eapp : ∀ {τ τ'} → exp Γ (Fun τ τ')  → exp Γ τ → exp Γ τ'

data aexp (Δ : ACtx) : AType → Set where
  var : ∀ {α} → (n : ℕ) → LookUp n Δ ≡ Some α → aexp Δ α
  scst : ℕ → aexp Δ SNum
  sadd : aexp Δ SNum → aexp Δ SNum → aexp Δ SNum
  slam : ∀ {α₁ α₂}   → aexp (α₂ ∷ Δ) α₁ → aexp Δ (SFun α₂ α₁)
  sapp : ∀ {α₁ α₂}   → aexp Δ (SFun α₂ α₁) → aexp Δ α₂ → aexp Δ α₁
  dcst : ℕ → aexp Δ (D Num)
  dadd : aexp Δ (D Num) → aexp Δ (D Num) → aexp Δ (D Num)
  dlam : ∀ {α₁ α₂}   → aexp ((D α₂) ∷ Δ) (D α₁) → aexp Δ (D (Fun α₂ α₁))
  dapp : ∀ {α₁ α₂}   → aexp Δ (D (Fun α₂ α₁)) → aexp Δ (D α₂) → aexp Δ (D α₁)


atint : Ctx → AType → Set
atint Γ SNum = ℕ
atint Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (atint Γ' α₁ → atint Γ' α₂)
atint Γ (D τ) =  exp Γ τ




∙< : ℕ → ℕ → Bool
∙< zero zero = false
∙< zero (suc n') = true
∙< (suc n) zero = false
∙< (suc n) (suc n') = ∙< n n'

--adjust the "De Bruijn Level index" for bounded variables
elevate↝ : (Γ : List Type ) → (n : ℕ) → ℕ
elevate↝ [] n = n
elevate↝ (x ∷ Γ) n = suc (elevate↝ Γ n) 

  

elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → exp Γ τ → exp Γ'' τ
elevate {Γ} {Γ'} Γ↝Γ'↝Γ'' (evar n pf) with ∙< n (Length Γ ∸ Length Γ')
elevate Γ↝Γ'↝Γ'' (evar n pf) | true = evar n {!!} --free variables
elevate {Γ' = Γ'} Γ↝Γ'↝Γ'' (evar n pf) | false = evar (elevate↝ Γ' n) {!!} --bounded variables
elevate Γ↝Γ'↝Γ'' (ecst x) = ecst x
elevate Γ↝Γ'↝Γ'' (eadd e e₁) = eadd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (elam e) = elam (elevate (extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (eapp e e₁) = eapp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
--note that 
--a)the idea that "variable id by 'De Bruijn Level' index stays unchanged under an extended envirionment" is 
--  not accurate in that only free variables are allowed to keep their ids unchanged while bounded variables 
--  have to adjust their ids to the the extended environment;
--b)note that this is actually the opposite of what we have to deal with by implementing "De Bruijn" index;
--c)now it is quite obvious that using "De Bruijn Level" index instead of simplifying the task at hand, further
--  complicate the matter: there is negative gain here!
 
atint↑ : ∀ {α Γ Γ'} → Γ ↝ Γ' → atint Γ α → atint Γ' α
atint↑ {SNum} Γ↝Γ' e = e
atint↑ {SFun α α₁} Γ↝Γ' e = λ Γ'↝Γ'' → e (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
atint↑ {D x} Γ↝Γ' e = elevate (refl Γ↝Γ') e 

data aenv : Ctx → ACtx → Set where
  [] : ∀ {Γ : Ctx} →  aenv Γ []
  cons : ∀ {Δ Γ} {α : AType} → atint Γ α → aenv Γ Δ → aenv Γ (α ∷ Δ)

aenv↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → aenv Γ Δ → aenv Γ' Δ
aenv↑ Γ↝Γ' [] = []
aenv↑ Γ↝Γ' (cons x env) = cons (atint↑ Γ↝Γ' x) (aenv↑ Γ↝Γ' env)

lookupvar : ∀ {α Γ Δ} → (n : ℕ ) → LookUp n Δ ≡ Some α → aenv Γ Δ → atint Γ α
lookupvar zero () []
lookupvar {α} {Γ} {α₁ ∷ Δ} zero x (cons x₁ aenv) with ℕ≡? 0 (Length Δ) 
lookupvar {α} {Γ} {.α ∷ Δ} zero refl (cons x₁ aenv) | true = x₁
lookupvar {α} {Γ} {α₁ ∷ Δ} zero x (cons x₁ aenv) | false = lookupvar zero x aenv
lookupvar (suc n₁) () []
lookupvar {α} {Γ} {α₁ ∷ Δ} (suc n₁) x (cons x₁ aenv) with ℕ≡? (suc n₁) (Length Δ) 
lookupvar {α} {Γ} {.α ∷ Δ} (suc n₁) refl (cons x₁ aenv) | true = x₁
lookupvar {α} {Γ} {α₁ ∷ Δ} (suc n₁) x (cons x₁ aenv) | false = lookupvar (suc n₁) x aenv

pe : ∀ {α : AType} {Δ : ACtx} {Γ : Ctx} → aexp Δ α → aenv Γ Δ → atint Γ α  
pe (var n x) aenv = lookupvar n x aenv
pe (scst x) aenv = x
pe (sadd e e₁) aenv = (pe e aenv) + (pe e₁ aenv)
pe (slam e) aenv = λ Γ↝Γ' → λ x → pe e (cons x (aenv↑ Γ↝Γ' aenv))
pe (sapp e e₁) aenv = pe e aenv refl (pe e₁ aenv)
pe (dcst x) aenv = ecst x
pe (dadd e e₁) aenv = eadd (pe e aenv) (pe e₁ aenv)
pe {D (Fun τ τ')} {Δ} {Γ} (dlam e) aenv = elam
                                              (pe e
                                               (cons {Γ = τ ∷ Γ} (evar {τ = τ} (Length Γ) this)
                                                (aenv↑ (extend refl) aenv)))
         where this : LookUp (Length Γ) (τ ∷ Γ) ≡ Some τ
               this rewrite lemma≡ {Type} {τ} {Γ} = refl
pe (dapp e e₁) aenv = eapp (pe e aenv) (pe e₁ aenv)