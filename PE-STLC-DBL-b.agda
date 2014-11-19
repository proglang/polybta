module PE-STLC-DBL-b where
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
atint Γ (D τ) =  ∀ {Γ'} → Γ ↝ Γ' → exp Γ' τ
 

atint↑ : ∀ {α Γ Γ'} → Γ ↝ Γ' → atint Γ α → atint Γ' α
atint↑ {SNum} Γ↝Γ' e = e
atint↑ {SFun α α₁} Γ↝Γ' e = λ Γ'↝Γ'' → e (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
atint↑ {D x} Γ↝Γ' e = λ Γ'↝Γ'' → e (lem-↝-trans Γ↝Γ' Γ'↝Γ'') 
    


data aenv : Ctx → ACtx → Set where
  [] : ∀ {Γ : Ctx} →  aenv Γ []
  cons : ∀ {Δ Γ} {α : AType} → atint Γ α → aenv Γ Δ → aenv Γ (α ∷ Δ)

 

aenv↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → aenv Γ Δ → aenv Γ' Δ
aenv↑ Γ↝Γ' [] = []
aenv↑  {Γ} {Γ'} {α ∷ Δ} Γ↝Γ' (cons x env) = cons (atint↑ {α} {Γ} {Γ'} Γ↝Γ' x) (aenv↑ Γ↝Γ' env)


Γ↝ : ∀ {A : Set} {Γ Γ' : List A} {τ : A} → (τ ∷ Γ) ↝ Γ' → Γ ↝ Γ'
Γ↝ refl = extend refl
Γ↝ (extend τ∷Γ↝Γ') = extend (Γ↝ τ∷Γ↝Γ')

 

∙< : ℕ → ℕ → Bool
∙< zero zero = false
∙< zero (suc n') = true
∙< (suc n) zero = false
∙< (suc n) (suc n') = ∙< n n'
  
  
∙<suc : ∀ {n : ℕ} → ∙< n (suc n) ≡ true
∙<suc {zero} = refl
∙<suc {suc n} = ∙<suc {n}

  
  
∙<truesuc : ∀ {n n' : ℕ} → ∙< n n' ≡ true → ∙< n (suc n') ≡ true
∙<truesuc {zero} {zero} ∙< = refl
∙<truesuc {zero} {suc n'} ∙< = refl
∙<truesuc {suc n} {zero} ()
∙<truesuc {suc n} {suc n'} ∙< = ∙<truesuc {n} {n'} ∙<

ℕ≡↝suc : ∀ {n n' : ℕ} → ∙< n n' ≡ true → ℕ≡? n n' ≡ false → ℕ≡? n (suc n') ≡ false
ℕ≡↝suc {zero} {zero} ∙< ()
ℕ≡↝suc {zero} {suc n'} ∙< ℕ≡?false = refl
ℕ≡↝suc {suc n} {zero} () ℕ≡?false
ℕ≡↝suc {suc n} {suc n'} ∙< ℕ≡?false = ℕ≡↝suc {n} {n'} ∙< ℕ≡?false

∙<↝ : ∀ {A : Set} {Γ Γ' : List A} {τ : A} → (τ ∷ Γ) ↝ Γ' → ∙< (Length Γ) (Length Γ') ≡ true
∙<↝ {Γ = Γ} refl rewrite ∙<suc {Length Γ} = refl
∙<↝ {Γ = Γ} {Γ' = τ' ∷ Γ'} {τ = τ} (extend τ∷Γ↝Γ') = ∙<truesuc {Length Γ} {Length Γ'} (∙<↝ τ∷Γ↝Γ')

ℕ≡false : ∀ {A : Set} {Γ : List A} → ℕ≡? (Length Γ) (suc (Length Γ)) ≡ false
ℕ≡false {A} {[]} = refl
ℕ≡false {A} {x ∷ Γ} = ℕ≡false {A} {Γ}

ℕ≡↝false : ∀ {A : Set} {Γ Γ' : List A} {τ : A} → (τ ∷ Γ) ↝ Γ' → ℕ≡? (Length Γ) (Length Γ') ≡ false   
ℕ≡↝false {A} {Γ} refl rewrite ℕ≡false {A} {Γ} = refl
ℕ≡↝false {Γ = Γ} {Γ' = τ' ∷ Γ'} {τ = τ} (extend τ∷Γ↝Γ') = ℕ≡↝suc {Length Γ} {Length Γ'} (∙<↝ τ∷Γ↝Γ') (ℕ≡↝false τ∷Γ↝Γ')


ℕ≡true : ∀ {A : Set} {Γ : List A} → ℕ≡? (Length Γ) (Length Γ) ≡ true
ℕ≡true {A} {[]} = refl
ℕ≡true {A} {x ∷ Γ} = ℕ≡true {A} {Γ}  


LemmaLookUp↝ : ∀ {A : Set} {Γ Γ' : List A} {τ : A} → (τ ∷ Γ) ↝ Γ' → Some τ ≡ LookUp (Length Γ) Γ'
LemmaLookUp↝ {A = Type} {Γ = Γ} refl rewrite ℕ≡true {Type} {Γ} = refl
LemmaLookUp↝ {A = Type} {Γ = Γ} {Γ' = τ' ∷ Γ'} {τ = τ} (extend τ∷Γ↝Γ') 
          rewrite ℕ≡true {Type} {Γ} | ℕ≡↝false {Type} {Γ} {Γ'} {τ} τ∷Γ↝Γ' = LemmaLookUp↝ τ∷Γ↝Γ'  

lookupvar : ∀ {α : AType} {Γ : Ctx} {Δ : ACtx} → (n : ℕ) → LookUp n Δ ≡ Some α → aenv Γ Δ → atint Γ α
lookupvar zero () []
lookupvar {α} {Γ} {α₁ ∷ Δ} zero x (cons x₁ aenv) with ℕ≡? 0 (Length Δ) 
lookupvar {α} {Γ} {.α ∷ Δ} zero refl (cons x₁ aenv) | true = x₁
lookupvar {α} {Γ} {α₁ ∷ Δ} zero x (cons x₁ aenv) | false = lookupvar zero x aenv
lookupvar (suc n) () []
lookupvar {α} {Γ} {α₁ ∷ Δ} (suc n) x (cons x₁ aenv) with ℕ≡? (suc n) (Length Δ) 
lookupvar {α} {Γ} {.α ∷ Δ} (suc n) refl (cons x₁ aenv) | true = x₁
lookupvar {α} {Γ} {α₁ ∷ Δ} (suc n) x (cons x₁ aenv) | false = lookupvar (suc n) x aenv

pe : ∀ {α : AType} {Δ : ACtx} {Γ : Ctx} → aexp Δ α → aenv Γ Δ → atint Γ α  
pe (var n x) aenv = lookupvar n x aenv
pe (scst x) aenv = x
pe (sadd e e₁) aenv = (pe e aenv) + (pe e₁ aenv)
pe (slam e) aenv = λ Γ↝Γ' → λ x → pe e (cons x (aenv↑ Γ↝Γ' aenv))
pe (sapp e e₁) aenv = pe e aenv refl (pe e₁ aenv)
pe (dcst x) aenv = λ Γ↝Γ' → ecst x
pe (dadd e e₁) aenv = λ Γ↝Γ' → eadd (pe e aenv Γ↝Γ') (pe e₁ aenv Γ↝Γ')
pe {D (Fun τ τ')} {Δ} {Γ} (dlam e) aenv = λ {Γ'} Γ↝Γ' 
            → elam (pe e (cons {Γ = τ ∷ Γ'} (λ {Γ''} Γ↝Γ'' → evar (Length Γ') (that {Γ'} {Γ''} Γ↝Γ'')) (aenv↑ (extend Γ↝Γ') aenv)) refl)
                where that : ∀ {Γ' Γ'' : Ctx} →  (τ ∷ Γ') ↝ Γ'' → LookUp (Length Γ') Γ'' ≡ Some τ
                      that {Γ'} {Γ''} τ∷Γ'↝Γ'' rewrite sym (LemmaLookUp↝ {Type} {Γ'} {Γ''} {τ} τ∷Γ'↝Γ'') = refl
pe (dapp e e₁) aenv = λ Γ↝Γ' → eapp (pe e aenv Γ↝Γ') (pe e₁ aenv Γ↝Γ')




--note: Using "De Bruijn Level" index does not simplify the specification
--1) "De Bruijn Level" index by a "reverse counting" scheme avoids the naming
--   of variable ids in case of an extended environment;
--2) however it comes at a price in the sense that there are additional lemmas
--   ,for instance [LemmaLookUp↝] is used to convince Agda that under such a
--   scheme there is no need to change variable ids under an extended environment;
--3) various lemmas as a result of "weakening Γ" are still present and in this regard
--   it does not really make a difference by implementing this alternative;
