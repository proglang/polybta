module PE-STLC-DBL where
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

--simple two-level terms

--"De Bruijn Level" index
--one possibility
-- module DBL-a where
    
--   Length : ∀ {A : Set} → List A → ℕ
--   Length [] = zero
--   Length (x ∷ ls) = suc (Length ls) 



--   --"De Bruijn Level" terms
--   data exp (Γ : Ctx) : Type → Set where
--     evar : ∀ {τ} → τ ∈ Γ → exp Γ τ
--     ecst : ℕ → exp Γ Num
--     eadd : exp Γ Num → exp Γ Num -> exp Γ Num
--     elam : ∀ {τ τ'} → exp (τ ∷ Γ) τ' → exp Γ (Fun τ τ')
--     eapp : ∀ {τ τ'} → exp Γ (Fun τ τ')  → exp Γ τ → exp Γ τ'

--   data aexp (Δ : ACtx) : AType → Set where
--     var : ∀ {α} → α ∈ Δ → aexp Δ α
--     scst : ℕ → aexp Δ SNum
--     sadd : aexp Δ SNum → aexp Δ SNum → aexp Δ SNum
--     slam : ∀ {α₁ α₂}   → aexp (α₂ ∷ Δ) α₁ → aexp Δ (SFun α₂ α₁)
--     sapp : ∀ {α₁ α₂}   → aexp Δ (SFun α₂ α₁) → aexp Δ α₂ → aexp Δ α₁
--     dcst : ℕ → aexp Δ (D Num)
--     dadd : aexp Δ (D Num) → aexp Δ (D Num) → aexp Δ (D Num)
--     dlam : ∀ {α₁ α₂}   → aexp ((D α₂) ∷ Δ) (D α₁) → aexp Δ (D (Fun α₂ α₁))
--     dapp : ∀ {α₁ α₂}   → aexp Δ (D (Fun α₂ α₁)) → aexp Δ (D α₂) → aexp Δ (D α₁)

--   atint : Ctx → AType → Set
--   atint Γ SNum = ℕ
--   atint Γ (SFun α₁ α₂) = atint Γ α₁ → atint Γ α₂
--   atint Γ (D τ) =  exp Γ τ
    
--   data aenv : Ctx → ACtx → Set where
--     [] : ∀ {Γ : Ctx} →  aenv Γ []
--     cons : ∀ {Δ Γ} {α : AType} → atint Γ α → aenv Γ Δ → aenv Γ (α ∷ Δ)

--   pe : ∀ {α : AType} {Δ : ACtx} {Γ : Ctx} → aexp Δ α → aenv Γ Δ → atint Γ α
--   pe (var x) aenv = {!!}
--   pe (scst x) aenv = {!!}
--   pe (sadd e e₁) aenv = {!!}
--   pe (slam e) aenv = λ x → pe e (cons x aenv)
--   pe (sapp e e₁) aenv = {!!}
--   pe (dcst x) aenv = {!!}
--   pe (dadd e e₁) aenv = {!!}
--   pe (dlam e) aenv = elam (pe e {!!})
--   pe (dapp e e₁) aenv = {!!}

  --partial evaluation
  --type interpreter
 --  data _↝_ {A : Set} : List A → List A → Set where
--     refl   : {l : List A} → l ↝ l
--     extend : ∀ {l₁ l₂ τ}  → l₁ ↝ l₂ → l₁ ↝ (l₂ ++ τ)

--   data _↝_↝_ {A : Set} : List A → List A → List A → Set where
--     refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ''
--     extend : ∀ {Γ Γ' Γ'' τ} →
--                Γ ↝ Γ' ↝ Γ'' → (Γ ++ τ) ↝ (Γ' ++ τ) ↝ (Γ'' ++ τ)
 
--   lem-↝-trans : ∀ {A : Set}{Γ Γ' Γ'' : List A} → Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
--   lem-↝-trans Γ↝Γ' refl = Γ↝Γ'
--   lem-↝-trans Γ↝Γ' (extend Γ'↝Γ'') = extend (lem-↝-trans Γ↝Γ' Γ'↝Γ'')

--   atint : Ctx → AType → Set
--   atint Γ SNum = ℕ
--   atint Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (atint Γ' α₁ → atint Γ' α₂)
--   atint Γ (D τ) =  exp Γ τ
    
--   --environment
--   data aenv : Ctx → ACtx → Set where
--     [] : ∀ {Γ : Ctx} →  aenv Γ []
--     cons : ∀ {Δ Γ} {α : AType} → atint Γ α → aenv Γ Δ → aenv Γ (Δ ++ α)

--   elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
--   elevate-var refl τ∈Γ = τ∈Γ
--   elevate-var (extend Γ↝Γ') τ∈Γ = tl (elevate-var Γ↝Γ' τ∈Γ)

--   elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ'' 
--   elevate-var2 (refl x) τ∈Γ = elevate-var x τ∈Γ
--   elevate-var2 (extend Γ↝Γ'↝Γ'') τ∈Γ = {!!}


--   elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → exp Γ τ → exp Γ'' τ
--   elevate Γ↝Γ'↝Γ'' (evar x) = evar (elevate-var2 Γ↝Γ'↝Γ'' x)
--   elevate Γ↝Γ'↝Γ'' (ecst x) = ecst x
--   elevate Γ↝Γ'↝Γ'' (eadd e e₁) = eadd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
--   elevate Γ↝Γ'↝Γ'' (elam e) = elam (elevate (extend Γ↝Γ'↝Γ'') e)
--   elevate Γ↝Γ'↝Γ'' (eapp e e₁) = eapp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)


--   int↑ : ∀ {Γ Γ'} α → Γ ↝ Γ' → atint Γ α → atint Γ' α 
--   int↑ SNum p v = v
--   int↑ (SFun x x₁) Γ↝Γ' v = λ Γ'↝Γ'' → v (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
--   int↑ (D x₁) Γ↝Γ' v = elevate (refl Γ↝Γ') v

--   env↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → aenv Γ Δ → aenv Γ' Δ
--   env↑ Γ↝Γ' [] = []
--   env↑ Γ↝Γ' (cons {α = α} x env) =  cons (int↑ α Γ↝Γ' x)  (env↑ Γ↝Γ' env)

--   consD : ∀ {Γ Δ} τ → aenv Γ Δ → aenv (Γ ++ τ ) (Δ ++ (D τ))  
--   consD {Γ} {Δ} τ aenv = (cons {Δ = Δ} {Γ = Γ ++ τ} {α = D τ} (evar (hd {x = τ} {xs = Γ})) (env↑ (extend refl) aenv))

--   --partial evaluator
--   pe : ∀ {α : AType} {Δ : ACtx} {Γ : Ctx} → aexp Δ α → aenv Γ Δ → atint Γ α
--   pe (var x) aenv = {!!}
--   pe (scst x) aenv = x
--   pe (sadd e e₁) aenv = (pe e aenv) + (pe e₁ aenv)
--   pe (slam e) aenv =  λ Γ↝Γ' → λ y → pe e (cons y (env↑ Γ↝Γ' aenv))
--   pe (sapp e e₁) aenv = pe e aenv refl (pe e₁ aenv)
--   pe (dcst x) aenv = ecst x
--   pe (dadd e e₁) aenv = eadd (pe e aenv) (pe e₁ aenv)
--   pe {D (Fun τ τ')} {Δ = Δ} {Γ} (dlam e) aenv = elam (pe e (consD τ aenv))
--   pe (dapp e e₁) aenv = eapp (pe e aenv) (pe e₁ aenv)

--an alternative specification
module DBL-b where
  
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

  
  --note:
  --[atint] differs only from [atint'] in its 
  --interpretation of the dynamic types
  atint : Ctx → AType → Set
  atint Γ SNum = ℕ
  atint Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (atint Γ' α₁ → atint Γ' α₂)
  atint Γ (D τ) =  exp Γ τ

  

  atint' : Ctx → AType → Set
  atint' Γ SNum = ℕ
  atint' Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → (atint' Γ' α₁ → atint' Γ' α₂)
  atint' Γ (D τ) =  ∀ {Γ'} → Γ ↝ Γ' → exp Γ' τ
  
  -- atint'' : Ctx → AType → Set
  -- atint'' Γ SNum = ℕ
  -- atint'' Γ (SFun α₁ α₂) = atint'' Γ α₁ → atint'' Γ α₂
  -- atint'' Γ (D τ) = exp Γ τ

  -- atint↑'' : ∀ {α Γ τ} → atint'' Γ α → atint'' (τ ∷ Γ) α
  -- atint↑'' {SNum} v = v
  -- atint↑'' {SFun α α₁} v = {!!}
  -- atint↑'' {D x} v = {!!}
  
  ∙< : ℕ → ℕ → Bool
  ∙< zero zero = false
  ∙< zero (suc n') = true
  ∙< (suc n) zero = false
  ∙< (suc n) (suc n') = ∙< n n'
  

  --adjust the "De Bruijn Level index" for bounded variables
  elevate↝ : (Γ : List Type ) → (n : ℕ) → ℕ
  elevate↝ [] n = n
  elevate↝ (x ∷ Γ) n = suc (elevate↝ Γ n) 

  ------------------------------------------------------------------------------------
  --now define "De Bruijn Level" index as the opposite of "De Bruijn" index
  DBL2DB : ∀ {n : ℕ} {τ : Type} {Γ : List Type} → LookUp n Γ ≡ Some τ → ℕ
  DBL2DB {n} {τ} {Γ} pf = Length Γ ∸ suc n

  --lookup function of "De Bruijn" index
  lookup : ∀ {A : Set} → ℕ → List A → Option A
  lookup n [] = Nothing
  lookup zero (x ∷ l) = Some x
  lookup (suc n) (x ∷ l) = lookup n l

  --now define "De Bruijn Level" index as the opposite of "De Bruijn" index
  DB2DBL : ∀ {n : ℕ} {τ : Type} {Γ : List Type} → lookup n Γ ≡ Some τ → ℕ
  DB2DBL = {!!}

  --equivalence between two schemes
  DBLDB≡ : ∀ {n n' : ℕ } {τ : Type} {Γ : List Type} → (pf : lookup n' Γ ≡ Some τ) 
             → DB2DBL {n'} {τ} {Γ} pf ≡ n →  LookUp n Γ ≡ Some τ
  DBLDB≡ = {!!}

  elevate-var' : ∀ {Γ Γ' : List Type} → Γ ↝ Γ' → ℕ → ℕ
  elevate-var' refl n = n
  elevate-var' (extend Γ↝Γ') n = suc (elevate-var' Γ↝Γ' n)

  elevate-var2' : ∀ {Γ Γ' Γ''} → Γ ↝ Γ' ↝ Γ'' → ℕ → ℕ 
  elevate-var2' (refl x) x₁ = elevate-var' x x₁
  elevate-var2' (extend Γ↝Γ'↝Γ'') zero = zero
  elevate-var2' (extend Γ↝Γ'↝Γ'') (suc x) = suc (elevate-var2' Γ↝Γ'↝Γ'' x)
  
  elevate' : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → exp Γ τ → exp Γ'' τ
  elevate' {Γ} {Γ'} {Γ''} {τ} Γ↝Γ'↝Γ'' (evar n x) = evar (elevate-var2' Γ↝Γ'↝Γ'' (DBL2DB {n} {τ} {Γ} x)) 
                                                    {!!}
  elevate' Γ↝Γ'↝Γ'' (ecst x) = {!!}
  elevate' Γ↝Γ'↝Γ'' (eadd e e₁) = {!!}
  elevate' Γ↝Γ'↝Γ'' (elam e) = {!!}
  elevate' Γ↝Γ'↝Γ'' (eapp e e₁) = {!!}

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

  atint↑' : ∀ {α Γ Γ'} → Γ ↝ Γ' → atint' Γ α → atint' Γ' α
  atint↑' {SNum} Γ↝Γ' e = e
  atint↑' {SFun α α₁} Γ↝Γ' e = λ Γ'↝Γ'' → e (lem-↝-trans Γ↝Γ' Γ'↝Γ'')
  atint↑' {D x} Γ↝Γ' e = λ Γ'↝Γ'' → e (lem-↝-trans Γ↝Γ' Γ'↝Γ'') 
    
  data aenv : Ctx → ACtx → Set where
    [] : ∀ {Γ : Ctx} →  aenv Γ []
    cons : ∀ {Δ Γ} {α : AType} → atint Γ α → aenv Γ Δ → aenv Γ (α ∷ Δ)

  data aenv' : Ctx → ACtx → Set where
    [] : ∀ {Γ : Ctx} →  aenv' Γ []
    cons' : ∀ {Δ Γ} {α : AType} → atint' Γ α → aenv' Γ Δ → aenv' Γ (α ∷ Δ)

  -- data aenv'' : Ctx → ACtx → Set where
  --   [] : ∀ {Γ : Ctx} →  aenv'' Γ []
  --   cons'' : ∀ {Δ Γ} {α : AType} → atint'' Γ α → aenv'' Γ Δ → aenv'' Γ (α ∷ Δ)

  -- data Aenv : Ctx → ACtx → Set where
  --   [] : Aenv [] []
  --   cons : ∀ {Δ } {α : AType} → atint (map Δ)  α → aenv Γ Δ → aenv Γ (α ∷ Δ)

  aenv↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → aenv Γ Δ → aenv Γ' Δ
  aenv↑ Γ↝Γ' [] = []
  aenv↑ Γ↝Γ' (cons x env) = cons (atint↑ Γ↝Γ' x) (aenv↑ Γ↝Γ' env)

  aenv↑' : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → aenv' Γ Δ → aenv' Γ' Δ
  aenv↑' Γ↝Γ' [] = []
  aenv↑'  {Γ} {Γ'} {α ∷ Δ} Γ↝Γ' (cons' x env) = cons' (atint↑' {α} {Γ} {Γ'} Γ↝Γ' x) (aenv↑' Γ↝Γ' env)


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
  pe {D (Fun τ τ')} {Δ} {Γ} (dlam e) aenv = {!elam (pe e (cons {Γ = τ ∷ Γ} (evar {τ = τ} (Length Γ) this) (aenv↑ (extend refl)  aenv)))!}
         where this : LookUp (Length Γ) (τ ∷ Γ) ≡ Some τ
               this rewrite lemma≡ {Type} {τ} {Γ} = refl
  pe (dapp e e₁) aenv = eapp (pe e aenv) (pe e₁ aenv)

  Γ↝ : ∀ {A : Set} {Γ Γ' : List A} {τ : A} → (τ ∷ Γ) ↝ Γ' → Γ ↝ Γ'
  Γ↝ refl = extend refl
  Γ↝ (extend τ∷Γ↝Γ') = extend (Γ↝ τ∷Γ↝Γ')

  -- ∙< : ℕ → ℕ → Bool
  -- ∙< zero zero = false
  -- ∙< zero (suc n') = true
  -- ∙< (suc n) zero = false
  -- ∙< (suc n) (suc n') = ∙< n n'
  
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

  ℕ≡↝false : ∀ {A : Set} {Γ Γ' : List A} {τ : A} → (τ ∷ Γ) ↝ Γ' → ℕ≡? (Length Γ) (Length Γ') ≡ false   
  ℕ≡↝false {A} {Γ} refl rewrite ℕ≡false {A} {Γ} = refl
  ℕ≡↝false {Γ = Γ} {Γ' = τ' ∷ Γ'} {τ = τ} (extend τ∷Γ↝Γ') = ℕ≡↝suc {Length Γ} {Length Γ'} (∙<↝ τ∷Γ↝Γ') (ℕ≡↝false τ∷Γ↝Γ')


  LemmaLookUp↝ : ∀ {A : Set} {Γ Γ' : List A} {τ : A} → (τ ∷ Γ) ↝ Γ' → Some τ ≡ LookUp (Length Γ) Γ'
  LemmaLookUp↝ {A = Type} {Γ = Γ} refl rewrite ℕ≡true {Type} {Γ} = refl
  LemmaLookUp↝ {A = Type} {Γ = Γ} {Γ' = τ' ∷ Γ'} {τ = τ} (extend τ∷Γ↝Γ') 
          rewrite ℕ≡true {Type} {Γ} | ℕ≡↝false {Type} {Γ} {Γ'} {τ} τ∷Γ↝Γ' = LemmaLookUp↝ τ∷Γ↝Γ'  

  lookupvar' : ∀ {α : AType} {Γ : Ctx} {Δ : ACtx} → (n : ℕ) → LookUp n Δ ≡ Some α → aenv' Γ Δ → atint' Γ α
  lookupvar' zero () []
  lookupvar' {α} {Γ} {α₁ ∷ Δ} zero x (cons' x₁ aenv) with ℕ≡? 0 (Length Δ) 
  lookupvar' {α} {Γ} {.α ∷ Δ} zero refl (cons' x₁ aenv) | true = x₁
  lookupvar' {α} {Γ} {α₁ ∷ Δ} zero x (cons' x₁ aenv) | false = lookupvar' zero x aenv
  lookupvar' (suc n) () []
  lookupvar' {α} {Γ} {α₁ ∷ Δ} (suc n) x (cons' x₁ aenv) with ℕ≡? (suc n) (Length Δ) 
  lookupvar' {α} {Γ} {.α ∷ Δ} (suc n) refl (cons' x₁ aenv) | true = x₁
  lookupvar' {α} {Γ} {α₁ ∷ Δ} (suc n) x (cons' x₁ aenv) | false = lookupvar' (suc n) x aenv

  pe' : ∀ {α : AType} {Δ : ACtx} {Γ : Ctx} → aexp Δ α → aenv' Γ Δ → atint' Γ α  
  pe' (var n x) aenv = lookupvar' n x aenv
  pe' (scst x) aenv = x
  pe' (sadd e e₁) aenv = (pe' e aenv) + (pe' e₁ aenv)
  pe' (slam e) aenv = λ Γ↝Γ' → λ x → pe' e (cons' x (aenv↑' Γ↝Γ' aenv))
  pe' (sapp e e₁) aenv = pe' e aenv refl (pe' e₁ aenv)
  pe' (dcst x) aenv = λ Γ↝Γ' → ecst x
  pe' (dadd e e₁) aenv = λ Γ↝Γ' → eadd (pe' e aenv Γ↝Γ') (pe' e₁ aenv Γ↝Γ')
  pe' {D (Fun τ τ')} {Δ} {Γ} (dlam e) aenv = λ {Γ'} Γ↝Γ' 
            → elam (pe' e (cons' {Γ = τ ∷ Γ'} (λ {Γ''} Γ↝Γ'' → evar (Length Γ') (that {Γ'} {Γ''} Γ↝Γ'')) (aenv↑' (extend Γ↝Γ') aenv)) refl)
                where that : ∀ {Γ' Γ'' : Ctx} →  (τ ∷ Γ') ↝ Γ'' → LookUp (Length Γ') Γ'' ≡ Some τ
                      that {Γ'} {Γ''} τ∷Γ'↝Γ'' rewrite sym (LemmaLookUp↝ {Type} {Γ'} {Γ''} {τ} τ∷Γ'↝Γ'') = refl
  pe' (dapp e e₁) aenv = λ Γ↝Γ' → eapp (pe' e aenv Γ↝Γ') (pe' e₁ aenv Γ↝Γ')

  -- pe'' : ∀ {α : AType} {Δ : ACtx} {Γ : Ctx} → aexp Δ α → aenv'' Γ Δ → atint'' Γ α  
  -- pe'' (var n x) aenv = {!!}
  -- pe'' (scst x) aenv = {!!}
  -- pe'' (sadd e e₁) aenv = {!!}
  -- pe'' (slam e) aenv = λ x → pe'' e (cons'' x aenv)
  -- pe'' (sapp e e₁) aenv = {!!}
  -- pe'' (dcst x) aenv = {!!}
  -- pe'' (dadd e e₁) aenv = {!!}
  -- pe'' (dlam e) aenv = elam (pe'' e {!!})
  -- pe'' (dapp e e₁) aenv = {!!}


--note: Using "De Bruijn Level" index does not simplify the specification
--1) "De Bruijn Level" index by a "reverse counting" scheme avoids the naming
--   of variable ids in case of an extended environment;
--2) however it comes at a price in the sense that there are additional lemmas
--   ,for instance [LemmaLookUp↝] is used to convince Agda that under such a
--   scheme there is no need to change variable ids under an extended environment;
--3) various lemmas as a result of "weakening Γ" are still present and in this regard
--   it does not really make a difference by implementing this alternative;
--4) the reason why "weakening Γ" is introduced is due to the evaluation of the
--   "dynamic function type" term which are typed under two environments Γ and Δ;
--5) when evaluating the function body, typing environment Γ is extended and it is
--   necessary to pass over a  "weakened" environment [aenv] to the evaluator and 
--   therefore all lemmas resulting from it have to be proved;  

