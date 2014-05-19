{- The base language with recursion on inductive types;
   simply typed lambda calculus with nats, addition, sums and products -}
module BaseInd where
open import Lib
open import Data.Unit 
open import Data.Bool

-- Shape of inductive types
data Ty : Set where
 Hole : Ty -- recursive occurence
 UNIT : Ty
 Sum : Ty → Ty → Ty
 Prd : Ty → Ty → Ty
 
data Type : Set where
  UNIT : Type
  Num : Type
  Fun : Type → Type → Type
  Prd : Type → Type → Type
  Sum : Type → Type → Type
  Ind : Ty → Type
Ctx = List Type

-- Fill the holes in a Shape with a Type
fmap : Ty → Type → Type
fmap Hole τ = τ
fmap UNIT τ = UNIT
fmap (Sum T T₁) τ = Sum (fmap T τ) (fmap T₁ τ)
fmap (Prd T T₁) τ = Prd (fmap T τ) (fmap T₁ τ)

data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ETT : Exp Γ UNIT
  ECst : ℕ → Exp Γ Num
  ESuc : Exp Γ Num → Exp Γ Num
  ERec : ∀ {τ} → Exp Γ Num → Exp Γ (Fun (Sum UNIT τ) τ) → Exp Γ τ
  EAdd : Exp Γ Num → Exp Γ Num → Exp Γ Num
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ') → Exp Γ τ → Exp Γ τ'
  EPair : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (Prd τ τ')
  EFst :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ
  ESnd :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ'
  EInl :  ∀ {τ τ'} → Exp Γ τ → Exp Γ (Sum τ τ')
  EInr :  ∀ {τ τ'} → Exp Γ τ' → Exp Γ (Sum τ τ')
  ECase : ∀ {τ τ' τ''} → Exp Γ (Sum τ τ') →
          Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''
  -- Construct a value of inductive type
  EFold : ∀ {T} → Exp Γ (fmap T (Ind T)) → Exp Γ (Ind T)
  -- Eliminate a value of inductive type
  EFoldRec : ∀ {τ T} → Exp Γ (Ind T) → Exp Γ (Fun (fmap T τ) τ) → Exp Γ τ


-- Values of inductive types, in U T1 T2, T1 is the top-level type, T2
-- is the type of the current node
data U : Ty → Ty → Set where
  InHole : ∀ T → U T T → U T Hole
  UNIT : ∀ T → U T UNIT
  Left : ∀ T T1 T2 → U T T1 → U T (Sum T1 T2)
  Right : ∀ T T1 T2 → U T T2 → U T (Sum T1 T2)
  Pair : ∀ T T1 T2 →  U T T1 → U T T2 → U T (Prd T1 T2)

V : Ty → Set 
V T = U T T
  
-- Type interpretation, extended for Ind
TInt : Type → Set
TInt UNIT = ⊤
TInt Num = ℕ
TInt (Fun τ₁ τ₂) = TInt τ₁ → TInt τ₂
TInt (Prd τ₁ τ₂) = TInt τ₁ × TInt τ₂
TInt (Sum τ₁ τ₂) = TInt τ₁ ⊎ TInt τ₂
TInt (Ind T) = V T

data Env : Ctx → Set where 
  [] : Env []
  _∷_ : ∀ {τ Γ} → TInt τ → Env Γ → Env (τ ∷ Γ)

lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → TInt τ
lookupE hd (x ∷ ρ) = x
lookupE (tl v) (_ ∷ ρ) = lookupE v ρ


-- Some examples for interpreting recursion, for inspiration
natrec : ∀ { t : Set } → ℕ → ((⊤ ⊎ t) → t) → t
natrec zero vs = vs (inj₁ tt) 
natrec (suc n) vs = vs (inj₂ (natrec n vs)) 

unitrec : ∀ {t : Set } → ⊤ → (⊤ → t) → t
unitrec tt v = v tt

boolrec : ∀ {t : Set } → Bool → (⊤ ⊎ ⊤ → t) → t
boolrec true v = v (inj₁ tt)
boolrec false v = v (inj₂ tt)

listrec : ∀ {t : Set } → List ℕ → (⊤ ⊎ (ℕ × t) → t) → t
listrec [] v = v (inj₁ tt)
listrec (x ∷ l) v = v (inj₂ (x , listrec l v))

-- Interpretation of Shapes given an interpreted type
UInt : Ty → Set → Set
UInt Hole t = t
UInt UNIT t = ⊤
UInt (Sum T1' T2') t = UInt T1' t ⊎ UInt T2' t
UInt (Prd T1' T2') t = UInt T1' t × UInt T2' t

urec  : ∀ {T1 : Ty} { t : Set } → U T1 T1 → (UInt T1 t → t) → t
urec' : ∀ {T1 T2 : Ty} { t : Set } → U T1 T2 → (UInt T1 t → t) → UInt T2 t
urec u v = v (urec' u v) 
urec' {T1} (InHole .T1 u) v = urec u v
urec' {T1} (UNIT .T1) v = tt
urec' {T1} (Left .T1 T2 T3 u) v = inj₁ (urec' u v)
urec' {T1} (Right .T1 T2 T3 u) v = inj₂ (urec' u v)
urec' {T1} (Pair .T1 T2 T3 u u₁) v = ( urec' u v , urec' u₁ v )

-- implements elimination
vrec : ∀ {T : Ty} {t : Set} → V T → (UInt T t → t) → t
vrec u v = urec u v

ufold' : (T0 T : Ty) → TInt (fmap T (Ind T0)) → U T0 T
ufold' T0 Hole v = InHole T0 v
ufold' T0 UNIT v = UNIT T0
ufold' T0 (Sum T T₁) (inj₁ x) = Left T0 T T₁ (ufold' T0 T x)
ufold' T0 (Sum T T₁) (inj₂ y) = Right T0 T T₁ (ufold' T0 T₁ y)
ufold' T0 (Prd T T₁) v = Pair T0 T T₁ (ufold' T0 T (proj₁ v)) (ufold' T0 T₁ (proj₂ v))

-- implements construction
ufold : (T : Ty) → TInt (fmap T (Ind T)) → TInt (Ind T)
ufold T v = ufold' T T v

-- aux lemma needed to type-check elimination
lem-uint-tint : ∀ T τ → UInt T (TInt τ) ≡ TInt (fmap T τ)
lem-uint-tint Hole τ = refl
lem-uint-tint UNIT τ = refl
lem-uint-tint (Sum T T₁) τ rewrite lem-uint-tint T τ | lem-uint-tint T₁ τ = refl
lem-uint-tint (Prd T T₁) τ rewrite lem-uint-tint T τ | lem-uint-tint T₁ τ = refl

ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
ev (EVar v) ρ = lookupE v ρ
ev (ETT) ρ = tt
ev (ECst x) ρ = x
ev (ESuc e) ρ = suc (ev e ρ)
ev (ERec e es) ρ = natrec (ev e ρ) (ev es ρ) 
ev (EAdd e f) ρ = ev e ρ + ev f ρ
ev (ELam e) ρ = λ x → ev e (x ∷ ρ)
ev (EApp e f) ρ = ev e ρ (ev f ρ)
ev (EPair e f) ρ = ev e ρ , ev f ρ
ev (EFst e) ρ = proj₁ (ev e ρ)
ev (ESnd e) ρ = proj₂ (ev e ρ)
ev (EInl e) ρ = inj₁ (ev e ρ)
ev (EInr e) ρ = inj₂ (ev e ρ)
ev (ECase e e₁ e₂) ρ with ev e ρ
... | inj₁ v = ev e₁ (v ∷ ρ)
... | inj₂ v = ev e₂ (v ∷ ρ)
ev (EFold {T} e) ρ = ufold T (ev e ρ)
ev (EFoldRec {τ} {T} e e₁) ρ = urec (ev e ρ) f
  where f : UInt T (TInt τ)  → TInt τ
        f v rewrite lem-uint-tint T τ = ev e₁ ρ v

--------------------------
-- Rec Examples
------------------------

-- Natural numbers:
UNatTy : Ty
UNatTy = Sum UNIT Hole

UNat : Type
UNat = Ind UNatTy

-- zero and successor function

--helper
fromℕ' : ∀ {Γ} → ℕ → Exp Γ UNat
fromℕ' = fold mzero msuc
  where -- meta-zero and -succ
      mzero : ∀ {Γ} → Exp Γ UNat
      mzero = EFold (EInl ETT) 

      msuc : ∀ {Γ} → Exp Γ UNat → Exp Γ UNat
      msuc e = EFold (EInr e)

fromℕ : ∀ {Γ} → ℕ → Exp Γ UNat
fromℕ = fold mzero msuc
  where -- meta-zero and -succ
      mzero : ∀ {Γ} → Exp Γ UNat
      mzero = EFold (EInl ETT) 

      msuc : ∀ {Γ} → Exp Γ UNat → Exp Γ UNat
      msuc e = EFold (EInr e)

ezero : ∀ {Γ} → Exp Γ UNat
ezero = EFold (EInl ETT) 

esuc : ∀ {Γ} → Exp Γ (Fun UNat UNat)
esuc = ELam (EFold (EInr (EVar hd)))

epred : ∀ {Γ} → Exp Γ (Fun UNat UNat)
epred = ELam ((EFoldRec (EVar hd) (ELam (ECase (EVar hd) {!EInl ?!} {!!})) ))

eplus : ∀ {Γ} → Exp Γ (Fun UNat (Fun UNat UNat))
eplus = ELam (ELam (EFoldRec (EVar (tl hd)) cases))
  where cases = ELam (ECase (EVar hd)
                            (EVar (tl (tl hd)))    -- zero case, use e2
                            (EApp esuc (EVar hd))) -- recursive case
                            
TBool : Type
TBool = Sum UNIT UNIT

ele : ∀ {Γ} → Exp Γ (Fun (Prd UNat UNat) (TBool))
ele = ELam {! !}

test-eplus : ev (EApp (EApp eplus (fromℕ 31)) (fromℕ 11)) [] ≡ ev (fromℕ 42) []
test-eplus = refl

UBinTy : Ty
UBinTy = Sum UNIT (Prd Hole Hole)
UBin : Type
UBin = Ind UBinTy


-- helper
leaf : ∀ {Γ} → Exp Γ UBin
leaf = EFold (EInl ETT)

node : ∀ {Γ} → Exp Γ UBin → Exp Γ UBin → Exp Γ UBin
node e1 e2 = EFold (EInr (EPair e1 e2))


-- defs
eleaf = leaf

enode : ∀ {Γ} → Exp Γ (Fun (Prd (UBin) (UBin)) (UBin))
enode = λ {Γ} → ELam (EFold (EInr (EVar hd)))



