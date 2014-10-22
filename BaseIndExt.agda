{- The base language with recursion on inductive types;
   simply typed lambda calculus with nats, addition, sums and products -}
module BaseIndExt where
open import Lib 
open Auxiliaries
open import Data.Unit 
open import Data.Bool
open import Data.Fin hiding (_+_)
open import Data.Vec hiding ( _∈_ )

-- Shape of inductive types
data Ty (n : ℕ) : Set where
 Hole : Ty n -- recursive occurrence
 Parm : Fin n → Ty n
 UNIT : Ty n
 Sum  : Ty n → Ty n → Ty n
 Prd  : Ty n → Ty n → Ty n
 
data Type : Set where
  UNIT : Type
  Num : Type
  Fun : Type → Type → Type
  Prd : Type → Type → Type
  Sum : Type → Type → Type
  Ind : ∀ {n} → Ty n → Vec Type n → Type
Ctx = List Type

-- Fill the holes in a Shape with a Type
fmap : ∀ {n} → Ty n → Vec Type n → Type → Type
fmap Hole v τ = τ
fmap (Parm i) v τ = lookup i v
fmap UNIT v τ = UNIT
fmap (Sum T T₁) v τ = Sum (fmap T v τ) (fmap T₁ v τ)
fmap (Prd T T₁) v τ = Prd (fmap T v τ) (fmap T₁ v τ)

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
  EFold : ∀ {n} → (T : Ty n) → (v : Vec Type n) → Exp Γ (fmap T v (Ind T v)) → Exp Γ (Ind T v)
  -- Eliminate a value of inductive type
  EFoldRec : ∀ {n τ} → (T : Ty n) → (v : Vec Type n) → Exp Γ (Ind T v) → Exp Γ (Fun (fmap T v τ) τ) → Exp Γ τ

-- Values of inductive types, in U T1 T2, T1 is the top-level type, T2
-- is the type of the current node
data U {n : ℕ} (v : Vec Set n) : Ty n → Ty n → Set where
  InHole : ∀ T → U v T T → U v T Hole
  UNIT   : ∀ T → U v T UNIT
  Left   : ∀ T T1 T2 → U v T T1 → U v T (Sum T1 T2)
  Right  : ∀ T T1 T2 → U v T T2 → U v T (Sum T1 T2)
  Pair   : ∀ T T1 T2 → U v T T1 → U v T T2 → U v T (Prd T1 T2)
  Parm   : ∀ T → (i : Fin n) → lookup i v → U v T (Parm i)



V : {n : ℕ} → Ty n → Vec Set n → Set 
V T v = U v T T

  
-- Type interpretation, extended for Ind
TInt : Type → Set
TInt' : ∀ {n} → Vec Type n → Vec Set n

TInt UNIT = ⊤
TInt Num = ℕ
TInt (Fun τ₁ τ₂) = TInt τ₁ → TInt τ₂
TInt (Prd τ₁ τ₂) = TInt τ₁ × TInt τ₂
TInt (Sum τ₁ τ₂) = TInt τ₁ ⊎ TInt τ₂
TInt (Ind T v) = V T (TInt' v)

TInt' [] = []
TInt' (τ ∷ τs) = TInt τ ∷ TInt' τs

lem-TInt : ∀ {n} (i : Fin n) (v : Vec Type n) → TInt (lookup i v) ≡ lookup i (TInt' v)
lem-TInt zero (x ∷ v) = refl
lem-TInt (suc i) (x ∷ v) = lem-TInt i v

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
UInt : ∀ {n} → Ty n → Vec Set n → Set → Set
UInt Hole v t = t
UInt UNIT v t = ⊤
UInt (Sum T1' T2') v t = UInt T1' v t ⊎ UInt T2' v t
UInt (Prd T1' T2') v t = UInt T1' v t × UInt T2' v t
UInt (Parm i) v t = lookup i v

urec  : ∀ {n} {T1 : Ty n} { t : Set } (v : Vec Set n) → U v T1 T1 → (UInt T1 v t → t) → t
urec' : ∀ {n} {T1 T2 : Ty n} { t : Set } (v : Vec Set n) → U v T1 T2 → (UInt T1 v t → t) → UInt T2 v t
urec v u alg = alg (urec' v u alg) 
urec' {T1} v (InHole _ u) alg = urec v u alg
urec' {T1} v (UNIT _) alg = tt
urec' {T1} v (Left _ T2 T3 u) alg = inj₁ (urec' v u alg)
urec' {T1} v (Right _ T2 T3 u) alg = inj₂ (urec' v u alg)
urec' {T1} v (Pair _ T2 T3 u u₁) alg = ( urec' v u alg , urec' v u₁ alg )
urec' {T1} v (Parm _ i x) alg = x

-- implements elimination
vrec : ∀ {n} {T : Ty n} {t : Set} (v : Vec Set n) → V T v → (UInt T v t → t) → t
vrec v u alg = urec v u alg

ufold' : ∀ {n} (T0 T : Ty n) (v : Vec Type n) → TInt (fmap T v (Ind T0 v)) → U (TInt' v) T0 T
ufold' T0 Hole v x = InHole T0 x
ufold' T0 UNIT v x = UNIT T0
ufold' T0 (Sum T T₁) v (inj₁ x) = Left T0 T T₁ (ufold' T0 T v x)
ufold' T0 (Sum T T₁) v (inj₂ y) = Right T0 T T₁ (ufold' T0 T₁ v y)
ufold' T0 (Prd T T₁) v x = Pair T0 T T₁ (ufold' T0 T v (proj₁ x)) (ufold' T0 T₁ v (proj₂ x))
ufold' T0 (Parm i) v x rewrite lem-TInt i v = Parm T0 i x

-- implements construction
ufold : ∀ {n} (T : Ty n) (v : Vec Type n) → TInt (fmap T v (Ind T v)) → TInt (Ind T v)
ufold T v x = ufold' T T v x

-- aux lemma needed to type-check elimination
lem-uint-tint : ∀ {n} (T : Ty n) (v : Vec Type n) τ → UInt T (TInt' v) (TInt τ) ≡ TInt (fmap T v τ)
lem-uint-tint Hole v τ = refl
lem-uint-tint UNIT v τ = refl
lem-uint-tint (Sum T T₁) v τ rewrite lem-uint-tint T v τ | lem-uint-tint T₁ v τ = refl
lem-uint-tint (Prd T T₁) v τ rewrite lem-uint-tint T v τ | lem-uint-tint T₁ v τ = refl
lem-uint-tint (Parm i) v τ rewrite lem-TInt i v = refl

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
ev (EFold T v e) ρ = ufold T v (ev e ρ)
ev (EFoldRec {τ = τ} T v e e₁) ρ = urec (TInt' v) (ev e ρ) f
  where f : UInt T (TInt' v) (TInt τ) → TInt τ
        f x rewrite lem-uint-tint T v τ = ev e₁ ρ x


{-
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

eplus : ∀ {Γ} → Exp Γ (Fun UNat (Fun UNat UNat))
eplus = ELam (ELam (EFoldRec (EVar (tl hd)) cases))
  where cases = ELam (ECase (EVar hd)
                            (EVar (tl (tl hd)))    -- zero case, use e2
                            (EApp esuc (EVar hd))) -- recursive case

test-eplus : ev (EApp (EApp eplus (fromℕ 31)) (fromℕ 11)) [] ≡ ev (fromℕ 42) []
test-eplus = refl

-- TODO:
UNatListTy : Ty
UNatListTy = Sum UNIT (Prd UNatTy Hole)
UNatList : Type
UNatList = Ind UNatListTy

-}
