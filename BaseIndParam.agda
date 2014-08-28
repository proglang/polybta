{- The base language with recursion on inductive types;
   simply typed lambda calculus with nats, addition, sums and products -}
module BaseIndParam where
open import Lib
open import Data.Unit using (⊤; tt)
open import Data.Bool

-- Shape of inductive types
mutual 
  data Ty : Set where
   Hole : Ty -- recursive occurence
   UNIT : Ty
   Sum : Ty → Ty → Ty
   Prd : Ty → Ty → Ty
   Cst : Type → Ty
   
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
fmap (Cst τ) _ = τ
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
open import Data.Empty
TInt : (U' : Set) → Type → Set
UInt : (U' : Set) → Ty → Set → Set
data U (U' : Set) (T : Ty) :  -- nesting level of Vals
                          Ty → Set where
  InHole : U U' T T → U U' T Hole
  UNIT : U U' T UNIT
  Left : ∀ T1 T2 → U U' T T1 → U U' T (Sum T1 T2)
  Right : ∀ T1 T2 → U U' T T2 → U U' T (Sum T1 T2)
  Pair : ∀ T1 T2 →  U U' T T1 → U U' T T2 → U U' T (Prd T1 T2)
  Val : ∀ {τ} → U' → U U' T (Cst τ)

-- Type interpretation, extended for Ind
V : Set → Ty  → Set 
V U' T = U U' T T
  
TInt U' UNIT = ⊤
TInt U' Num = ℕ
TInt U' (Fun τ₁ τ₂) = TInt U' τ₁ → TInt U' τ₂
TInt U' (Prd τ₁ τ₂) = TInt U' τ₁ × TInt U' τ₂
TInt U' (Sum τ₁ τ₂) = TInt U' τ₁  ⊎ TInt U' τ₂
TInt U' (Ind T) = V U' T
-- Interpretation of Shapes given an interpreted type
UInt U' Hole t = t
UInt U' UNIT t = ⊤
UInt U' (Sum T1' T2') l t = UInt T1' l t ⊎ UInt T2' l t
UInt U' (Prd T1' T2') l t = UInt T1' l t × UInt T2' l t
UInt U' (Cst τ) t = {!!}

-- data Env (val : Type → Set) : Ctx → Set where 
--   [] : Env val []
--   _∷_ : ∀ {τ Γ} → TInt val τ → Env val Γ → Env val (τ ∷ Γ)

-- lookupE : ∀ { τ Γ } (val : Type → Set) → τ ∈ Γ → Env val Γ → TInt val τ
-- lookupE val hd (x ∷ ρ) = x
-- lookupE val (tl v) (_ ∷ ρ) = lookupE val v ρ


-- -- Some examples for interpreting recursion, for inspiration
-- natrec : ∀ { t : Set } → ℕ → ((⊤ ⊎ t) → t) → t
-- natrec zero vs = vs (inj₁ tt) 
-- natrec (suc n) vs = vs (inj₂ (natrec n vs)) 

-- unitrec : ∀ {t : Set } → ⊤ → (⊤ → t) → t
-- unitrec tt v = v tt

-- boolrec : ∀ {t : Set } → Bool → (⊤ ⊎ ⊤ → t) → t
-- boolrec true v = v (inj₁ tt)
-- boolrec false v = v (inj₂ tt)

-- listrec : ∀ {t : Set } → List ℕ → (⊤ ⊎ (ℕ × t) → t) → t
-- listrec [] v = v (inj₁ tt)
-- listrec (x ∷ l) v = v (inj₂ (x , listrec l v))


-- urec  : ∀ {T1 : Ty} { t : Set } (val : Type → Set) → U val T1 T1 → (UInt val T1 t → t) → t
-- urec' : ∀ {T1 T2 : Ty} { t : Set } (val : Type → Set) → U val T1 T2 → (UInt val T1 t → t) → UInt val T2 t
-- urec val u v = v (urec' val u v) 
-- urec' {T1} val (InHole  u) v = urec val u v
-- urec' {T1} val (UNIT ) v = tt
-- urec' {T1} val (Left T2 T3 u) v = inj₁ (urec' val u v)
-- urec' {T1} val (Right T2 T3 u) v = inj₂ (urec' val u v)
-- urec' {T1} val (Pair T2 T3 u u₁) v = ( urec' val u v , urec' val u₁ v )
-- urec' {T1} val (Val v) f = {!!}

-- -- -- implements elimination
-- -- vrec : ∀ {T : Ty} {t : Set} → V val T → (UInt T t → t) → t
-- -- vrec u v = urec u v

-- ufold' : (val : Type → Set) (T0 T : Ty) → TInt val (fmap T (Ind T0)) → U val T0 T
-- ufold' val T0 Hole v = InHole v
-- ufold' val T0 UNIT v = UNIT 
-- ufold' val T0 (Sum T T₁) (inj₁ x) = Left T T₁ (ufold' val T0 T x)
-- ufold' val T0 (Sum T T₁) (inj₂ y) = Right T T₁ (ufold' val T0 T₁ y)
-- ufold' val T0 (Prd T T₁) v = Pair T T₁ (ufold' val T0 T (proj₁ v)) (ufold' val T0 T₁ (proj₂ v))
-- ufold' val T0 (Cst τ) v = {!!}

-- -- implements construction
-- ufold : (val : Type → Set) (T : Ty) → TInt val (fmap T (Ind T)) → TInt val (Ind T)
-- ufold val T v = ufold' val T T v

-- -- uint-val : Type → Set
-- -- uint-val = {!UInt!}

-- -- -- aux lemma needed to type-check elimination
-- -- lem-uint-tint : ∀ T τ → UInt (λ x → UInt x τ) T (TInt τ) ≡ TInt (fmap T τ)
-- -- lem-uint-tint Hole τ = refl
-- -- lem-uint-tint UNIT τ = refl
-- -- lem-uint-tint (Sum T T₁) τ rewrite lem-uint-tint T τ | lem-uint-tint T₁ τ = refl
-- -- lem-uint-tint (Prd T T₁) τ rewrite lem-uint-tint T τ | lem-uint-tint T₁ τ = refl
-- -- lem-uint-tint (Cst τ') τ = refl

-- -- ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
-- -- ev (EVar v) ρ = lookupE v ρ
-- -- ev (ETT) ρ = tt
-- -- ev (ECst x) ρ = x
-- -- ev (ESuc e) ρ = suc (ev e ρ)
-- -- ev (ERec e es) ρ = natrec (ev e ρ) (ev es ρ) 
-- -- ev (EAdd e f) ρ = ev e ρ + ev f ρ
-- -- ev (ELam e) ρ = λ x → ev e (x ∷ ρ)
-- -- ev (EApp e f) ρ = ev e ρ (ev f ρ)
-- -- ev (EPair e f) ρ = ev e ρ , ev f ρ
-- -- ev (EFst e) ρ = proj₁ (ev e ρ)
-- -- ev (ESnd e) ρ = proj₂ (ev e ρ)
-- -- ev (EInl e) ρ = inj₁ (ev e ρ)
-- -- ev (EInr e) ρ = inj₂ (ev e ρ)
-- -- ev (ECase e e₁ e₂) ρ with ev e ρ
-- -- ... | inj₁ v = ev e₁ (v ∷ ρ)
-- -- ... | inj₂ v = ev e₂ (v ∷ ρ)
-- -- ev (EFold {T} e) ρ = ufold T (ev e ρ)
-- -- ev (EFoldRec {τ} {T} e e₁) ρ = ? -- urec (ev e ρ) f
-- --   -- where f : UInt T (TInt τ)  → TInt τ
-- --   --       f v rewrite lem-uint-tint T τ = ev e₁ ρ v

-- -- --------------------------
-- -- -- Rec Examples
-- -- ------------------------

-- -- -- Natural numbers:
-- -- UNatTy : Ty
-- -- UNatTy = Sum UNIT Hole

-- -- UNat : Type
-- -- UNat = Ind UNatTy

-- -- -- zero and successor function

-- -- --helper
-- -- fromℕ : ∀ {Γ} → ℕ → Exp Γ UNat
-- -- fromℕ = fold mzero msuc
-- --   where -- meta-zero and -succ
-- --       mzero : ∀ {Γ} → Exp Γ UNat
-- --       mzero = EFold (EInl ETT) 

-- --       msuc : ∀ {Γ} → Exp Γ UNat → Exp Γ UNat
-- --       msuc e = EFold (EInr e)

-- -- ezero : ∀ {Γ} → Exp Γ UNat
-- -- ezero = EFold (EInl ETT) 

-- -- esuc : ∀ {Γ} → Exp Γ (Fun UNat UNat)
-- -- esuc = ELam (EFold (EInr (EVar hd)))

-- -- eplus : ∀ {Γ} → Exp Γ (Fun UNat (Fun UNat UNat))
-- -- eplus = ELam (ELam (EFoldRec (EVar (tl hd)) cases))
-- --   where cases = ELam (ECase (EVar hd)
-- --                             (EVar (tl (tl hd)))    -- zero case, use e2
-- --                             (EApp esuc (EVar hd))) -- recursive case

-- -- test-eplus : ev (EApp (EApp eplus (fromℕ 31)) (fromℕ 11)) [] ≡ ev (fromℕ 42) []
-- -- test-eplus = refl

-- -- -- TODO:
-- -- UNatListTy : Ty
-- -- UNatListTy = Sum UNIT (Prd UNatTy Hole)
-- -- UNatList : Type
-- -- UNatList = Ind UNatListTy