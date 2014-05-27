{- The base language with recursion on inductive types;
   simply typed lambda calculus with nats, addition, sums and products -}
module BaseInd where
open import Lib
open import Data.Unit 
open import Data.Bool

-- Shape of inductive types
data Ty : Set where
 Hole : Ty -- recursive occurence
 Ind : Ty → Ty -- substructure
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

-- -- Fill the holes in a Shape with a Type
fmap : Ty → Type → Type
fmap Hole τ = τ
fmap (Ind T) _ = Ind T
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
  InSub : ∀ T T' → U T' T' → U T (Ind T')
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
UInt (Ind T) t = V T 
UInt UNIT t = ⊤
UInt (Sum T1' T2') t = UInt T1' t ⊎ UInt T2' t
UInt (Prd T1' T2') t = UInt T1' t × UInt T2' t

urec  : ∀ {T1 : Ty} { t : Set } → U T1 T1 → (UInt T1 t → t) → t
urec' : ∀ {T1 T2 : Ty} { t : Set } → U T1 T2 → (UInt T1 t → t) → UInt T2 t
urec u alg = alg (urec' u alg) 
urec' {T1} (InHole .T1 u) alg = urec u alg
urec' {T1} (InSub .T1 T' x) alg = x
urec' {T1} (UNIT .T1) alg = tt
urec' {T1} (Left .T1 T2 T3 u) alg = inj₁ (urec' u alg)
urec' {T1} (Right .T1 T2 T3 u) alg = inj₂ (urec' u alg)
urec' {T1} (Pair .T1 T2 T3 u u₁) alg = ( urec' u alg , urec' u₁ alg )

-- implements elimination
vrec : ∀ {T : Ty} {t : Set} → V T → (UInt T t → t) → t
vrec u v = urec u v

ufold' : (T0 T : Ty) → TInt (fmap T (Ind T0)) → U T0 T
ufold' T0 Hole v = InHole T0 v
ufold' T0 UNIT v = UNIT T0
ufold' T0 (Ind T) v = InSub T0 T v
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
lem-uint-tint (Ind T') τ = refl
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
ezero : ∀ {Γ} → Exp Γ UNat
ezero = EFold (EInl ETT) 

esuc : ∀ {Γ} → Exp Γ (Fun UNat UNat)
esuc = ELam (EFold (EInr (EVar hd)))

--helper for tests
fromℕ : ∀ {Γ} → ℕ → Exp Γ UNat
fromℕ = fold mzero msuc
  where -- meta-zero and -succ
      mzero : ∀ {Γ} → Exp Γ UNat
      mzero = EFold (EInl ETT) 

      msuc : ∀ {Γ} → Exp Γ UNat → Exp Γ UNat
      msuc e = EFold (EInr e)
      
toℕ : V UNatTy → ℕ
toℕ (Left .(Sum UNIT Hole) .UNIT .Hole v) = 0
toℕ (Right .(Sum UNIT Hole) .UNIT .Hole (InHole .(Sum UNIT Hole) v)) = suc (toℕ v)
      
lem-toℕ-fromℕ : ∀ n → toℕ (ev (fromℕ n) []) ≡ n
lem-toℕ-fromℕ zero = refl
lem-toℕ-fromℕ (suc n) rewrite lem-toℕ-fromℕ n = refl

-- conversion from Num to UNat and back
fromNum : ∀ {Γ} → Exp Γ (Fun Num UNat)
fromNum = ELam (ERec (EVar hd) (ELam (ECase (EVar hd) mzero (EApp esuc (EVar hd)))))
  where -- meta-zero and -succ
      mzero : ∀ {Γ} → Exp Γ UNat
      mzero = EFold (EInl ETT) 

      msuc : ∀ {Γ} → Exp Γ UNat → Exp Γ UNat
      msuc e = EFold (EInr e)
      
toNum : ∀ {Γ} → Exp Γ (Fun UNat Num)
toNum = ELam (EFoldRec (EVar hd) (ELam (ECase (EVar hd) (ECst 0) (ESuc (EVar hd)))))


      
test-fromNum : ev (EApp fromNum (ECst 42)) [] ≡ ev (fromℕ 42) []
test-fromNum = refl

test-toNum1 : ev (EApp toNum (fromℕ 42)) [] ≡ 42
test-toNum1 = refl

test-toNum2 : ev (EApp toNum (EApp esuc (EApp esuc (EApp esuc ezero)))) [] ≡ 3
test-toNum2 = refl


-- addition
eplus : ∀ {Γ} → Exp Γ (Fun UNat (Fun UNat UNat))
eplus = ELam (ELam (EFoldRec (EVar (tl hd)) cases))
  where cases = ELam (ECase (EVar hd)
                            (EVar (tl (tl hd)))    -- zero case, use e2
                            (EApp esuc (EVar hd))) -- recursive case

test-eplus : ev (EApp (EApp eplus (fromℕ 31)) (fromℕ 11)) [] ≡ ev (fromℕ 42) []
test-eplus = refl


-- predecessor
enatcase : ∀ {Γ τ} → Exp Γ (Fun (Prd τ (Fun UNat τ)) (Fun UNat UNat))
enatcase = ELam (ELam (EFst (EFoldRec (EVar hd)
  (ELam (ECase (EVar hd) (EPair ezero ezero) (EFoldRec (ESnd (EVar hd))
                                              (ELam (ECase (EVar hd)
                                                    (EPair ezero (EApp esuc ezero))
                                                    (EPair (EApp esuc (EFst (EVar hd))) (EApp esuc (ESnd (EVar hd))))))))))))
epred : ∀ {Γ} → Exp Γ (Fun UNat UNat)
epred = EApp enatcase (EPair ezero (ELam (EVar hd)))

test-epred : ev (EApp toNum (EApp epred (EApp fromNum (ECst 42)))) [] ≡ 41
test-epred = refl

-- substraction
etimes : ∀ {Γ τ} → Exp Γ (Fun (Prd UNat τ) (Fun (Fun τ τ) τ))
etimes = ELam (ELam (EFoldRec (EFst (EVar (tl hd))) (ELam (ECase (EVar hd) (ESnd (EVar (tl (tl (tl hd))))) (EApp (EVar (tl (tl hd))) (EVar hd))))))

esub : ∀ {Γ} → Exp Γ (Fun (Prd UNat UNat) UNat)
esub = ELam (EApp (EApp etimes (EPair (ESnd (EVar hd)) (EFst (EVar hd)))) epred)

test-esub : ev (EApp toNum (EApp esub (EPair (fromℕ 42) (fromℕ 11)))) [] ≡ 31
test-esub = refl
                            
-- maximum
emax : ∀ {Γ} → Exp Γ (Fun (Prd UNat UNat) UNat)
emax = ELam (EFoldRec (EApp esub (EVar hd))
  (ELam (ECase (EVar hd) (ESnd (EVar (tl (tl hd)))) (EFst (EVar (tl (tl hd)))))))
  
test-emax : ev (EApp toNum (EApp emax (EPair (fromℕ 42) (fromℕ 11)))) [] ≡ 42
test-emax = refl

test-emax2 : ev (EApp toNum (EApp emax (EPair (fromℕ 2) (fromℕ 11)))) [] ≡ 11
test-emax2 = refl

-- Binary trees
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

eheight : ∀ {Γ} → Exp Γ (Fun UBin UNat)
eheight = ELam (EFoldRec (EVar hd) (ELam (ECase (EVar hd) ezero (EApp esuc (EApp emax (EVar hd))))))

bin1 : ∀ {Γ} → Exp Γ UBin
bin1 = EApp enode (EPair eleaf eleaf)

bin2 : ∀ {Γ} → Exp Γ UBin
bin2 = EApp enode (EPair bin1 eleaf)

bin3 : ∀ {Γ} → Exp Γ UBin
bin3 = EApp enode (EPair bin1 (EApp enode (EPair bin2 (EApp enode (EPair eleaf bin1)))))

test-height1 : ev (EApp toNum (EApp eheight bin1)) [] ≡ 1
test-height1 = refl

test-height2 : ev (EApp toNum (EApp eheight bin2)) [] ≡ 2
test-height2 = refl

test-height3 : ev (EApp toNum (EApp eheight bin3)) [] ≡ 4
test-height3 = refl

-- Natlist
UNatListTy : Ty
UNatListTy = Sum UNIT (Prd (Ind UNatTy) Hole)
UNatList : Type
UNatList = Ind UNatListTy

enil : ∀ {Γ} → Exp Γ UNatList
enil = EFold (EInl ETT)

econs : ∀ {Γ} → Exp Γ (Fun (Prd UNat UNatList) UNatList)
econs = ELam (EFold (EInr (EPair (EFst (EVar hd)) (ESnd (EVar hd)))))

fromList : ∀ {Γ} → List ℕ → Exp Γ UNatList
fromList [] = EFold (EInl ETT)
fromList (x ∷ xs) = EApp econs (EPair (fromℕ x) (fromList xs))

toList : V UNatListTy → List ℕ 
toList v = urec v f
  where f : (x : ⊤ ⊎ Σ (U (Sum UNIT Hole) (Sum UNIT Hole)) (λ _ → List ℕ)) →
              List ℕ
        f (inj₁ _) = []
        f (inj₂ (x , xs)) = toℕ x ∷ xs

l1 l2 : List ℕ
l1 = (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
l2 = (1 ∷ 2 ∷ [])

emap : ∀ {Γ} → Exp Γ (Fun (Fun UNat UNat) (Fun UNatList UNatList))
emap = ELam (ELam (EFoldRec (EVar hd)
      (ELam (ECase (EVar hd)
        enil
        (EApp econs (EPair (EApp (EVar (tl (tl (tl hd))))
                           (EFst (EVar hd))) (ESnd (EVar hd))))))))
                           
test-emap-nil : toList (ev (EApp (EApp emap esuc) enil) []) ≡ []
test-emap-nil = refl

test-emap-l1 : toList (ev (EApp (EApp emap esuc) (fromList l1)) []) ≡ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
test-emap-l1 = refl
