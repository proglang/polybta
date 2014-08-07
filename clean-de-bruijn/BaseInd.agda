{- The base language with recursion on inductive types;
   simply typed lambda calculus with nats, addition, sums and products -}
module BaseInd where
open import Lib
open import Data.Unit 
open import Data.Bool

--now extend it with recursors

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

--...
--fmap Hole Num = Num
--fmap (Ind UNIT) _ = Ind UNIT
--fmap UNIT Num = UNIT
--fmap (Sum UNIT UNIT) τ = Sum UNIT UNIT
--fmap (Prd UNIT UNIT) τ = Prd UNIT UNIT 


data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ETT : Exp Γ UNIT
  ECst : ℕ → Exp Γ Num
  ESuc : Exp Γ Num → Exp Γ Num
  ERec : ∀ {τ} → Exp Γ Num → Exp Γ (Fun (Sum UNIT τ) τ) → Exp Γ τ
  -- it differs from the iterator,
  -- ERec : ∀ {τ} → Exp Γ Num → Exp Γ τ → Exp Γ (Fun τ τ) → Exp Γ τ
  -----------------------------------------------------------------
  --recursor
  EIt  : ∀ {τ} → Exp Γ τ → Exp Γ (Fun Num (Fun τ τ)) → Exp Γ Num
               → Exp Γ τ
  -----------------------------------------------------------------
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
  -- note:[fold] is a standard way of generating "denotational semantics",
  --      by replacing all syntactic constructors with corresponding "interpreting"
  --      functions. Consider the following examples,
  --      syntactic addition : Add (Val n₁) (Val n₂) whose semantics as,
  --      [Add (Val n₁) (Var n₂)] = n₁ + n₂ 
  --      the above semantic interpretation can be obtained by using the following two
  --      functions for two constructors involved in the expression,
  --      f : exp int → int   g : int → int → int
  --      thus,
  --      fold f g (Add (Val n₁) (Val n₂)) = g (f n₁) (f n₂) = n₁ + n₂
  -------------------------------------------------------------------------
  --     
  EFold : ∀ {T} → Exp Γ (fmap T (Ind T)) → Exp Γ (Ind T)
  -- Eliminate a value of inductive type
  EFoldRec : ∀ {τ T} → Exp Γ (Ind T) → Exp Γ (Fun (fmap T τ) τ) → Exp Γ τ
  -- note: what is the corresponding term for [? : Exp Γ (Fun (fmap T τ) τ)]

-- Values of inductive types, in U T1 T2, T1 is the top-level type, T2
-- is the type of the current node
data U : Ty → Ty → Set where
  InHole : ∀ T → U T T → U T Hole
  InSub : ∀ T T' → U T' T' → U T (Ind T')
  UNIT : ∀ T → U T UNIT
  Left : ∀ T T1 T2 → U T T1 → U T (Sum T1 T2)
  Right : ∀ T T1 T2 → U T T2 → U T (Sum T1 T2)
  Pair : ∀ T T1 T2 →  U T T1 → U T T2 → U T (Prd T1 T2)
--[U] is the meta-level value of inductive types

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
-- the default value of the recursion by the iterator is computed
-- by a case distinction
 
natrec (suc n) vs = vs (inj₂ (natrec n vs)) 

unitrec : ∀ {t : Set } → ⊤ → (⊤ → t) → t
unitrec tt v = v tt

boolrec : ∀ {t : Set } → Bool → (⊤ ⊎ ⊤ → t) → t
boolrec true v = v (inj₁ tt)
boolrec false v = v (inj₂ tt)

listrec : ∀ {t : Set } → List ℕ → (⊤ ⊎ (ℕ × t) → t) → t
listrec [] v = v (inj₁ tt)
listrec (x ∷ l) v = v (inj₂ (x , listrec l v))

--interpreting recursion for recursors
Natrec : ∀ {t : Set} → ℕ → t → (ℕ → (t → t)) → t
Natrec zero v u = v
Natrec (suc n) v u = u n (Natrec n v u)


-- TInt : Type → Set
-- TInt UNIT = ⊤
-- TInt Num = ℕ
-- TInt (Fun τ₁ τ₂) = TInt τ₁ → TInt τ₂
-- TInt (Prd τ₁ τ₂) = TInt τ₁ × TInt τ₂
-- TInt (Sum τ₁ τ₂) = TInt τ₁ ⊎ TInt τ₂
-- TInt (Ind T) = V T


-- Interpretation of Shapes given an interpreted type

-- fill the "holes" of the inductive type with an
-- meta-level type
UInt : Ty → Set → Set
UInt Hole t = t
UInt (Ind T) t = V T 
UInt UNIT t = ⊤
UInt (Sum T1' T2') t = UInt T1' t ⊎ UInt T2' t
UInt (Prd T1' T2') t = UInt T1' t × UInt T2' t

-- data U : Ty → Ty → Set where
--   InHole : ∀ T → U T T → U T Hole
--   InSub : ∀ T T' → U T' T' → U T (Ind T')
--   UNIT : ∀ T → U T UNIT
--   Left : ∀ T T1 T2 → U T T1 → U T (Sum T1 T2)
--   Right : ∀ T T1 T2 → U T T2 → U T (Sum T1 T2)
--   Pair : ∀ T T1 T2 →  U T T1 → U T T2 → U T (Prd T1 T2)


--[urec] and [urec'] together translate a meta-level value of inductive type 
--in [U] to another meta-level value?
--the semantics of this function might be,
--translating the meta-level value of inductive type to meta-level value of
--inductive type whose holes are filled
urec  : ∀ {T1 : Ty} {t : Set} → U T1 T1 → (UInt T1 t → t) → t
urec' : ∀ {T1 T2 : Ty} {t : Set} → U T1 T2 → (UInt T1 t → t) → UInt T2 t
urec u alg = alg (urec' u alg) 
urec' {T1} (InHole .T1 u) alg = urec u alg
--note: [u : U T1 T1], [alg : UInt T1 t → t], [UInt Hole t = t]
--hece [urec u alg : t ]
urec' {T1} (InSub .T1 T' x) alg = x
--note: [x : U T' T'], [alg : UInt T' t → t], [UInt (Ind T') t = U T' T']
urec' {T1} (UNIT .T1) alg = tt
--note: [UNIT T1 : U T1 UNIT], [alg : UInt T1 t → t], [UInt UNIT t = T]
urec' {T1} (Left .T1 T2 T3 u) alg = inj₁ (urec' u alg)
--note: [Left T1 T2 T3 u : U T1 (Sum T2 T3)], [alg : UInt T1 t → t], 
--[UInt (Sum T2 T3) t = UInt T2 t ⊎ UInt T3 t]
--[inj₁ (urec' u alg) : UInt T2 t ⊎ UInt T3 t] 
urec' {T1} (Right .T1 T2 T3 u) alg = inj₂ (urec' u alg)
--note : [Right T1 T2 T3 u : U T1 (Sum T2 T3)], [alg : UInt T1 t → t], 
--[UInt (Sum T2 T3) t = UInt T2 t ⊎ UInt T3 t]
--[inj₂ (urec' u arg) : UInt T2 t ⊎ UInt T3 t]
urec' {T1} (Pair .T1 T2 T3 u u₁) alg = ( urec' u alg , urec' u₁ alg )
--note : [Pair T1 T2 T3 u u₁ : U T1 (Prd T2 T3)], [alg : UInt T1 t → t],
--[UInt (Prd T2 T3) t = UInt T2 t × Uint T3 t]
--[(urec' u alg , urec' u₁ alg)]

-- -- implements elimination
-- -- what "elimination" ? 
-- -- from high-level value defined by [U] to meta-level values by Agda? 
vrec : ∀ {T : Ty} {t : Set} → V T → (UInt T t → t) → t
vrec u v = urec u v


-- --from meta-level value to high-level inductive value

-- --operational semantics:unfold operation
-- --consider the following example of a simple state transition system,
-- -- [Add (Val n₁) (Val n₂)] -> [Val (n₁ + n₂)]
-- -- which is essentially one small-step reduction of the term [Add (Val n₁) (Val n₂)]
-- -- such a one step reduction of the term can be obtained by the [unfold] operation
-- -- specified as a transition/small-step relation [trans]. Then we have
-- -- unfold trans (Add (Val n₁) (Val n₂)) = trans (Add (Val n₁) (Val n₂)) = Val (n₁ + n₂)
-- ---------------------------------------------------------------
-- --[ufold'] can be interpreted as follows,
-- -- taking an interpreted inductive term,evaluate to its value defined on the 
-- -- meta-level

 
ufold' : (T0 T : Ty) → TInt (fmap T (Ind T0)) → U T0 T
ufold' T0 Hole v = InHole T0 v
--note:[fmap Hole τ = τ] and [v : U T0 T0]
ufold' T0 UNIT v = UNIT T0
--note:[fmap UNIT (Ind T0) = UNIT] and  [UNIT T0 : U T0 UNIT]
ufold' T0 (Ind T) v = InSub T0 T v
--note:[v : U T T] and [InSub T0 T v : U T0 (Ind T)]
ufold' T0 (Sum T T₁) (inj₁ x) = Left T0 T T₁ (ufold' T0 T x)
--note:[fmap (Sum T T₁) (Ind T0) = Sum (fmap T (Ind T0)) (fmap T₁ (Ind T0))]
--[x : fmap T (Ind T0)] and [ufold' T0 T x : U T0 T] 
ufold' T0 (Sum T T₁) (inj₂ y) = Right T0 T T₁ (ufold' T0 T₁ y)
--note:[ufold' T0 T₁ y : U T0 T₁]
ufold' T0 (Prd T T₁) v = Pair T0 T T₁ (ufold' T0 T (proj₁ v)) (ufold' T0 T₁ (proj₂ v))
--note:[v : Prd (fmap T (Ind T0))(fmap T₁ (Ind T0))] 

-- implements construction
ufold : (T : Ty) → TInt (fmap T (Ind T)) → TInt (Ind T)
ufold T v = ufold' T T v

-- -- aux lemma needed to type-check elimination
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
ev (EIt v u n) ρ = Natrec (ev n ρ) (ev v ρ) (ev u ρ) 
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
-- evaluating [EFold] to its corresponding meta-level value
-- defined by [U]
-- [e : exp Γ (fmp T (Ind T))] and [(ev e ρ) : TInt (fmp T (Ind T))]
-- [ufold T (ev e ρ) : U T T] ,thus
-- generating the meta-level values of the inductive type
ev (EFoldRec {τ} {T} e e₁) ρ = urec (ev e ρ) f
-- [e : exp Γ (Ind T)] [e₁ : exp Γ (Fun (fmap T τ) τ)]
-- [(ev e ρ) : U T T] and 
-- [urec] here serves as [iterator]?
  where f : UInt T (TInt τ)  → TInt τ
        f v rewrite lem-uint-tint T τ = ev e₁ ρ v
-- evaluating [EFoldRec] to 
--------------------------
-- Rec Examples
------------------------

-- Natural numbers:
UNatTy : Ty
UNatTy = Sum UNIT Hole
--natural number type is defined as,
--[UNatTy = Sum UNIT Hole] with holes to be filled up by "things"
UNat : Type
UNat = Ind UNatTy
--then define the inductive type [Type] on top of [UNatTy],
--[UNat = Ind UNatTy]

--constructing inductive type

-- zero and successor function
ezero : ∀ {Γ} → Exp Γ UNat
ezero = EFold (EInl ETT) 
--note:
--[EInl ETT : fmap UNatTy (Ind UNatTy)] and 
--[fmap UNatTy (Ind UNatTy) = Sum (fmap UNIT UNat) (fmap Hole UNat)]
--[...=Sum UNIT UNat]

--also note that here [EFold] is being used to encapsulate the "regular"
--low-level term to change its type to the inductive type [Ind ty]

esuc : ∀ {Γ} → Exp Γ (Fun UNat UNat)
esuc = ELam (EFold (EInr (EVar hd)))
--note:
--[EVar hd : UNat] and [EInr (EVar hd) : Sum UNIT UNat]
--[EFold (EInr (EVar hd)) : exp Γ UNat]

--also note:
--[apply esuc ezero : Exp Γ UNat]



--helper for tests
--[fold?]
--[from natural number,meta-level, to high-level number ]
fromℕ : ∀ {Γ} → ℕ → Exp Γ UNat
fromℕ = fold mzero msuc
--note that [fold] above is an iterator
--where argument [mzero] serves as the default value of the 
--recursion and [msuc] as the involved recursive function 

--note that here [fold] is the iterator which takes 
--a) [ezero] as its default return when the predessessor is zero
--b) [esuc] as the function passed over at the beginning of every 
--   iteration


--also note,
--a) [mzero] is used as the default value of the iterator [fold];
--b) [msuc] is used as the recursive function of the iterator
  where -- meta-zero and -succ
      mzero : ∀ {Γ} → Exp Γ UNat
      mzero = EFold (EInl ETT) 

      msuc : ∀ {Γ} → Exp Γ UNat → Exp Γ UNat
      msuc e = EFold (EInr e)
--then [fromℕ] is a function upon input value [n : ℕ] returns
--the corresponding low-level term
toℕ : V UNatTy → ℕ
toℕ (Left .(Sum UNIT Hole) .UNIT .Hole v) = 0
--[v : U (Sum UNIT Hole) UNIT] which means that [v = UNIT (Sum UNIT Hole)]
--which means that the [v] is a unit value representing [0]
--why? how a positive number is represented as indicated by [esuc]
toℕ (Right .(Sum UNIT Hole) .UNIT .Hole (InHole .(Sum UNIT Hole) v)) = suc (toℕ v)
--[InHole (Sum UNIT Hole) v : U (Sum UNIT Hole) Hole] which means that
--[v: U (Sum UNIT Hole) (Sum UNIT Hole)] itsefl representing a predessessor      
lem-toℕ-fromℕ : ∀ n → toℕ (ev (fromℕ n) []) ≡ n
lem-toℕ-fromℕ zero = refl
lem-toℕ-fromℕ (suc n) rewrite lem-toℕ-fromℕ n = refl

--note [toℕ] is used as the converter from number of type [UNat] to type [Num]
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
--[EFoldRec] here is equivalent to an iterator with a type [Exp Γ UNat] counter whose
--meta-level type is [U UNatTy UNatTy]. The semantics of [EFoldRec] works as follows,
--a) every time the function within the body of [EFoldRec] is called,the meta-level value
--   of type [U UNatTy UNatTy] is match against constructors [Left] and [Right] and continues
--   in case of [Right];
--b) it terminates in case [Left].

--[toNum] upon a number of the inductive type [Exp Γ UNat],returns a number of 
--type [Exp Γ Num]


      
test-fromNum : ev (EApp fromNum (ECst 42)) [] ≡ ev (fromℕ 42) []
test-fromNum = refl

test-toNum1 : ev (EApp toNum (fromℕ 42)) [] ≡ 42
test-toNum1 = refl

test-toNum2 : ev (EApp toNum (EApp esuc (EApp esuc (EApp esuc ezero)))) [] ≡ 3
test-toNum2 = refl


--note that the three representations of natural numbers in the current system
--a)the natural number as inductive type [UNat];
--b)the natural number as type [Num];
--c)the natural number as meta-level inductive type [U (Sum UNIT Hole) (Sum UNIT Hole)];
--d)the natural number as it is in agda [ℕ]. 

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
