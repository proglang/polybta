--library 
module Lib where
open import Data.Nat public hiding (_<_ ; _*_) 
open import Function public using (_∘_)
open import Data.List public 
open import Data.Product public using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; ∃)
open import Data.Sum public using (_⊎_ ; [_,_]′ ; inj₁ ; inj₂)
open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Data.Bool

open import Category.Functor public



--------------------------------
--module "Auxiliaries"
--note: it includes common
--      propositions, functions, 
--      and lemmas shared by all
--      files
--------------------------------
module Auxiliaries where


  infix 4 _∈_
  data _∈_ {A : Set} : A → List A → Set where
    hd : ∀ {x xs} → x ∈ (x ∷ xs)
    tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

  mapIdx : {A B : Set} → (f : A → B) →
           {x : A} {xs : List A} → x ∈ xs → f x ∈ map f xs
  mapIdx f hd = hd
  mapIdx f (tl x₁) = tl (mapIdx f x₁)

  data _==_ {A : Set} (x : A) : A → Set where
    refl : x == x


  →tl : ∀ {A B : Set} {x' y' : A} (x y : A ⊎ B)→ x ≡ y →  x ≡ inj₁ x' → y ≡ inj₁ y' → x' ≡ y' 
  →tl px py a b c rewrite b | c with py | a 
  ... | H | refl = refl

                                                                                             
  →tr : ∀ {A B : Set} {x' y' : B} (x y : A ⊎ B)→ x ≡ y →  x ≡ inj₂ x' → y ≡ inj₂ y' → x' ≡ y' 
  →tr px py a b c rewrite c | b with px | a 
  ... | H | refl = refl 

  cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
            (f : A → B → C → D) {xa ya xb yb xc yc} →
            xa ≡ ya → xb ≡ yb → xc ≡ yc → f xa xb xc ≡ f ya yb yc
  cong₃ f refl refl refl = refl
                           

  module SubLists where
    data _↝_ {A : Set} : List A → List A → Set where
      refl   : {l : List A} → l ↝ l
      extend : ∀ {l₁ l₂ τ}  → l₁ ↝ l₂ → l₁ ↝ (τ ∷ l₂)

    lem-↝-trans : ∀ {A : Set}{Γ Γ' Γ'' : List A} → Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
    lem-↝-trans Γ↝Γ' refl = Γ↝Γ'
    lem-↝-trans Γ↝Γ' (extend Γ'↝Γ'') = extend (lem-↝-trans Γ↝Γ' Γ'↝Γ'')


    lem-↝-refl-id : ∀ {A : Set} {Γ Γ' : List A} →
                      (Γ↝Γ' : Γ ↝ Γ') →
                      Γ↝Γ' ≡ (lem-↝-trans refl Γ↝Γ')  
    lem-↝-refl-id refl = refl
    lem-↝-refl-id (extend Γ↝Γ') = cong extend (lem-↝-refl-id Γ↝Γ')

    _↝-∷_ : {A : Set} (x : A) (l : List A) → l ↝ (x ∷ l)
    x ↝-∷ l = extend refl

    data _↝_↝_ {A : Set} : List A → List A → List A → Set where
      refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ''
      extend : ∀ {Γ Γ' Γ'' τ} →
                 Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'')

    _⊕_ : ∀ {A : Set}{Γ Γ' Γ'' : List A} → 
             Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
    _⊕_ Γ↝Γ' refl = Γ↝Γ'                                 
    _⊕_ Γ↝Γ' (extend Γ'↝Γ'') = extend (Γ↝Γ' ⊕ Γ'↝Γ'')
  open SubLists public


---------------------------
--module "TwoLevelTypes"
--note: it includes
--a)submodule "Subsumption";
--b)submodule "Others".
--------------------------- 
module TwoLevelTypes where
  open import Data.Bool
  open Auxiliaries
  open import Types
  open two-level-types

  module Subsumption where
    
 

    lem-bt≼S : {bt : BT} → isTrue (bt ≼ S) → bt == S
    lem-bt≼S {S} bt≼S = refl
    lem-bt≼S {D} ()

    lem-D≼bt : {bt : BT} → isTrue (D ≼ bt) → bt == D
    lem-D≼bt {S} ()
    lem-D≼bt {D} D≼bt = refl

    lem-force-bt : ∀ {bt at} → isTrue (bt ≼ btof at) → D == bt → D == btof at
    lem-force-bt {S} bt≼at ()
    lem-force-bt {D} {Ann S y'} () D=bt
    lem-force-bt {D} {Ann D y'} bt≼at D=bt = refl
 
  open Subsumption public

  module Others where
 
    data IsDynamic : AType → Set where
      is-dyn : ∀ σ → IsDynamic (Ann D σ)

    lem-IsDynamic-by-wf : ∀ α → isTrue (D ≼ btof α) → IsDynamic α
    lem-IsDynamic-by-wf (Ann S σ) ()
    lem-IsDynamic-by-wf (Ann D σ) _ = is-dyn σ 



    mutual
      strip : AType → Type
      strip (Ann _ σ) = strip' σ

      strip' : SType → Type
      strip' SNum = TNum
      strip' (SFun y y') = TFun (strip y) (strip y')


  open Others public 

 ----------------------------------
--module "TwoLevelTerms"
--note: it includes
--a)weakening lemmas.
----------------------------------- 
module TwoLevelTerms where  
  open TwoLevelTypes
  open Auxiliaries
  open import Types
  open two-level-types
 
-----------------------------------
--module "TwoLevelTypes-Simp"
--note: well-formedness restriction
--      is incorporated into types
--a)some factored out lemmas.
----------------------------------- 
module TwoLevelTypes-Simp where
  open Auxiliaries
  open import Types
  open two-level-types-simp

 
  module Others where
 
    lem : ∀ {A : Set} (x y : A) (xs xs' : List A) → (x ∷ xs) ↝ xs' → xs ↝ (y ∷ xs')
    lem x y xs .(x ∷ xs) refl = extend (extend refl)
    lem x y xs .(x' ∷ xs') (extend {.(x ∷ xs)} {xs'} {x'} p) = extend (lem x x' xs xs' p)
 

  
  open Others public 

 ----------------------------------
--module "TwoLevelTerms-Simp"
--note: it includes
--a)weakening lemmas.
----------------------------------- 
module TwoLevelTerms-Simp where 
  open TwoLevelTypes-Simp
  open Auxiliaries
  open import Types
  open two-level-types-simp
  

 ----------------------------------
--module "TwoLevelTerms-Simp-lift"
--note: it includes
--a)weakening lemmas.
----------------------------------- 
module TwoLevelTerms-Simp-Lift where
  open TwoLevelTypes-Simp
  open Auxiliaries
  open import Types
  open two-level-types-simp
 
  module Correctness where

    ---------------------------
    --strip off two-level types
    ---------------------------
    typeof : AType → Type
    typeof SNum = Num
    typeof (SFun α₁ α₂) = Fun (typeof α₁) (typeof α₂)
    typeof (D x) = x

    stripα = typeof

    stripΔ : ACtx → Ctx
    stripΔ = map stripα


  open Correctness public  
 


 ----------------------------------
--module "TwoLevelTerms-Simp-PS"
--note: it includes
--a)terms of base type [Exp];
--b)terms of two-level type [AExp]
--  extended with lifting operator
--  of terms of static numbers;
--c)extended with pairs, sums,
--  and terms of liftable types;
--d)weakening lemmas.
----------------------------------- 
module TwoLevelTerms-Simp-PS where
  open Auxiliaries
  open import Types
  open two-level-types-simp-ps

  data Exp (Γ : Ctx) : Type → Set where
    EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
    ECst : ℕ → Exp Γ Num
    EAdd : Exp Γ Num → Exp Γ Num -> Exp Γ Num
    ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
    EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'
    EPair  : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (Prd τ τ')
    EInl   : ∀ {τ τ'} → Exp Γ τ → Exp Γ (Sum τ τ')
    EInr   : ∀ {τ τ'} → Exp Γ τ' → Exp Γ (Sum τ τ') 
    EFst : ∀ {τ τ'} → Exp Γ (Prd τ  τ') → Exp Γ τ
    ESnd : ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ'
    ECase : ∀ {τ τ' τ''} → Exp Γ (Sum τ τ') → Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''
  
  ------------------------------------
  --module "Liftable"
  --note: liftable types are specified
  ------------------------------------
  module liftable where
   
    typeof : AType → Type
    typeof SNum = Num
    typeof (SFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
    typeof (D x) = x
    typeof (SPrd α₁ α₂) = Prd (typeof α₁) (typeof α₂)
    typeof (SSum α₁ α₂) = Sum (typeof α₁) (typeof α₂)
   
    -------------------------------
    --module "Examples"
    --note:some motivating examples 
    --     before the specification
    -------------------------------
    --module Examples where

      -- liftE : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
      -- liftE Γ↝Γ' e = elevate (refl Γ↝Γ') e

      --case 1. a first-order static value in a dynamic environment
      -- lift1 : AExp [] SNum
      -- lift1 = (SCst 0)

      -- e1 : ATInt [] SNum
      -- e1 = 0

      -- lifted1 : Exp [] (typeof SNum)
      -- lifted1 = ECst e1
      --case 2. higher-order static function in a dynamic environment
      --a. a function whose input argument is of static integer
      --lift2 : AExp [] (AFun AInt AInt)
      --lift2 = ALam (Var hd)

      --e2 : Imp [] (AFun AInt AInt)
      --e2 = λ Γ↝Γ' x → x

      --lifted2 : Exp [] (typeof (AFun AInt AInt))
      --lifted2 = ELam {!!}
      --Note that as explained above it is impossible to construct the right term using [e2]
      --to fill in the above hole!

      --b. a function whose input argument is of dynamic integer
      --b.1. when return type is of dynamic integer
      -- lift3 : AExp [] (SFun (D Num) (D Num))
      -- lift3 = SLam (Var hd)

      -- e3 : ATInt [] (SFun (D Num) (D Num))
      -- e3 =  λ Γ↝Γ' x → x

      -- liftede3 : Exp [] (typeof (SFun (D Num) (D Num)))
      -- liftede3 = ELam (e3 (extend refl) (EVar hd))
      --b.2. when return type is of static integer
      -- lift4 : AExp [] (SFun (D Num) SNum)
      -- lift4 = SLam (SCst 0)

      -- e4 : ATInt [] (SFun (D Num) SNum)
      -- e4 = λ Γ↝Γ' x → 0

      -- liftede4 : Exp [] (typeof (SFun (D Num) SNum))
      -- liftede4 = ELam ( ECst {Num ∷ []} (e4 (extend refl) (EVar hd)))

      --c. a function whose input argument is of static function type
      --c.1. static function type returns a static integer
      --lift5 : AExp []  (AFun (AFun AInt AInt) AInt)
      --lift5 = ALam (AApp (Var hd) (AInt 0))

      --e5 : Imp []  (AFun (AFun AInt AInt) AInt)
      --e5 = λ Γ↝Γ' x → x ↝-refl 0

      --liftede5 : Exp [] (typeof ( AFun (AFun AInt AInt) AInt))
      --liftede5 =  ELam (EInt (e5 (↝-extend {τ = Fun Int Int} ↝-refl) (λ Γ↝Γ' e' → {!!})))
      --Note that again it is impossible to construct the right residual term

      --c.2. static function type returns a dynamic integer
      --c.2.1. the input of the function type is of static integer
      -- lift6 : AExp []  (SFun (SFun SNum (D Num)) (D Num))
      -- lift6 = SLam (SApp (Var hd) (SCst 0))

      -- e6 : ATInt []  (SFun (SFun SNum (D Num)) (D Num))
      -- e6 = λ Γ↝Γ' x → x refl 0

      -- liftede6 : Exp [] (typeof ( SFun (SFun SNum (D Num)) (D Num)))
      -- liftede6 =  ELam ((e6 (extend {τ = Fun Num Num} refl) 
      --                  (λ Γ↝Γ' e' → EApp (liftE Γ↝Γ' (EVar {Fun Num Num ∷ []} hd)) (ECst e'))))
      --c.2.1. the input of the function type is of dynamic integer
      -- lift7 : AExp []  (SFun (SFun (D Num) (D Num)) (D Num))
      -- lift7 = SLam (SApp (Var hd) (DCst 0))

      -- e7 : ATInt []  (SFun (SFun (D Num) (D Num)) (D Num))
      -- e7 = λ Γ↝Γ' x → x refl (ECst 0)

      -- liftede7 : Exp [] (typeof ( SFun (SFun (D Num) (D Num)) (D Num)))
      -- liftede7 =  ELam ((e7 (extend {τ = Fun Num Num} refl) 
      --                  (λ Γ↝Γ' e' → EApp (liftE Γ↝Γ' (EVar {Fun Num Num ∷ []} hd)) e')))
      --c.3. the output of the function type is of higher-order static value
      --c.3.1 the return value has one static integer as input
      -- lift8 : AExp []  (AFun (D Int) (AFun AInt (D Int)))
      -- lift8 = ALam (ALam (Var (tl hd)))

      -- e8 : Imp []  (AFun (D Int) (AFun AInt (D Int)))
      -- e8 = λ Γ↝Γ' x Γ'↝Γ'' y → liftE Γ'↝Γ'' x 

      -- liftede8 : Exp [] (typeof ( AFun (D Int) (AFun AInt (D Int))))
      -- liftede8 =  ELam (ELam (e8 (↝-extend (↝-extend ↝-refl)) (EVar (tl hd)) ↝-refl {!!}))

      --c.3.2 the return value has one dynamic integer as input
      -- lift9 : AExp []  (SFun (D Num) (SFun (D Num) (D Num)))
      -- lift9 = SLam (SLam (Var (tl hd)))

      -- e9 : ATInt []  (SFun (D Num) (SFun (D Num) (D Num)))
      -- e9 = λ Γ↝Γ' x Γ'↝Γ'' y → liftE Γ'↝Γ'' x 

      -- liftede9 : Exp [] (typeof ( SFun (D Num) (SFun (D Num) (D Num))))
      -- liftede9 =  ELam (ELam (e9 (extend (extend refl)) (EVar (tl hd)) refl (EVar hd)))

      --d. static pairs and sums in dynamic environment
      --d.1. identity function with  static sum as its input 
      -- lift10 : AExp [] (SFun (SSum (D Num) (D Num)) (SSum (D Num) (D Num)))
      -- lift10 = SLam (Var hd)

      -- e10 : ATInt [] (SFun (SSum (D Num) (D Num)) (SSum (D Num) (D Num)))
      -- e10 =  λ Γ↝Γ' x → x


      -- liftede10 : Exp [] (typeof (AFun ((D Int) ⊎ (D Int)) ((D Int) ⊎ (D Int))))
      -- liftede10 = ELam {!e10!}

      --d.2. identity function with  static pair as its input 
      -- lift11 : AExp [] (SFun (SPrd (D Num) (D Num)) (SPrd (D Num) (D Num)))
      -- lift11 = SLam (Var hd)

      -- e11 : ATInt [] (SFun (SPrd (D Num) (D Num)) (SPrd (D Num) (D Num)))
      -- e11 =  λ Γ↝Γ' x → x


      -- liftede11 : Exp [] (typeof (SFun (SPrd (D Num) (D Num)) (SPrd (D Num) (D Num))))
      -- liftede11 = ELam (fst (e11 (extend refl) (EFst (EVar hd) , ESnd (EVar hd))) ,
      --                     snd (e11 (extend refl) (EFst (EVar hd) , ESnd (EVar hd))))

      --Note that the above two examples in section "d" clearly shows that 
      --"static functions with inputs of static sum type are not liftable
      -- while with inputs of static pair type are liftable ".

      ---------------------------
      --summary on liftable terms
      ---------------------------
      --a. Regarding static first-order static value (static integer) in dynamic environment
      --   All terms of static integer type are liftable
      --b. Regarding static higher-order static value in dynamic environment
      --b.1. given that output value is liftable 
      --     • when input is of first-order dynamic type,liftable 
      --     • when input is of higher-order static type and output 
      --       of that input is of dynamic type,liftable
      --b.2. given that input value is liftable
      --     • when output is of first-order type,liftable
      --     • when output is of higher-order type and inputs 
      --       of that type are of dynamic type,liftable
  
  --open Examples public
    
    mutual 
      data Liftable : AType → Set where
        D : ∀ τ → Liftable (D τ)
        SCst : Liftable SNum
        SSum : ∀ {α₁ α₂} → Liftable α₁ → Liftable α₂ → Liftable (SSum α₁ α₂)
        SPrd : ∀ {α₁ α₂} → Liftable α₁ → Liftable α₂ → Liftable (SPrd α₁ α₂)
        SFun : ∀ {α₁ α₂} → Liftable⁻ α₁ → Liftable α₂ → Liftable (SFun α₁ α₂)

      data Liftable⁻ : AType → Set where
        D : ∀ τ → Liftable⁻ (D τ)
        SPrd : ∀ {α₁ α₂} → Liftable⁻ α₁ → Liftable⁻ α₂ → Liftable⁻ (SPrd α₁ α₂)
        SFun : ∀ {α₁ α₂} → Liftable α₁ → Liftable⁻ α₂ → Liftable⁻ (SFun α₁ α₂)
  
  open liftable public 

  data AExp (Δ : ACtx) : AType → Set where
    Var : ∀ {α} → α ∈ Δ → AExp Δ α
    SCst : ℕ → AExp Δ SNum
    SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
    SLam : ∀ {α₁ α₂}   → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
    SApp : ∀ {α₁ α₂}   → AExp Δ (SFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
    DCst : ℕ → AExp Δ (D Num)
    DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
    DLam : ∀ {σ₁ σ₂}   → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
    DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)
    SPair  : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ α₂ → AExp Δ (SPrd α₁ α₂)
    SInl   : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ (SSum α₁ α₂)
    SInr   : ∀ {α₁ α₂} → AExp Δ α₂ → AExp Δ (SSum α₁ α₂)
    SFst  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₁
    SSnd  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₂
    SCase : ∀ {α₁ α₂ α₃} → AExp Δ (SSum α₁ α₂) → AExp (α₁ ∷ Δ) α₃ → AExp (α₂ ∷ Δ) α₃ → AExp Δ α₃
    DPair  : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D σ₂) → AExp Δ (D (Prd σ₁ σ₂))
    DInl   : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D (Sum σ₁ σ₂))
    DInr   : ∀ {σ₁ σ₂} → AExp Δ (D σ₂) → AExp Δ (D (Sum σ₁ σ₂))
    DFst  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₁)
    DSnd  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₂)
    DCase : ∀ {σ₁ σ₂ σ₃} → AExp Δ (D (Sum σ₁ σ₂)) → AExp ((D σ₁) ∷ Δ) (D σ₃) → AExp ((D σ₂) ∷ Δ) (D σ₃) → AExp Δ (D σ₃) 
    ↑     : ∀ {α} → Liftable α → AExp Δ α  → AExp Δ (D (typeof α))


  
  module Weakening where
    
    elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
    elevate-var refl x = x
    elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)

    elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
    elevate-var2 (refl x) x₁ = elevate-var x x₁
    elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
    elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)

    elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
    elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
    elevate Γ↝Γ'↝Γ'' (ECst x) = ECst x
    elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
    elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (extend Γ↝Γ'↝Γ'') e)
    elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
    elevate Γ↝Γ'↝Γ'' (EPair e e₁) = EPair (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
    elevate Γ↝Γ'↝Γ'' (EInl e) = EInl (elevate Γ↝Γ'↝Γ'' e)
    elevate Γ↝Γ'↝Γ'' (EInr e) = EInr (elevate Γ↝Γ'↝Γ'' e)
    elevate Γ↝Γ'↝Γ'' (EFst e) = EFst (elevate Γ↝Γ'↝Γ'' e)
    elevate Γ↝Γ'↝Γ'' (ESnd e) = ESnd (elevate Γ↝Γ'↝Γ'' e)
    elevate Γ↝Γ'↝Γ'' (ECase c e₁ e₂) = ECase (elevate Γ↝Γ'↝Γ'' c) (elevate (extend Γ↝Γ'↝Γ'') e₁) (elevate (extend Γ↝Γ'↝Γ'') e₂)

    exp↑ : ∀ {τ Γ Γ'} → Γ ↝ Γ' → Exp Γ τ → Exp Γ' τ
    exp↑ Γ↝Γ' e = elevate (refl Γ↝Γ') e
  
  open Weakening public


  module Correctness where

    ---------------------------
    --strip off two-level types
    ---------------------------
    stripα = typeof

    stripΔ : ACtx → Ctx
    stripΔ = map stripα

    strip-lookup : ∀ { α Δ} → α ∈ Δ → stripα α ∈ stripΔ Δ
    strip-lookup hd = hd
    strip-lookup (tl x) = tl (strip-lookup x)
      
    ---------------------------
    --strip off two-level terms
    ---------------------------
    strip : ∀ {α Δ} → AExp Δ α → Exp (stripΔ Δ) (stripα α)
    strip (Var x) = EVar (strip-lookup x)
    strip (SCst x) = ECst x
    strip (SAdd e e₁) = EAdd (strip e) (strip e₁)
    strip (SLam e) = ELam (strip e)
    strip (SApp e e₁)  = EApp (strip e) (strip e₁)
    strip (DCst x)  = ECst x
    strip (DAdd e e₁) = EAdd (strip e) (strip e₁)
    strip (DLam e)  = ELam (strip e)
    strip (DApp e e₁)  = EApp (strip e) (strip e₁)
    strip (SPair e e₁)  = EPair (strip e) (strip e₁) 
    strip (SInl e)  = EInl (strip e)
    strip (SInr e)  = EInr (strip e)
    strip (SFst e)  = EFst (strip e)
    strip (SSnd e)  = ESnd (strip e)
    strip (SCase e e₁ e₂)  = ECase (strip e) (strip e₁) (strip e₂)
    strip (DPair e e₁)  = EPair (strip e) (strip e₁) 
    strip (DInl e)  = EInl (strip e)
    strip (DInr e)  = EInr (strip e)
    strip (DFst e)  = EFst (strip e)
    strip (DSnd e)  = ESnd (strip e)
    strip (DCase e e₁ e₂)  = ECase (strip e) (strip e₁) (strip e₂)
    strip (↑ x e) = strip e

    stripLift : ∀ {α Δ Γ} → stripΔ Δ ↝ Γ → AExp Δ α  → Exp Γ (stripα α)
    stripLift Δ↝Γ = exp↑ Δ↝Γ ∘ strip


  open Correctness public 


   ----------------------------------
--module "TwoLevelTerms-Simp-PSRI"
--note: it includes
--a)weakening lemmas.
----------------------------------- 
module TwoLevelTerms-Simp-PSRI where
  open Auxiliaries
  open import Types
  open two-level-types-simp-ps  


  ----------------------------------
  --helper for evaluating recursors.
  ----------------------------------
  natrec : ∀ {t : Set} → ℕ → t → (ℕ → (t → t)) → t
  natrec zero v0 vs = v0
  natrec (suc n) v0 vs = vs n (natrec n v0 vs)
  
  ----------------------------------
  --helper for evaluating iterators.
  ----------------------------------
  natit : ∀ { t : Set } → ℕ → t → (t → t) → t
  natit zero v0 vs = v0
  natit (suc n) v0 vs = vs (natit n v0 vs)
  


-------------------------------------------------------------------------------
--module "DB&PHOAS"
--note: it includes
--1)weakening lemmas.
-------------------------------------------------------------------------------
module DB&PHOAS where
  open TwoLevelTypes-Simp public
  
  -------------------------
  --module "DB-Terms"
  --note: some weakening lemmas involving 
  --      "De Bruijn" terms
  -------------------------
  module DB-terms where
    open Auxiliaries
    open import Types
    open two-level-types-simp
    open import Terms
    open two-level-terms-DB&PHOAS
  
    

  open DB-terms public
 

    
    