-----------------------------------------------------
--translating from "PHOAS" terms to "De Bruijn" terms
-----------------------------------------------------
module PHOAS2DB where
open import Data.Bool 
open import Lib
open Auxiliaries
open DB&PHOAS
open import Types
open two-level-types-simp


--------------------------
--two-level-terms-DB&PHOAS
--------------------------
-------------------
--"De Bruijn" terms
-------------------
module DB-Terms where

  data Exp (Γ : Ctx) : Type → Set where
    EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
    ECst : ℕ → Exp Γ Num
    EAdd : Exp Γ Num → Exp Γ Num -> Exp Γ Num
    ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
    EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'
   
  module liftable where
      
    typeof : AType → Type
    typeof SNum = Num
    typeof (SFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
    typeof (D x) = x

    -----------------------------------
    --a less powerful lifting criterion
    -----------------------------------
    data liftable1 : AType → Set where
      base : ∀ {x : Type} → liftable1 (D x)
      Func : ∀ {α₁ α₂ : AType} 
              → liftable1 α₁ → liftable1 α₂
              → liftable1 (SFun α₁ α₂)

    ---------------------------------------------
    --[liftable] in [BTA9] without pairs and sums
    ---------------------------------------------
    mutual 
      data Liftable2 : AType → Set where
        D : ∀ τ → Liftable2 (D τ)
        SCst : Liftable2 SNum
        SFun : ∀ {α₁ α₂} → Liftable2⁻ α₁ → Liftable2 α₂ → Liftable2 (SFun α₁ α₂)

      data Liftable2⁻ : AType → Set where
        D : ∀ τ → Liftable2⁻ (D τ)
        SFun : ∀ {α₁ α₂} → Liftable2 α₁ → Liftable2⁻ α₂ → Liftable2⁻ (SFun α₁ α₂)
   
  open liftable public


  data AExp (Δ : ACtx) : AType → Set where
    Var : ∀ {α} → α ∈ Δ → AExp Δ α
    SCst : ℕ → AExp Δ SNum
    SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
    SLam : ∀ {α₁ α₂}   → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
    SApp : ∀ {α₁ α₂}   → AExp Δ (SFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
    DCst : ℕ → AExp Δ (D Num)
    DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
    DLam : ∀ {τ₁ τ₂}   → AExp ((D τ₁) ∷ Δ) (D τ₂) → AExp Δ (D (Fun τ₁ τ₂))
    DApp : ∀ {τ₁ τ₂}   → AExp Δ (D (Fun τ₂ τ₁)) → AExp Δ (D τ₂) → AExp Δ (D τ₁)
    ↑    : ∀  {α} → liftable1 α → AExp Δ α → AExp Δ (D (typeof α))

open DB-Terms public

-------------------
--"PHOAS" terms
-------------------
module PHOAS-Terms where
  
   data exp (var : Type → Set) : Type → Set where
     EVar : ∀ {A} → var A → exp var A
     ECst : ℕ → exp var Num
     EAdd : exp var Num → exp var Num → exp var Num
     ELam : ∀ {A B} → (var A → exp var B) → exp var (Fun A B)
     EApp : ∀ {A B} → exp var (Fun A B) → exp var A → exp var B

   data aexp (var : AType → Set) : AType → Set where
     Var  : ∀ {A} → var A → aexp var A
     SCst : ℕ → aexp var SNum
     SAdd : aexp var SNum → aexp var SNum → aexp var SNum
     SLam : ∀ {A B} → (var A → aexp var B) → aexp var (SFun A B)
     SApp : ∀ {A B} → aexp var (SFun A B) → aexp var A → aexp var B
     DCst : ℕ → aexp var (D Num)
     DAdd : aexp var (D Num) → aexp var (D Num) → aexp var (D Num)
     DLam : ∀ {a b} → (var (D a) → aexp var (D b)) → aexp var (D (Fun a b))
     DApp : ∀ {a b} → aexp var (D (Fun a b)) → aexp var (D a) → aexp var (D b)
     ↑    : ∀  {α} → liftable1 α → aexp var α → aexp var (D (typeof α))
  
open PHOAS-Terms public   

--------------------------------
--module "auxiliaries"
--note: some auxiliary functions 
--      coming in handy later
--------------------------------
module auxiliaries where

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

  Some≡ : ∀ {a : AType} {b : AType} → Some a ≡ Some b → a ≡ b
  Some≡ {SNum} {SNum} eq = refl
  Some≡ {SNum} {SFun b b₁} ()
  Some≡ {SNum} {D x} ()
  Some≡ {SFun a a₁} {SNum} ()
  Some≡ {SFun .b .b₁} {SFun b b₁} refl = refl
  Some≡ {SFun a a₁} {D x} ()
  Some≡ {D x} {SNum} ()
  Some≡ {D x} {SFun b b₁} ()
  Some≡ {D .x₁} {D x₁} refl = refl

  LookUp : ℕ → ACtx → Option AType 
  LookUp n [] = Nothing
  LookUp n (x ∷ Δ) with ℕ≡? n (Length Δ) 
  ... | true = Some x
  ... | false = LookUp n Δ


----------------------------------------------------------------------
--module "PHOAS→DB"
--note: 
--a)the main difficulty here is to compute
--  the "De Bruijn" index of variable occurrences
--  corresponding to where the "PHOAS values" are
--  stored in the environment [Env];
--b)in the context of a generalized interpreter 
--  [var : AType → Set], computing the corresponding
--  indices is not possible for the domain of [Set]
--  is "infinite";
--c)one fix is to specify [var] as function [avar] which 
--  returns "De Bruijn Level" indices;
--d)in order to guarantee that "De Bruijn Level" indices 
--  are consistent with the typing context for the corresponding
--  DB terms [Δ],a "well-formedness" restriction [WF] is imposed
--  over the PHOAS terms to be projected;
--e)note that "De Bruijn Level" indices stays the same when the 
--  context is weakened;
--f)once we have a consistent "De Bruijn Level" index,it can be 
--  converted to the corresponding "De Bruijn" index [DebLeveltoIndex].
-----------------------------------------------------------------------
module PHOAS→DB where
  open auxiliaries
 
  -------------------------------------------------------
  --[avar] a particular interpreter generating 
  --"De Bruijn Level" indices for two-level types [AType]
  -------------------------------------------------------
  avar : AType → Set
  avar _ = ℕ

  -----------------------------------------------------------------------
  --[WF] "well-formedness" restriction over PHOAS terms to guarantee that
  --all "De Bruijn Level" indices are consistent with the typing context
  --[Δ] for the corresponding DB terms
  -----------------------------------------------------------------------
  data WF {Δ : ACtx} : ∀ {A : AType} → aexp avar A → Set where
    WF-Var : ∀ {A : AType} {n : ℕ} → LookUp n Δ ≡ Some A → WF {Δ} {A} (Var n)
    WF-SCst : ∀ {n : ℕ} → WF {Δ} {SNum} (SCst n)
    WF-SAdd : ∀ {e} {e'} → WF {Δ} {SNum} e → WF {Δ} {SNum} e' → WF {Δ} {SNum} (SAdd e e')
    WF-SLam : ∀ {A : AType} {B : AType} {e : avar A → aexp avar B}
                 → WF {A ∷ Δ} {B} (e (Length Δ)) → WF {Δ} {SFun A B} (SLam e)
    WF-SApp : ∀ {A : AType} {B : AType} {f : aexp avar (SFun A B)} {x : aexp avar A}
                 → WF {Δ} {SFun A B} f → WF {Δ} {A} x → WF {Δ} {B} (SApp f x)
    WF-DCst : ∀ {n : ℕ} → WF {Δ} {D Num} (DCst n)
    WF-DAdd : ∀ {e} {e'} → WF {Δ} {D Num} e → WF {Δ} {D Num} e' → WF {Δ} {D Num} (DAdd e e')
    WF-DLam : ∀ {a : Type} {b : Type} {e : avar (D a) → aexp avar (D b)}
                 → WF {(D a) ∷ Δ} {D b} (e (Length Δ)) → WF {Δ} {D (Fun a b)} (DLam e)
    WF-DApp : ∀ {a : Type} {b : Type} {f : aexp avar (D (Fun a b))} {x : aexp avar (D a)} 
                 → WF {Δ} {D (Fun a b)} f → WF {Δ} {D a} x → WF {Δ} {D b} (DApp f x)
    WF-↑    : ∀ {α : AType} {lft : liftable1 α} {e : aexp avar α} → WF {Δ} {α} e → WF {Δ} {D (typeof α)} (↑ lft e)

  
  ---------------------------------------------------------------
  --[DebLeveltoIndex] a consistent "De Bruijn Level" index can be 
  --converted to the corresponding "De Bruijn" index
  ---------------------------------------------------------------
  DebLeveltoIndex : ∀ {n} {A} {Δ} → LookUp n Δ ≡ Some A → A ∈ Δ
  DebLeveltoIndex {n} {A} {[]} ()
  DebLeveltoIndex {n} {A} {x ∷ Δ} eq with ℕ≡? n (Length Δ) 
  ... | true rewrite Some≡ {x} {A} eq = hd
  ... | false = tl (DebLeveltoIndex {n} {A} {Δ} eq)


  --------------------------------------------------------------------
  --[P2D] translating a "well-formed" PHOAS term into a DB term 
  --given that the type interpreter [var] of the PHOAS terms generates
  --"De Bruijn Level" indices for two-level types 
  --------------------------------------------------------------------
  P2D : ∀ {A : AType} {Δ} 
            → (e : aexp avar A)
            → WF {Δ} {A} e 
            → AExp Δ A
  P2D {A} {Δ} (Var x) (WF-Var x₁) = Var (DebLeveltoIndex x₁)
  P2D (SCst x) wf-e = SCst x
  P2D (SAdd e e₁) (WF-SAdd wf-e wf-e₁) = SAdd (P2D e wf-e) (P2D e₁ wf-e₁)
  P2D {SFun A B} {Δ} (SLam x) (WF-SLam wf-e) = SLam (P2D {B} {A ∷ Δ} (x (Length Δ)) wf-e)
  P2D (SApp e e₁) (WF-SApp wf-e wf-e₁) = SApp (P2D e wf-e) (P2D e₁ wf-e₁)
  P2D (DCst x) wf-e = DCst x
  P2D (DAdd e e₁) (WF-DAdd wf-e wf-e₁) = DAdd (P2D e wf-e) (P2D e₁ wf-e₁)
  P2D {D (Fun A B)} {Δ} (DLam x) (WF-DLam wf-e) = DLam (P2D {D B} {D A ∷ Δ} (x (Length Δ)) wf-e)
  P2D (DApp e e₁) (WF-DApp wf-e wf-e₁) = DApp (P2D e wf-e) (P2D e₁ wf-e₁)
  P2D (↑ lft e) (WF-↑ wf-e) = ↑ lft (P2D e wf-e)












