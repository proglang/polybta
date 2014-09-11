---------------------------------------------
--base terms [Exp] and two-level terms [AExp]
---------------------------------------------
module Terms where
  open import Data.List
  open import Data.Nat
  open import Types

  infix 4 _∈_
  data _∈_ {A : Set} : A → List A → Set where
    hd : ∀ {x xs} → x ∈ (x ∷ xs)
    tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

  ------------------------------------
  --module "two-level-terms"
  --note: annotated terms of annotated types
  --a)base-level terms [Exp] and two-level terms [AExp].
  ------------------------------------
  module two-level-terms where
    open two-level-types 

    data Exp (Γ : Ctx) : Type → Set where
      EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
      ECst : ℕ → Exp Γ TNum
      ELam : ∀ {τ₁ τ₂} → Exp (τ₂ ∷ Γ) τ₁ → Exp Γ (TFun τ₂ τ₁)
      EApp : ∀ {τ₁ τ₂} → Exp Γ (TFun τ₂ τ₁) → Exp Γ τ₂ → Exp Γ τ₁

    data AExp (Δ : ACtx) : AType → Set where
      Var : ∀ {α} → α ∈ Δ → AExp Δ α
      Cst : (bt : BT) → ℕ → AExp Δ (ATNum bt)
      Lam : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp (α₂ ∷ Δ) α₁ → AExp Δ (ATFun bt α₂ α₁)
      App : ∀ {α₁ α₂} (bt : BT) → wft (ATFun bt α₂ α₁) → AExp Δ (ATFun bt α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
  

  --------------------------------------------------------
  --module "two-level-terms-simp"
  --note: terms of types where "well-formedness" is incorporated
  --a)base-level terms [Exp] and two-level terms [AExp].
  --------------------------------------------------------
  module two-level-terms-simp where
    open two-level-types-simp 

    data Exp (Γ : Ctx) : Type → Set where
      EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
      ECst : ℕ → Exp Γ Num
      EAdd : Exp Γ Num → Exp Γ Num -> Exp Γ Num
      ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
      EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'

    data AExp (Δ : ACtx) : AType → Set where
      Var : ∀ {α} → α ∈ Δ → AExp Δ α
      SCst : ℕ → AExp Δ SNum
      SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
      SLam : ∀ {α₁ α₂}   → AExp (α₂ ∷ Δ) α₁ → AExp Δ (SFun α₂ α₁)
      SApp : ∀ {α₁ α₂}   → AExp Δ (SFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
      DCst : ℕ → AExp Δ (D Num)
      DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
      DLam : ∀ {α₁ α₂}   → AExp ((D α₂) ∷ Δ) (D α₁) → AExp Δ (D (Fun α₂ α₁))
      DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)
    

  --------------------------------------------
  --module "two-level-terms-simp-lift"
  --note: extended with "lifting" constructor [lift]
  --a)base-level terms [Exp] and two-level terms [AExp].
  --------------------------------------------
  module two-level-terms-simp-lift where
    open two-level-types-simp 

    data Exp (Γ : Ctx) : Type → Set where
      EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
      ECst : ℕ → Exp Γ Num
      EAdd : Exp Γ Num → Exp Γ Num -> Exp Γ Num
      ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
      EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ')  → Exp Γ τ → Exp Γ τ'

    data AExp (Δ : ACtx) : AType → Set where
      Var : ∀ {α} → α ∈ Δ → AExp Δ α
      SCst : ℕ → AExp Δ SNum
      SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
      SLam : ∀ {α₁ α₂}   → AExp (α₂ ∷ Δ) α₁ → AExp Δ (SFun α₂ α₁)
      SApp : ∀ {α₁ α₂}   → AExp Δ (SFun α₂ α₁) → AExp Δ α₂ → AExp Δ α₁
      DCst : ℕ → AExp Δ (D Num)
      DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
      DLam : ∀ {α₁ α₂}   → AExp ((D α₂) ∷ Δ) (D α₁) → AExp Δ (D (Fun α₂ α₁))
      DApp : ∀ {α₁ α₂}   → AExp Δ (D (Fun α₂ α₁)) → AExp Δ (D α₂) → AExp Δ (D α₁)
      Lift : AExp Δ SNum → AExp Δ (D Num)

  -----------------------------------------------------
  --module "two-level-terms-simp-lift-psri"
  --note: extended with paris, sums, recursors, and iterators
  --a)liftable criterion;
  --b)base-level terms [Exp] and two-level terms [AExp].
  -----------------------------------------------------
  module two-level-terms-simp-lift-psri where
    open two-level-types-simp-ps 

    -------------------------------
    --a simple "liftable criterion"
    -------------------------------
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

    --------------------------
    --some auxiliary functions
    --------------------------
    typeof : AType → Type
    typeof SNum = Num
    typeof (SFun α₁ α₂) = Fun (typeof α₁) (typeof α₂) 
    typeof (D x) = x
    typeof (SPrd α₁ α₂) = Prd (typeof α₁) (typeof α₂)
    typeof (SSum α₁ α₂) = Sum (typeof α₁) (typeof α₂)
    
    data Exp (Γ : Ctx) : Type → Set where
      EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
      ECst : ℕ → Exp Γ Num
      ESuc : Exp Γ Num → Exp Γ Num
      EIt  : ∀ {τ} → Exp Γ Num → Exp Γ τ → Exp Γ (Fun τ τ) → Exp Γ τ
      ERec : ∀ {τ} → Exp Γ τ → Exp Γ (Fun Num (Fun τ τ)) → Exp Γ Num
                  → Exp Γ τ
      EAdd  : Exp Γ Num → Exp Γ Num → Exp Γ Num
      ELam  : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
      EApp  : ∀ {τ τ'} → Exp Γ (Fun τ τ') → Exp Γ τ → Exp Γ τ'
      EPair : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (Prd τ τ')
      EFst  :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ
      ESnd  :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ'
      EInl  :  ∀ {τ τ'} → Exp Γ τ → Exp Γ (Sum τ τ')
      EInr  :  ∀ {τ τ'} → Exp Γ τ' → Exp Γ (Sum τ τ')
      ECase : ∀ {τ τ' τ''} → Exp Γ (Sum τ τ') →
                Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''

    data AExp (Δ : ACtx) : AType → Set where
      Var  : ∀ {α} → α ∈ Δ → AExp Δ α
      SCst : ℕ → AExp Δ SNum
      SSuc : AExp Δ SNum → AExp Δ SNum
      SIt  : ∀ {α} → AExp Δ SNum → AExp Δ α → AExp Δ (SFun α α) → AExp Δ α
      SRec : ∀ {α} → AExp Δ α → AExp Δ (SFun SNum (SFun α α)) → AExp Δ SNum 
                 → AExp Δ α
      SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
      SLam : ∀ {α₁ α₂} → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
      SApp : ∀ {α₁ α₂} → AExp Δ (SFun α₁ α₂) → AExp Δ α₁ → AExp Δ α₂
      DCst : ℕ → AExp Δ (D Num)
      DSuc : AExp Δ (D Num) → AExp Δ (D Num)
      DIt  : ∀ {σ} → AExp Δ (D Num) → AExp Δ (D σ) → AExp Δ (D (Fun σ σ)) → AExp Δ (D σ)
      DRec : ∀ {σ} → AExp Δ (D σ) → AExp Δ (D (Fun Num (Fun σ σ))) → AExp Δ (D Num) 
                 → AExp Δ (D σ)
      DAdd  : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
      DLam  : ∀ {σ₁ σ₂} → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
      DApp  : ∀ {σ₁ σ₂} → AExp Δ (D (Fun σ₂ σ₁)) → AExp Δ (D σ₂) → AExp Δ (D σ₁)
      SPair : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ α₂ → AExp Δ (SPrd α₁ α₂)
      SInl  : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ (SSum α₁ α₂)
      SInr  : ∀ {α₁ α₂} → AExp Δ α₂ → AExp Δ (SSum α₁ α₂)
      SFst  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₁
      SSnd  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₂
      SCase : ∀ {α₁ α₂ α₃} → AExp Δ (SSum α₁ α₂) → AExp (α₁ ∷ Δ) α₃ → AExp (α₂ ∷ Δ) α₃ → AExp Δ α₃
      DPair : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D σ₂) → AExp Δ (D (Prd σ₁ σ₂))
      DInl  : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D (Sum σ₁ σ₂))
      DInr  : ∀ {σ₁ σ₂} → AExp Δ (D σ₂) → AExp Δ (D (Sum σ₁ σ₂))
      DFst  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₁)
      DSnd  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₂)
      DCase : ∀ {σ₁ σ₂ σ₃} → AExp Δ (D (Sum σ₁ σ₂)) → AExp ((D σ₁) ∷ Δ) (D σ₃) → AExp ((D σ₂) ∷ Δ) (D σ₃) → AExp Δ (D σ₃) 
      Lift  : {α : AType} →
              Liftable α → AExp Δ α  → AExp Δ (D (typeof α))

  --------------------------------------------------------
  --module "two-level-terms-DB&PHOAS"
  --note: terms used in translations between "De Bruijn" terms
  --      and "PHOAS" terms
  --a)"De Bruijn" terms [Exp] and [AExp];
  --b)"PHOAS" terms [exp] and [aexp];
  --c)liftable criteria [liftable1] and [liftable2].
  --------------------------------------------------------
  module two-level-terms-DB&PHOAS where
    open two-level-types-simp 
    
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

    ----------------------
    --module "PHOAS-Terms"
    --note: PHOAS terms
    ----------------------
    module PHOAS-Terms where
      open two-level-types-simp

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

   

 
    