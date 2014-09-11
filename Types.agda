--------------------------------------
--"two level types" [Type] and [AType]
--------------------------------------
module Types where
  open import Data.List
  open import Data.Bool

  ---------------------------------------------
  --module "two-level-types"
  --note: two-level annotated types where
  --      "well-formedness" is not incorporated
  --      into the typing system
  --a)[Type] and [AType];
  --b)"well-formedness" criterion;
  --c)typing contexts [Ctx] and [ACtx].
  ---------------------------------------------
  module two-level-types where 
    
    data BT : Set where
      S : BT
      D : BT

    data Type : Set where
      TNum : Type
      TFun : Type → Type → Type

    mutual
      data AType : Set where
        Ann : BT → SType → AType
  
      data SType : Set where
        SNum  : SType
        SFun  : AType → AType → SType

    --------------------------
    --some auxiliary functions
    --------------------------
    record True : Set where
    data False : Set where

    isTrue : Bool → Set
    isTrue true  = True
    isTrue false = False

    ATNum : BT → AType
    ATNum bt = Ann bt SNum

    ATFun  : BT → AType → AType → AType
    ATFun  bt at1 at2 = Ann bt (SFun at1 at2)
    
    btof : AType → BT
    btof (Ann bt _) = bt

    _≼_ : BT → BT → Bool
    _≼_ D S  = false
    _≼_ _ _  = true
    
    ---------------------------
    --well-formedness criterion
    ---------------------------
    data wft : AType → Set where
      wf-int  : ∀ {bt} → wft (Ann bt SNum)
      wf-fun  : ∀ {bt at1 at2} → wft at1 → wft at2
                    → isTrue (bt ≼ btof at1) → isTrue (bt ≼ btof at2) → wft (Ann bt (SFun at1 at2))


    -----------------
    --typing contexts
    -----------------
    Ctx  = List Type
    ACtx = List AType
  
 
  -----------------------------------------------
  --module "two-level-types-simp"
  --note: two-level types where "well-formedness" 
  --      is incorporated into the typing system
  --a)[Type] and [AType];
  --b)typing contexts [Ctx] and [ACtx].
  -----------------------------------------------
  module two-level-types-simp where

    data Type : Set where
      Num : Type
      Fun : Type → Type → Type

    data AType : Set where
      SNum  : AType
      SFun  : AType → AType → AType
      D     : Type → AType

    -----------------
    --typing contexts
    -----------------
    Ctx  = List Type
    ACtx = List AType

  ---------------------------------------
  --module "two-level-types-simp-ps"
  --note: two-level types extended with pairs 
  --      and sums
  --a)[Type] and [AType];
  --b)typing contexts [Ctx] and [ACtx].
  ---------------------------------------
  module two-level-types-simp-ps where

    data Type : Set where
      Num : Type
      Fun : Type → Type → Type
      Prd : Type  → Type  → Type   
      Sum : Type → Type → Type


    data AType : Set where
      SNum  : AType
      SFun  : AType → AType → AType
      D     : Type → AType
      SPrd   : AType → AType → AType 
      SSum   : AType → AType → AType 

    -----------------
    --typing contexts
    -----------------
    Ctx  = List Type
    ACtx = List AType
  
  