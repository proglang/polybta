module PE-STLCfix where
open import Data.Nat public
open import Lib public
open Auxiliaries public
open TwoLevelTerms-Simp-PSRI public hiding (natrec)
open import Data.Product 
open import Data.Maybe 

data Type : Set where
  Num : Type
  Fun : Type → Type → Type
  
Ctx : Set
Ctx = List Type

data Exp (Γ : Ctx) : Type → Set where
  Var : forall {σ} → σ ∈ Γ → Exp Γ σ
  C : ℕ → Exp Γ Num
  Dspℕ : forall {σ} → Exp Γ Num 
                       → Exp Γ σ
                       → Exp (Num ∷ Γ) σ 
                       → Exp Γ σ
--note:
--[Dspℕ] allows to dispatch upon the natural number

  Suc : Exp Γ Num → Exp Γ Num
  Lam : ∀ {σ₂} σ₁ → Exp (σ₁ ∷ Γ) σ₂ → Exp Γ (Fun σ₁ σ₂)
  App : ∀ {σ₁ σ₂} → Exp Γ (Fun σ₁ σ₂) → Exp Γ σ₁ → Exp Γ σ₂
  Rec : ∀ {σ} → Exp Γ σ → Exp Γ (Fun Num (Fun σ σ)) → Exp Γ Num → Exp Γ σ
--the introduction of [Rec] here corresponds to the using of a static recursor
--in the two-level language in place of a static fix-point operator
  Fix : ∀ {σ₁ σ₂} → Exp Γ (Fun (Fun σ₁ σ₂) (Fun σ₁ σ₂)) → Exp Γ (Fun σ₁ σ₂) 
--[Fix] operator allows in the function body the possibility of referring to the 
--function itself



---------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------
--note:
--a)low-level language does not contain "recursor" which can be constructed
--  using fix-point constructor as recursor


recursor : ∀ {σ} {Γ} → Exp Γ (Fun (Fun Num (Fun σ σ)) (Fun Num (Fun σ σ)))
recursor {σ} {Γ} = Lam (Fun Num (Fun σ σ)) (Fix (Lam (Fun Num (Fun σ σ)) 
                   (Lam Num 
                   (Lam σ 
                   (Dspℕ (Var (tl hd)) (Var hd) (App (App (Var (tl (tl (tl (tl hd))))) (Var (tl (tl hd)))) 
                                                     (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd)))))))))  
---------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------

--now evaluation
--type interpretation
--idea:
--a)[Num] is interpreted as ℕ
--b)[Fun σ₁ σ₂] is interpreted as
--  interpret(σ₁) → interpret(σ₂)
--c)with [Fix] now we have to deal
--  with functions which infinitely
--  call itself(non-termination)
--d)one way to get pass Agda's termination
--  check is to set the upper bound of
--  the number of recursive unfoldings
--  and any evaluation which needs to
--  unfold more is discarded
--e)therefore we have the type interpretation as
--  follows,



Int : Type → Set
Int Num = ℕ
Int (Fun σ₁ σ₂) = Maybe (Int σ₁) → Maybe (Int σ₂)
--note: the reason for the above interpretation of function type
--

data Env : Ctx → Set where
    []  : Env [] 
    _∷_ : ∀ {σ : Type} {Γ : Ctx} → Maybe (Int σ) → Env Γ → Env (σ ∷ Γ)

--partial evaluation of [Type] terms
lookup : ∀ {σ Γ} → σ ∈ Γ → Env Γ → Maybe (Int σ)
lookup hd (x ∷ env) = x
lookup (tl id) (x ∷ env) = lookup id env


Natrec : ∀ {t : Set} → ℕ → t →  Maybe (Maybe ℕ → Maybe (Maybe t → Maybe t)) → Maybe t
Natrec zero v0 vs = just v0
Natrec (suc n) v0 vs with vs 
Natrec (suc n) v0 vs | just vs' with (Natrec n v0 vs) 
Natrec (suc n) v0 vs | just vs' | just r with vs' (just n) 
Natrec (suc n) v0 vs | just vs' | just r | just vs'' = vs'' (Natrec n v0 vs) 
Natrec (suc n) v0 vs | just vs' | just r | nothing = nothing
Natrec (suc n) v0 vs | just vs' | nothing = nothing
Natrec (suc n) v0 vs | nothing = nothing



natrec : ∀ {t : Set} → ℕ → t → (ℕ → (t → t)) → t
natrec zero v0 vs = v0
natrec (suc n) v0 vs = vs n (natrec n v0 vs)


ev : ∀ {σ Γ} → ℕ → Exp Γ σ → Env Γ → Maybe (Int σ)
ev n (Var x) env = lookup x env
ev n (C x) env = just x
ev n (Dspℕ e e₁ e₂) env with ev n e env 
... | just 0       = ev n e₁ env
... | just (suc m) = ev n e₂ (just m ∷ env)
... | nothing       = nothing
ev n (Suc e) env with ev n e env
... | just m = just (suc m)
... | nothing = nothing
ev n (Lam σ₁ e) env = just (λ y → ev n e (y ∷ env))
ev n (App e e₁) env with ev n e env
... | just f = f (ev n e₁ env)
... | nothing = nothing
ev n (Rec v u m) env with ev n m env | ev n v env 
... | just n' | just v'  = Natrec n' v' (ev n u env) 
... | _ | _  = nothing

ev zero (Fix e) env = nothing
ev (suc n) (Fix e) env with ev n e env
... | just f = f (ev n (Fix e) env)
... | nothing = nothing




------------------------------------------------------
--two level types and terms


data AType : Set where
  D    : Type → AType
  SFun : AType → AType → AType
  SNum : AType
    
ACtx : Set
ACtx = List AType
  
--note
--a)the two-level language does not contain "static fix-point constructor"
--  for we want to have clear-cut evaluation results
--b)the fix-point constructor is being replaced by a static recursor instead

--recap: recursor
--a)a recursor constructor takes three inputs, 1)a natural number representing
--  number of recursive calls, 2)the recursive function itself, 3)the default 
--  value when the recursive number turns to zero
--b)in the presence of product types,recursor is equivalent to iterator 
 
data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  SC : ℕ → AExp Δ SNum
  DC : ℕ → AExp Δ (D Num)
  SDspℕ : ∀ {α} → AExp Δ SNum 
                          → AExp Δ α 
                          → AExp (SNum ∷ Δ) α
                          → AExp Δ α
  DDspℕ : ∀ {σ} → AExp Δ (D Num) 
                          → AExp Δ (D σ) 
                          → AExp (D Num ∷ Δ) (D σ) 
                          → AExp Δ (D σ)
  SSuc : AExp Δ SNum → AExp Δ SNum
  DSuc : AExp Δ (D Num) → AExp Δ (D Num)
  SLam : ∀ {α₂} α₁ → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
  DLam : ∀ {σ₂} σ₁ → AExp (D σ₁ ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  SApp : ∀ {α₁ α₂} → AExp Δ (SFun α₁ α₂) → AExp Δ α₁ → AExp Δ α₂
  DApp : ∀ {σ₁ σ₂} → AExp Δ (D (Fun σ₁ σ₂)) → AExp Δ (D σ₁) → AExp Δ (D σ₂)
  SRec : ∀ {α} → AExp Δ α → AExp Δ (SFun SNum (SFun α α)) → AExp Δ SNum → AExp Δ α
  --note: a recursor constructor taking 
  --a)a default value
  --b)a recursive function
  --c)a natural number indicating the number of recursive calls  
  DFix : ∀ {σ₁ σ₂} → AExp Δ (D (Fun (Fun σ₁ σ₂) (Fun σ₁ σ₂))) → AExp Δ (D (Fun σ₁ σ₂))




ATInt : Ctx -> AType -> Set
ATInt Γ SNum = ℕ
ATInt Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → ATInt Γ' α₁ → ATInt Γ' α₂
ATInt Γ (D σ) = Exp Γ σ
  
elevate-var : ∀ {Γ Γ'} {σ : Type} → Γ ↝ Γ' → σ ∈ Γ → σ ∈ Γ'
elevate-var refl x = x
elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)
  
elevate-var2 : ∀ {Γ Γ' Γ'' σ} → Γ ↝ Γ' ↝ Γ'' → σ ∈ Γ → σ ∈ Γ''
elevate-var2 (refl x) x₁ = elevate-var x x₁
elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)
 
elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ 
elevate Γ↝Γ'↝Γ'' (Var x) = Var (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (C x) = C x
elevate Γ↝Γ'↝Γ'' (Dspℕ e e₁ e₂) = Dspℕ (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁) (elevate (extend Γ↝Γ'↝Γ'') e₂)
elevate Γ↝Γ'↝Γ'' (Suc e) = Suc (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (Lam σ₁ e) = Lam σ₁ (elevate (extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (App e e₁) = App (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (Rec v u n) = Rec (elevate Γ↝Γ'↝Γ'' v) (elevate Γ↝Γ'↝Γ'' u) (elevate Γ↝Γ'↝Γ'' n)
elevate Γ↝Γ'↝Γ'' (Fix e) = Fix (elevate Γ↝Γ'↝Γ'' e) 

exp↑ : ∀ {σ Γ Γ'} → Γ ↝ Γ' → Exp Γ σ → Exp Γ' σ
exp↑ Γ↝Γ' e = elevate (refl Γ↝Γ') e

atint↑ : ∀ {α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
atint↑ {D x} Γ↝Γ' atint = exp↑ Γ↝Γ' atint
atint↑ {SFun α α₁} {Γ} {Γ'} Γ↝Γ' atint = λ {Γ''} Γ'↝Γ'' → atint {Γ''} (Γ↝Γ' ⊕ Γ'↝Γ'')
atint↑ {SNum} Γ↝Γ' atint = atint



data AEnv (Γ : Ctx) : ACtx → Set where
  []  : AEnv Γ []
  _∷_ : ∀ {α Δ} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)



aenv↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
aenv↑ Γ↝Γ' [] = []
aenv↑ Γ↝Γ' (x ∷ aenv) = atint↑ Γ↝Γ' x ∷ aenv↑ Γ↝Γ' aenv


addfresh : ∀ {σ Γ Δ} → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
addfresh aenv = (Var hd) ∷ aenv↑ (extend refl) aenv


Lookup : ∀ {α Γ Δ} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α 
Lookup hd (x ∷ aenv) = x
Lookup (tl id) (x ∷ aenv) = Lookup id aenv

pe : ∀ {α Γ Δ} → AExp Δ α → AEnv Γ Δ → ATInt Γ α  
pe (Var x) aenv = Lookup x aenv
pe (SC x) aenv = x
pe (DC x) aenv = C x
pe (SDspℕ e e₁ e₂) aenv with pe e aenv
... | 0      = pe e₁ aenv
... | suc n  = pe e₂ (n ∷ aenv)
pe (DDspℕ e e₁ e₂) aenv = Dspℕ (pe e aenv) (pe e₁ aenv) (pe e₂ (addfresh aenv))
pe (SSuc e) aenv = suc (pe e aenv)
pe (DSuc e) aenv = Suc (pe e aenv)
pe (SLam α₁ e) aenv = λ Γ↝Γ' → λ y → pe e (y ∷ aenv↑ Γ↝Γ' aenv)
pe (DLam σ₁ e) aenv = Lam σ₁ (pe e (addfresh aenv))
pe (SApp e e₁) aenv = pe e aenv refl (pe e₁ aenv)
pe (DApp e e₁) aenv = App (pe e aenv) (pe e₁ aenv)
pe {Γ = Γ} (SRec v u n) aenv = natrec (pe n aenv) (pe v aenv)
                                 (λ n₁ → pe u aenv {Γ} refl n₁ {Γ} refl)
pe (DFix e) aenv = Fix (pe e aenv)


