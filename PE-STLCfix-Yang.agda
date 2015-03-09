module PE-STLCfix-Yang where
open import Data.Nat
open import Lib
open Auxiliaries
open import Data.Product

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
--[NatCase] allows us to dispatch upon
--the natural number

  Suc : Exp Γ Num → Exp Γ Num
  Lam : ∀ {σ₂} σ₁ → Exp (σ₁ ∷ Γ) σ₂ → Exp Γ (Fun σ₁ σ₂)
  App : ∀ {σ₁ σ₂} → Exp Γ (Fun σ₁ σ₂) → Exp Γ σ₁ → Exp Γ σ₂
  Fix : ∀ {σ₁ σ₂} → Exp Γ (Fun (Fun σ₁ σ₂) (Fun σ₁ σ₂)) → Exp Γ (Fun σ₁ σ₂) 

--some examples
--addition(recursive)
--Fix λ f. λ n n'. match n | 0    => n'
--                         | S n  => S (f n n')
                    
--addition(iterative)
--Fix λ f. λ n n'. match n | 0    => n'
--                         | S n  => f (n (S n'))

add : Exp [] (Fun Num (Fun Num Num))
add = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) --dispatch upon the first argument
                     (Var hd)      
                     (Suc (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd)))))))) 
aDD : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
aDD {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
                   (Lam Num 
                   (Lam Num 
                   (Dspℕ (Var (tl hd)) 
                         (Var hd) 
                         (Suc (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd))))))))

add' : Exp [] (Fun Num (Fun Num Num))
add' = Fix (Lam (Fun Num (Fun Num Num)) 
                (Lam Num 
                (Lam Num 
                (Dspℕ (Var (tl hd)) 
                      (Var hd) 
                      (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Suc (Var (tl hd))))))))

aDD' : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
aDD' {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
                (Lam Num 
                (Lam Num 
                (Dspℕ (Var (tl hd)) 
                      (Var hd) 
                      (App (App (Var (tl (tl (tl hd)))) (Var hd)) (Suc (Var (tl hd))))))))

--multiplication(recursive)
--Fix λ f. λ n n'. match n | 0       => 0
--                         | 1       => n'
--                         | S (S n) => n' + (f (S n) n')



mul : Exp [] (Fun Num (Fun Num Num))
mul = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                     (Var (tl hd)) 
                     (App (App aDD (Var (tl (tl hd)))) 
                          (App (App (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

mUL : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
mUL {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                     (Var (tl hd)) 
                     (App (App aDD (Var (tl (tl hd)))) 
                          (App (App (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

mUL' : ∀ {Γ} → Exp Γ (Fun Num (Fun Num Num))
mUL' {Γ} = Fix (Lam (Fun Num (Fun Num Num)) 
               (Lam Num 
               (Lam Num 
               (Dspℕ (Var (tl hd)) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                     (Var (tl hd)) 
                     (App (App aDD' (Var (tl (tl hd)))) 
                          (App (App (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

--factorial(recursive)
--Fix λ f. λ n. match n | 0   => 1
--                      | S n' => n * (f n')

fact : Exp [] (Fun Num Num)
fact = Fix (Lam (Fun Num Num) 
                (Lam Num 
                (Dspℕ (Var hd) 
                      (C 1) 
                      (App (App mUL (Var (tl hd))) 
                           ((App (Var (tl (tl hd))) (Var hd)))))))

--nth Fibonacci number(recursive)
--Fix λ f. λ n. match n | 0        => 0
--                      | 1        => 1
--                      | S (S n') => f (S n') + f n'

fib : Exp [] (Fun Num Num)
fib = Fix (Lam (Fun Num Num) 
               (Lam Num 
               (Dspℕ (Var hd) 
                     (C 0) 
                     (Dspℕ (Var hd) 
                           (C 1) 
                           (App (App aDD (App (Var (tl (tl (tl hd)))) (Var (tl hd)))) (App (Var (tl (tl (tl hd)))) (Var hd)))))))


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
data nothing : Set where
  N : nothing

Int : Type → Set
Int Num = ℕ
Int (Fun σ₁ σ₂) = Int σ₁ ⊎ nothing → Int σ₂ ⊎ nothing

data Env : Ctx → Set where
    []  : Env [] 
    _∷_ : ∀ {σ : Type} {Γ : Ctx} → Int σ ⊎ nothing → Env Γ → Env (σ ∷ Γ)

--partial evaluation of [Type] terms
lookup : ∀ {σ Γ} → σ ∈ Γ → Env Γ → Int σ ⊎ nothing
lookup hd (x ∷ env) = x
lookup (tl id) (x ∷ env) = lookup id env


ev : ∀ {σ Γ} → ℕ → Exp Γ σ → Env Γ → Int σ ⊎ nothing
ev n (Var x) env = lookup x env
ev n (C x) env = inj₁ x
ev n (Dspℕ e e₁ e₂) env with ev n e env 
... | inj₁ 0       = ev n e₁ env
... | inj₁ (suc m) = ev n e₂ (inj₁ m ∷ env)
... | inj₂ _       = inj₂ N
ev n (Suc e) env with ev n e env
... | inj₁ m = inj₁ (suc m)
... | inj₂ _ = inj₂ N
ev n (Lam σ₁ e) env = inj₁ (λ y → ev n e (y ∷ env))
ev n (App e e₁) env with ev n e env
... | inj₁ f = f (ev n e₁ env)
... | inj₂ _ = inj₂ N
ev zero (Fix e) env = inj₂ N
ev (suc n) (Fix e) env with ev n e env
... | inj₁ f = f (ev n (Fix e) env)
... | inj₂ _ = inj₂ N

--some evaluation examples
------------------------------------------------
--note:given sufficient amount of "fuel"
--     evaluator [ev] is expected to return
--     correct result in case recursive function
--     application
------------------------------------------------

--a)sum(recursive)
ex1 : ev 3000 (App (App add (C 1)) (C 6)) [] ≡ inj₁ 7
ex1 = refl

--b)sum(iterative)
ex2 : ev 3000 (App (App add' (C 1)) (C 6)) [] ≡ inj₁ 7
ex2 = refl

--c)multiplication(recursive)
ex3 : ev 3000 (App (App mul (C 5)) (C 6)) [] ≡ inj₁ 30
ex3 = refl

--d)factorial
ex5 : ev 3000 (App fact (C 6)) [] ≡ inj₁ 720
ex5 = refl

--e)nth Fibonacci number
ex6 : ev 3000 (App fib (C 9)) [] ≡ inj₁ 34
ex6 = refl


------------------------------------------------------
--two level types and terms


data AType : Set where
  D    : Type → AType
  SFun : AType → AType → AType
  SNum : AType
    
ACtx : Set
ACtx = List AType
  

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
  SFix : ∀ {α₁ α₂} → AExp Δ (SFun (SFun α₁ α₂) (SFun α₁ α₂)) → AExp Δ (SFun α₁ α₂)
  DFix : ∀ {σ₁ σ₂} → AExp Δ (D (Fun (Fun σ₁ σ₂) (Fun σ₁ σ₂))) → AExp Δ (D (Fun σ₁ σ₂))


--some examples
--addition
ADDD : AExp [] (D (Fun Num (Fun Num Num)))
ADDD = DFix (DLam (Fun Num (Fun Num Num)) 
               (DLam Num 
               (DLam Num 
               (DDspℕ (Var (tl hd)) 
                     (Var hd)      
                     (DSuc (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd)))))))) 

ADDS : AExp [] (SFun SNum (SFun SNum SNum))
ADDS = SFix (SLam (SFun SNum (SFun SNum SNum)) 
               (SLam SNum 
               (SLam SNum 
               (SDspℕ (Var (tl hd)) 
                     (Var hd)      
                     (SSuc (SApp (SApp (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd)))))))) 

AddD : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
AddD {Δ} = DFix (DLam (Fun Num (Fun Num Num)) 
                   (DLam Num 
                   (DLam Num 
                   (DDspℕ (Var (tl hd)) 
                         (Var hd) 
                         (DSuc (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd))))))))

AddS : ∀ {Δ} → AExp Δ (SFun SNum (SFun SNum SNum))
AddS {Δ} = SFix (SLam (SFun SNum (SFun SNum SNum)) 
                   (SLam SNum 
                   (SLam SNum 
                   (SDspℕ (Var (tl hd)) 
                         (Var hd) 
                         (SSuc (SApp (SApp (Var (tl (tl (tl hd)))) (Var hd)) (Var (tl hd))))))))


ADDD' : AExp [] (D (Fun Num (Fun Num Num)))
ADDD' = DFix (DLam (Fun Num (Fun Num Num)) 
                (DLam Num 
                (DLam Num 
                (DDspℕ (Var (tl hd)) 
                      (Var hd) 
                      (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (DSuc (Var (tl hd))))))))

ADDS' : AExp [] (SFun SNum (SFun SNum SNum))
ADDS' = SFix (SLam (SFun SNum (SFun SNum SNum)) 
                (SLam SNum 
                (SLam SNum 
                (SDspℕ (Var (tl hd)) 
                      (Var hd) 
                      (SApp (SApp (Var (tl (tl (tl hd)))) (Var hd)) (SSuc (Var (tl hd))))))))

AddD' : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
AddD' {Δ} = DFix (DLam (Fun Num (Fun Num Num)) 
                (DLam Num 
                (DLam Num 
                (DDspℕ (Var (tl hd)) 
                      (Var hd) 
                      (DApp (DApp (Var (tl (tl (tl hd)))) (Var hd)) (DSuc (Var (tl hd))))))))

AddS' : ∀ {Δ} → AExp Δ (SFun SNum (SFun SNum SNum))
AddS' {Δ} = SFix (SLam (SFun SNum (SFun SNum SNum)) 
                (SLam SNum 
                (SLam SNum 
                (SDspℕ (Var (tl hd)) 
                      (Var hd) 
                      (SApp (SApp (Var (tl (tl (tl hd)))) (Var hd)) (SSuc (Var (tl hd))))))))



MULD : AExp [] (D (Fun Num (Fun Num Num)))
MULD = DFix (DLam (Fun Num (Fun Num Num)) 
               (DLam Num 
               (DLam Num 
               (DDspℕ (Var (tl hd)) 
                     (DC 0) 
                     (DDspℕ (Var hd) 
                     (Var (tl hd)) 
                     (DApp (DApp AddD (Var (tl (tl hd)))) 
                          (DApp (DApp (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

MULS : AExp [] (SFun SNum (SFun SNum SNum))
MULS = SFix (SLam (SFun SNum (SFun SNum SNum)) 
               (SLam SNum 
               (SLam SNum 
               (SDspℕ (Var (tl hd)) 
                     (SC 0) 
                     (SDspℕ (Var hd) 
                     (Var (tl hd)) 
                     (SApp (SApp AddS (Var (tl (tl hd)))) 
                          (SApp (SApp (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

MulD : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
MulD {Δ} = DFix (DLam (Fun Num (Fun Num Num)) 
               (DLam Num 
               (DLam Num 
               (DDspℕ (Var (tl hd)) 
                     (DC 0) 
                     (DDspℕ (Var hd) 
                     (Var (tl hd)) 
                     (DApp (DApp AddD (Var (tl (tl hd)))) 
                          (DApp (DApp (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

MulS : ∀ {Δ} → AExp Δ (SFun SNum (SFun SNum SNum))
MulS {Δ} = SFix (SLam (SFun SNum (SFun SNum SNum)) 
               (SLam SNum 
               (SLam SNum 
               (SDspℕ (Var (tl hd)) 
                     (SC 0) 
                     (SDspℕ (Var hd) 
                     (Var (tl hd)) 
                     (SApp (SApp AddS (Var (tl (tl hd)))) 
                          (SApp (SApp (Var (tl (tl (tl (tl hd))))) (Var (tl hd))) (Var (tl (tl hd)))))
                     )))))

FACTD : AExp [] (D (Fun Num Num))
FACTD = DFix (DLam (Fun Num Num) 
                (DLam Num 
                (DDspℕ (Var hd) 
                      (DC 1) 
                      (DApp (DApp MulD (Var (tl hd))) 
                           ((DApp (Var (tl (tl hd))) (Var hd)))))))

FACTS : AExp [] (SFun SNum SNum)
FACTS = SFix (SLam (SFun SNum SNum) 
                (SLam SNum 
                (SDspℕ (Var hd) 
                      (SC 1) 
                      (SApp (SApp MulS (Var (tl hd))) 
                           ((SApp (Var (tl (tl hd))) (Var hd)))))))



FIBD : AExp [] (D (Fun Num Num))
FIBD = DFix (DLam (Fun Num Num) 
               (DLam Num 
               (DDspℕ (Var hd) 
                     (DC 0) 
                     (DDspℕ (Var hd) 
                           (DC 1) 
                           (DApp (DApp AddD (DApp (Var (tl (tl (tl hd)))) (Var (tl hd)))) (DApp (Var (tl (tl (tl hd)))) (Var hd)))))))

FIBS : AExp [] (SFun SNum SNum)
FIBS = SFix (SLam (SFun SNum SNum) 
               (SLam SNum 
               (SDspℕ (Var hd) 
                     (SC 0) 
                     (SDspℕ (Var hd) 
                           (SC 1) 
                           (SApp (SApp AddS (SApp (Var (tl (tl (tl hd)))) (Var (tl hd)))) (SApp (Var (tl (tl (tl hd)))) (Var hd)))))))



--type interpreters and environment
ATInt : Ctx -> AType -> Set
ATInt Γ SNum = ℕ
ATInt Γ (SFun α₁ α₂) = ∀ {Γ'} → Γ ↝ Γ' → ATInt Γ' α₁ ⊎ nothing → ATInt Γ' α₂ ⊎ nothing
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
elevate Γ↝Γ'↝Γ'' (Fix e) = Fix (elevate Γ↝Γ'↝Γ'' e) 

exp↑ : ∀ {σ Γ Γ'} → Γ ↝ Γ' → Exp Γ σ → Exp Γ' σ
exp↑ Γ↝Γ' e = elevate (refl Γ↝Γ') e

atint↑ : ∀ {α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
atint↑ {D x} Γ↝Γ' atint = exp↑ Γ↝Γ' atint
atint↑ {SFun α α₁} {Γ} {Γ'} Γ↝Γ' atint = λ {Γ''} Γ'↝Γ'' → atint {Γ''} (Γ↝Γ' ⊕ Γ'↝Γ'')
atint↑ {SNum} Γ↝Γ' atint = atint

atint⊎nothing↑ : ∀ {α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α ⊎ nothing → ATInt Γ' α ⊎ nothing
atint⊎nothing↑ {α} {Γ} {Γ'} Γ↝Γ' (inj₁ x) = inj₁ (atint↑ {α} {Γ} {Γ'} Γ↝Γ' x)
atint⊎nothing↑ Γ↝Γ' (inj₂ y) = inj₂ y 
 
data AEnv (Γ : Ctx) : ACtx → Set where
  []  : AEnv Γ []
  _∷_ : ∀ {α Δ} → ATInt Γ α ⊎ nothing → AEnv Γ Δ → AEnv Γ (α ∷ Δ)

aenv↑ : ∀ {Γ Γ' Δ} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
aenv↑ Γ↝Γ' [] = []
aenv↑ Γ↝Γ' (x ∷ aenv) = (atint⊎nothing↑ Γ↝Γ' x) ∷ (aenv↑ Γ↝Γ' aenv)

addfresh : ∀ {σ Γ Δ} → AEnv Γ Δ → AEnv (σ ∷ Γ) (D σ ∷ Δ)
addfresh aenv = inj₁ (Var hd) ∷ aenv↑ (extend refl) aenv

Lookup : ∀ {α Γ Δ} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α ⊎ nothing
Lookup hd (x ∷ aenv) = x
Lookup (tl id) (x ∷ aenv) = Lookup id aenv



--partial evaluator of the two-level language
pe : ∀ {α Γ Δ} → ℕ → AExp Δ α → AEnv Γ Δ → ATInt Γ α ⊎ nothing 
pe n (Var x) aenv = Lookup x aenv
pe n (SC x) aenv = inj₁ x
pe n (DC x) aenv = inj₁ (C x)
pe n (SDspℕ e e₁ e₂) aenv with pe n e aenv
... | inj₁ 0       = pe n e₁ aenv
... | inj₁ (suc m) = pe n e₂ (inj₁ m ∷ aenv) 
... | inj₂ _       = inj₂ N
pe n (DDspℕ e e₁ e₂) aenv with pe n e aenv | pe n e₁ aenv | pe n e₂ (addfresh aenv) 
... | inj₁ a | inj₁ a₁ | inj₁ a₂ = inj₁ (Dspℕ a a₁ a₂)
... | _ | _ | _                  = inj₂ N
pe n (SSuc e) aenv with pe n e aenv 
... | inj₁ m = inj₁ (suc m)
... | inj₂ _ = inj₂ N
pe n (DSuc e) aenv with pe n e aenv 
... | inj₁ a     = inj₁ (Suc a)
... | inj₂ _     = inj₂ N
pe n (SLam α₁ e) aenv = inj₁ (λ Γ↝Γ' → λ y → pe n e (y ∷ (aenv↑ Γ↝Γ' aenv)))
pe n (DLam σ₁ e) aenv with pe n e (addfresh aenv) 
... | inj₁ a = inj₁ (Lam σ₁ a)
... | inj₂ _ = inj₂ N
pe {Γ = Γ } n (SApp e e₁) aenv with pe n e aenv  
... | inj₁ f = f refl (pe n e₁ aenv)
... | inj₂ _ = inj₂ N 
pe n (DApp e e₁) aenv with pe n e aenv | pe n e₁ aenv 
... | inj₁ a | inj₁ a' = inj₁ (App a a')
... | _ | _            = inj₂ N
pe zero (SFix e) aenv = inj₂ N
pe {Γ = Γ} (suc n) (SFix e) aenv with pe n e aenv 
... | inj₁ f = f {Γ} refl (pe n (SFix e) aenv)
... | inj₂ _ = inj₂ N
pe n (DFix e) aenv with pe n e aenv 
... | inj₁ df = inj₁ (Fix df)
... | inj₂ _  = inj₂ N 

--some evaluation examples
EX1 : pe 3000 (DApp (DApp ADDD (DC 1)) (DC 6)) [] ≡ inj₁ (App (App add (C 1)) (C 6))
EX1 = refl

EX2 : pe {SNum} {[]} {[]}3000 (SApp (SApp ADDS (SC 1)) (SC 6)) [] ≡ inj₁ 7
EX2 = refl

EX3 : pe 3000 (DApp (DApp ADDD' (DC 1)) (DC 6)) [] ≡ inj₁ (App (App add' (C 1)) (C 6))
EX3 = refl

EX4 : pe {SNum} {[]} {[]}3000 (SApp (SApp ADDS' (SC 1)) (SC 6)) [] ≡ inj₁ 7
EX4 = refl

EX5 : pe 3000 (DApp (DApp MULD (DC 5)) (DC 6)) [] ≡ inj₁ (App (App mul (C 5)) (C 6))
EX5 = refl

EX6 : pe {SNum} {[]} {[]} 3000 (SApp (SApp MULS (SC 5)) (SC 6)) [] ≡ inj₁ 30
EX6 = refl

EX7 : pe 3000 (DApp FACTD (DC 6)) [] ≡ inj₁ (App fact (C 6))
EX7 = refl

EX8 : pe {SNum} {[]} {[]} 3000 (SApp FACTS (SC 6)) [] ≡ inj₁ 720
EX8 = refl

EX9 : pe 3000 (DApp FIBD (DC 9)) [] ≡ inj₁ (App fib (C 9))
EX9 = refl

EX10 : pe {SNum} {[]} {[]} 3000 (SApp FIBS (SC 9)) [] ≡ inj₁ 34
EX10 = refl