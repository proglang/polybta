-- Partial evaluation of the simply typed lambda calculus with a fixpoint combinator.
-- version by Lu



module PE-STLCFix  where

open import Data.Nat
open import Lib
open Auxiliaries
open import Relation.Binary 
open DecTotalOrder decTotalOrder public using () renaming (refl to ≤-refl) 

data Type : Set where
  Num : Type
  Fun : Type -> Type -> Type
  
Cx : Set
Cx = List Type

data Exp (G : Cx) : Type -> Set where
  Var : forall {t} -> t ∈ G -> Exp G t
  C : ℕ -> Exp G Num
  NatCase : forall {t} -> Exp G Num -- condition
                       -> Exp G t -- zero case
                       -> Exp (Num ∷ G) t -- succ case
                       -> Exp G t
  Suc : Exp G Num -> Exp G Num
  Lam : forall {t2} t1 -> Exp (t1 ∷ G) t2 -> Exp G (Fun t1 t2)
  App : forall {t1 t2} -> Exp G (Fun t1 t2) -> Exp G t1 -> Exp G t2
  Fix : forall {t} -> Exp (t ∷ G) t -> Exp G t





----------------------------------------------------------------------------------------------------------------



data exp (Γ : Cx) : Type → Set where
    var : ∀ {t : Type} → t ∈ Γ → exp Γ t
    cst : ℕ → exp Γ Num
    suc : exp Γ Num → exp Γ Num
    prd : exp Γ Num → exp Γ Num
    mul : exp Γ Num → exp Γ Num → exp Γ Num
    ∔   : exp Γ Num → exp Γ Num → exp Γ Num
    if_then_else_  : ∀ {t : Type} → exp Γ Num → exp Γ t → exp Γ t → exp Γ t
    lam : ∀ {t₁ t₂ : Type} → exp (t₁ ∷ Γ) t₂ → exp Γ (Fun t₁ t₂)
    app : ∀ {t₁ t₂ : Type} → exp Γ (Fun t₁ t₂) → exp Γ t₁ → exp Γ t₂
    fix : ∀ {t : Type} → exp Γ (Fun (Fun t t) (Fun t t)) → exp Γ (Fun t t) 

  --some examples

--a. factorial 
exp-01 : exp [] (Fun (Fun Num Num) (Fun Num Num)) 
exp-01 = lam {t₁ = Fun Num Num} {t₂ = Fun Num Num} (lam {t₁ = Num} {t₂ = Num} 
               (if (var hd) then (cst 1) else (mul (var hd) (app (var (tl hd)) (prd (var hd))))))

exp-02 : exp [] (Fun Num Num)
exp-02 = fix exp-01

exp-03 : exp [] (Fun Num Num)
exp-03 = app exp-01 exp-02

--b. summation
exp-04 : exp [] (Fun (Fun Num Num) (Fun Num Num))
exp-04 = lam {t₁ = Fun Num Num} {t₂ = Fun Num Num}  
         (lam {t₁ = Num} {t₂ = Num} 
         (if (var hd) then (cst 0) else ∔ (var hd) (app (var (tl hd)) (prd (var hd)))))

exp-05 : exp [] (Fun Num Num)
exp-05 = fix exp-04

exp-06 : exp [] (Fun Num Num)
exp-06 = app exp-04 exp-05

--c. Fibonacci numbers
exp-07 : exp [] (Fun (Fun Num Num) (Fun Num Num))
exp-07 = lam {t₁ = Fun Num Num} {t₂ = Fun Num Num}  
         (lam {t₁ = Num} {t₂ = Num} 
         (if (prd (var hd)) then (var hd) else ∔ (app (var (tl hd)) (prd (prd (var hd)))) (app (var (tl hd)) (prd (var hd)))))

exp-08 : exp [] (Fun Num Num)
exp-08 = fix exp-07

exp-09 : exp [] (Fun Num Num)
exp-09 = app exp-07 exp-08

  --evaluations
  
  --type interpreter
int : Type → Set
int Num = ℕ
int (Fun ty ty₁) = int ty → int ty₁

  --environment
data env : Cx → Set where
    []  : env [] 
    _∷_ : ∀ {t : Type} {Γ : Cx} → int t → env Γ → env (t ∷ Γ)

  --look-up
lookUp : ∀ {t : Type} {Γ : Cx} → t ∈ Γ → env Γ → int t
lookUp () []
lookUp hd (x ∷ env) = x
lookUp (tl id) (x ∷ env) = lookUp id env

  --evaluator
eval : ∀ {t : Type} {Γ : Cx} → env Γ → exp Γ t → int t
eval env (var x) = lookUp x env
eval env (cst x) = x
eval env (suc e) = suc (eval env e)
eval env (prd e) with eval env e 
... | suc n = n
... | 0     = 0
eval env (if e then e₁ else e₂) with eval env e 
... | suc n = eval env e₂
... | 0     = eval env e₁
eval env (lam e) = λ x → eval (x ∷ env) e
eval env (app e e₁) = eval env e (eval env e₁)
eval env (fix e) = eval env e (eval env (fix e))
eval env (mul e e₁) = (eval env e) * (eval env e₁) 
eval env (∔ e e₁) = (eval env e) + (eval env e₁)
  --note: since there is no guarantee that 
  --      the recursive call eventually terminates
  --      , [eval] can not pass Agda's termination 
  --      check.
   

eval1 : ∀ {t : Type} {Γ : Cx} → ℕ → env Γ → exp Γ t → int t
eval1 fuel env (var x) = lookUp x env
eval1 fuel env (cst x) = x
eval1 fuel env (suc e) = suc (eval1 fuel env e)
eval1 fuel env (prd e) with eval1 fuel env e 
... | 0     = 0
... | suc n = n
eval1 fuel env (if e then e₁ else e₂) with eval1 fuel env e 
... | 0 = eval1 fuel env e₁
... | suc n = eval1 fuel env e₂
eval1 fuel env (lam e) = λ x → eval1 fuel (x ∷ env) e
eval1 fuel env (app e e₁) = eval1 fuel env e (eval1 fuel env e₁) 
eval1 zero env (fix e) = eval1 zero env e (λ x → x)
eval1 (suc fuel) env (fix e) = eval1 fuel env e (eval1 fuel env (fix e))
eval1 fuel env (mul e e₁) = (eval1 fuel env e) * (eval1 fuel env e₁) 
eval1 fuel env (∔ e e₁) = (eval1 fuel env e) + (eval1 fuel env e₁)

eval-factorial0 : ℕ → ℕ
eval-factorial0 = eval1 0 [] exp-02

0! : ℕ
0! = eval-factorial0 0

eval-factorial1 : ℕ → ℕ
eval-factorial1 = eval1 1 [] exp-02
  
1! : ℕ
1! = eval-factorial1 1

eval-factorial6 : ℕ → ℕ
eval-factorial6 = eval1 6 [] exp-02

6! : ℕ
6! = eval-factorial6 6

eval-summation0 : ℕ → ℕ
eval-summation0 = eval1 0 [] exp-05

Σ0 : ℕ
Σ0 = eval-summation0 0

eval-summation1 : ℕ → ℕ
eval-summation1 = eval1 1 [] exp-05

Σ1 : ℕ
Σ1 = eval-summation1 1

eval-summation10 : ℕ → ℕ
eval-summation10 = eval1 10 [] exp-05

Σ10 : ℕ
Σ10 = eval-summation10 10

eval-fibonacci0 : ℕ → ℕ
eval-fibonacci0 = eval1 0 [] exp-08

fibo0 : ℕ
fibo0 = eval-fibonacci0 0

eval-fibonacci1 : ℕ → ℕ
eval-fibonacci1 = eval1 1 [] exp-08

fibo1 : ℕ
fibo1 = eval-fibonacci1 1

eval-fibonacci10 : ℕ → ℕ
eval-fibonacci10 = eval1 10 [] exp-08

fubo10 = eval-fibonacci10 10

----------------------------------------------------------------------------------------


data eXp (Γ : Cx) : Type → Set where
    var : ∀ {t : Type} → t ∈ Γ → eXp Γ t
    cst : ℕ → eXp Γ Num
    lam : ∀ {t₁ t₂ : Type} → eXp (t₁ ∷ Γ) t₂ → eXp Γ (Fun t₁ t₂)
    app : ∀ {t₁ t₂ : Type} → eXp Γ (Fun t₁ t₂) → eXp Γ t₁ → eXp Γ t₂
    fix : ∀ {t₁ t₂ : Type} → eXp Γ (Fun (Fun t₁ t₂) (Fun t₁ t₂)) → eXp Γ (Fun t₁ t₂)
    succ : eXp Γ Num → eXp Γ Num
    prd : eXp Γ Num → eXp Γ Num
    mul : eXp Γ Num → eXp Γ Num → eXp Γ Num
    add : eXp Γ Num → eXp Γ Num → eXp Γ Num
    if_then_else_ : ∀ {t : Type} → eXp Γ Num → eXp Γ t → eXp Γ t → eXp Γ t
    

eval2 : ∀ {t : Type} {Γ : Cx} → ℕ → eXp Γ t → env Γ → int t
eval2 c (var x) env = lookUp x env
eval2 c (cst x) env = x
eval2 c (lam e) env = λ x → eval2 c e (x ∷ env)
eval2 c (app e e₁) env = eval2 c e env (eval2 c e₁ env)
eval2 zero (fix {Num} e) env = λ n → eval2 zero e env (eval2 zero (fix e) env) 0
eval2 (suc c) (fix {Num} e) env = eval2 (suc c) e env (eval2 c (fix e) env)
eval2 c (fix {Fun t₁ t₂} e) env = {!!} -- not clear about this case?
eval2 c (succ e) env = suc (eval2 c e env)
eval2 c (prd e) env with eval2 c e env 
... | 0 = 0
... | suc n = n
eval2 c (mul e₁ e₂) env = (eval2 c e₁ env) * (eval2 c e₂ env)
eval2 c (add e₁ e₂) env = (eval2 c e₁ env) + (eval2 c e₂ env)
eval2 c (if n then e₁ else e₂) env with eval2 c n env 
... | 0 = eval2 c e₁ env
... | suc n' = eval2 c e₂ env

--some examples
--a. factorial 
eXp-01 : eXp [] (Fun (Fun Num Num) (Fun Num Num)) 
eXp-01 = lam {t₁ = Fun Num Num} {t₂ = Fun Num Num} (lam {t₁ = Num} {t₂ = Num} 
               (if (var hd) then (cst 1) else (mul (var hd) (app (var (tl hd)) (prd (var hd))))))

eXp-02 : eXp [] (Fun Num Num)
eXp-02 = fix eXp-01

eXp-10! : eXp [] Num
eXp-10! = app eXp-02 (cst 10)

eval2-factorial-1 : ℕ
eval2-factorial-1 = (eval2 3 eXp-02 []) 3   



-----------------------------------------------------------------------------------------------
--note: no-termination problems have to be dealt with when having
--      recursive functions. There main difficulties related to
--      designing the evaluation [ev] are,
--a)in order to guarantee termination, some artificial counter has to be
--  introduced to set the limit of recursive calls independent from the
--  underlying recursive function itself;
--b)"termination value", the value we assign to a recursive function when
--  the number of recursive calls reaches its limit,[nothing],has to be
--  propagated in a way that it will not distroy the intended evaluation
--  process. 

data Nothing : Set where
  nothing : Nothing

Int : Type → Set
Int Num = ℕ
Int (Fun ty ty₁) = Int ty ⊎ Nothing → Int ty₁ ⊎ Nothing


data ENv : Cx → Set where
    []  : ENv [] 
    _∷_ : ∀ {t : Type} {Γ : Cx} → Int t ⊎ Nothing → ENv Γ → ENv (t ∷ Γ)



--Look-up
LookUp : ∀ {t : Type} {Γ : Cx} → t ∈ Γ → ENv Γ → Int t ⊎ Nothing
LookUp () []
LookUp hd (x ∷ env) = x
LookUp (tl id) (x ∷ env) = LookUp id env

eval3 : ∀ {t : Type} {Γ : Cx} → ℕ → eXp Γ t → ENv Γ → (Int t) ⊎ Nothing
eval3 n (var x) env = LookUp x env
eval3 n (cst x) env = inj₁ x
eval3 n (lam e) env = inj₁ (λ x → eval3 n e (x ∷ env))
eval3 n (app e e₁) env with eval3 n e env | eval3 n e₁ env 
... | inj₁ e' | inj₁ e₁' = e' (inj₁ e₁')
... | inj₁ e' | inj₂ e₁' = e' (inj₂ e₁')
... | inj₂ e' | inj₁ e₁' = inj₂ nothing
... | inj₂ e' | inj₂ e₁' = inj₂ nothing 
eval3 zero (fix e) env = inj₂ nothing
eval3 (suc n) (fix e) env with eval3 (suc n) e env | eval3 n (fix e) env 
... | inj₁ e' | inj₁ e₁' = e' (inj₁ e₁') -- 
... | inj₁ e' | inj₂ e₁' = e' (inj₂ e₁')
... | inj₂ e' | inj₁ e₁' = inj₂ nothing
... | inj₂ e' | inj₂ e₁' = inj₂ nothing
eval3 n (succ e) env with eval3 n e env
... | inj₁ n' = inj₁ (suc n')
... | inj₂ _  = inj₂ nothing
eval3 n (prd e) env with eval3 n e env 
eval3 n (prd e) env | inj₁ zero = inj₁ 0
eval3 n (prd e) env | inj₁ (suc n') = inj₁ n'
... | inj₂ _ = inj₂ nothing
eval3 n (mul e e₁) env with eval3 n e env | eval3 n e₁ env
... | inj₁ e' | inj₁ e₁' = inj₁ (e' * e₁')
... | inj₁ e' | inj₂ e₁' = inj₁ e'
... | inj₂ e' | inj₁ e₁' = inj₁ e₁'
... | inj₂ e' | inj₂ e₁' = inj₂ nothing 
eval3 n (add e e₁) env with eval3 n e env | eval3 n e₁ env 
... | inj₁ e' | inj₁ e₁' = inj₁ (e' + e₁')
... | inj₁ e' | inj₂ e₁' = inj₁ e'
... | inj₂ e' | inj₁ e₁' = inj₁ e₁'
... | inj₂ e' | inj₂ e₁' = inj₂ nothing
eval3 n (if e then e₁ else e₂) env with eval3 n e env 
eval3 n (if e then e₁ else e₂) env | inj₁ zero = eval3 n e₁ env
eval3 n (if e then e₁ else e₂) env | inj₁ (suc e') = eval3 n e₂ env
... | inj₂ _ = inj₂ nothing

--some examples
--factorials
eval3-factorial-10 : ℕ ⊎ Nothing
eval3-factorial-10 = eval3 10 eXp-10! [] 


--yet another try at the evaluator
eval4 : ∀ {t : Type} {Γ : Cx} → eXp Γ t → env Γ → int t
eval4 (var x) env = {!!}
eval4 (cst x) env = {!!}
eval4 (lam e) env = λ x → eval4 e (x ∷ env)
eval4 (app e e₁) env = eval4 e env (eval4 e₁ env)
eval4 (fix e) env = {!!}
eval4 (succ e) env = {!!}
eval4 (prd e) env = {!!}
eval4 (mul e e₁) env = {!!}
eval4 (add e e₁) env = {!!}
eval4 (if e then e₁ else e₂) env = {!!}

  
module Example-Terms where

  loop : forall {G t} -> Exp G t
  loop = Fix (Var (hd)) 
  
  loop-fun' : forall {G} -> Exp G (Fun Num Num)
  loop-fun' {G} = loop {G = G} {t = Fun Num Num}

  loop-fun : forall {G} -> Exp G (Fun Num Num) 
  loop-fun = Fix (Lam _ (App (Var (tl hd)) (Var hd)))
  
  nofix : forall {G} -> Exp G Num
  nofix = App (Fix (Lam _ (C 42))) (C 5)
  
  
  iter : forall {G t} -> Exp G (Fun (Fun t t) (Fun t (Fun Num t)))
  iter = Lam _ (Lam _ ((Fix (Lam _ (NatCase (Var hd) --a
                                            (Var (tl (tl hd))) --b
                                            (App (Var (tl (tl (tl (tl hd))))) --c
                                                 (App (Var (tl (tl hd))) (Var hd)) )))))) --d, e
  --note:  a) Var hd : Num, b) Var (tl (tl hd)) : t, c) Var (tl (tl (tl (tl hd)))) : Fun t t
  --       d) Var (tl (tl hd)) : Fun Num t
  --       e) Var hd : Num 
  
  inc : forall {G} -> Exp G (Fun Num Num)
  inc = (App (App iter (Lam _ (Suc (Var hd)))) (C 1))

  inc' : forall {G} -> Exp G (Fun Num Num)
  inc' = (Fix (Lam _ (NatCase (Var hd) (C 1) (Suc (App (Var (tl (tl hd))) (Var hd))))))
  
  -- add : forall {G} -> Exp G (Fun Num (Fun Num Num))
  -- add = (Lam _ (App (App iter (Lam _ (App inc (Var hd)))) (Var hd)))
  
--module Evaluation where
  
open import Data.Maybe 
open import Category.Functor
open import Category.Monad
import Level
open RawMonad {Level.zero} Data.Maybe.monad

-- Environments, parameterized over the type interpretation
--module Env (⟦_⟧ : Type -> Set) where

⟦_⟧ : Type -> Set
⟦ Num ⟧ = ℕ
⟦ Fun t1 t2 ⟧ = ⟦ t1 ⟧ -> Maybe ⟦ t2 ⟧ 


  
data Env : Cx -> Set where
     []   : Env []
     _∷_ : ∀ {t G} -> Maybe ⟦ t ⟧ -> Env G -> Env (t ∷ G)
    
lookup : forall {t G} -> t ∈ G -> Env G -> Maybe ⟦ t ⟧
lookup hd (v ∷ env) = v
lookup (tl x) (_ ∷ env) = lookup x env 


--module Step where

-- ⟦_⟧ : Type -> Set
-- ⟦ Num ⟧ = ℕ
-- ⟦ Fun t1 t2 ⟧ = ⟦ t1 ⟧ -> Maybe ⟦ t2 ⟧ 
  
-- open Env (λ t -> Maybe ⟦ t ⟧) public

ev : forall {G t} -> (fuel : ℕ) -> Env G -> Exp G t -> Maybe ⟦ t ⟧
ev fuel env (C x) = just x
ev fuel env (NatCase e e₁ e₂) with ev fuel env e
... | just zero = ev fuel env e₁
... | just (suc n) = ev fuel (just n ∷ env) e₂
... | nothing = nothing
ev fuel env (Suc e) = suc <$> ev fuel env e 
ev fuel env (Var x) = lookup x env
ev fuel    env (Lam t1 e) = just (λ x → ev fuel (just x ∷ env) e) 
ev fuel env (App e e₁) = join (ev fuel env e ⊛ ev fuel env e₁)
ev (suc fuel) env (Fix f) = ev (suc fuel) (f' ∷ env) f
    where f' = ev fuel env (Fix f)
ev zero _         (Fix f) = nothing

--specification using partiality monad


------------------------------------
--construct some reasonable examples
--test instance

test-Exp : Exp [] (Fun Num Num)
test-Exp = Fix {t = Fun Num Num} (Lam Num (App (Var (tl hd)) (Suc (Var hd))) )

test-ev-wrong : ev 4 [] (App test-Exp (C 4)) ≡ nothing
test-ev-wrong  = refl
--note: the above example ""test-ev-wrong" shows that [ev] is semantically wrong
--      in the sense that "non-termination" term "nothing" is propogated incorrectly
--      in the evaluation process...



  module EvalExamples where
    open Example-Terms
    
    ex1 : ev 3000 [] (App loop-fun (C 42)) ≡ nothing
    ex1 = refl

    ex2' : ev 3000 [] (NatCase (C 0) (C 5) (Var hd)) ≡ just 5
    ex2' = refl

    ex2'' : ev 3000 [] (NatCase (C 42) (C 5) (Var hd)) ≡ just 41
    ex2'' = refl
  
    ex2 : ev 3000 [] (App inc (C 3)) ≡ just 4
    ex2 = refl -- refl
    
    ex3 : ev 3000 [] nofix ≡ just 42
    ex3 = refl

module TwoLevel where


  data AType : Set where
    D : Type -> AType
    SFun : AType -> AType -> AType
    SNum : AType
    
  ACx : Set
  ACx = List AType
  
  data AExp (G : ACx) : AType -> Set where
    Var : forall {t} -> t ∈ G -> AExp G t
    SC : ℕ -> AExp G SNum
    DC : ℕ -> AExp G (D Num)
    SNatCase : forall {t} -> AExp G SNum -- condition
                          -> AExp G t -- zero case
                          -> AExp (SNum ∷ G) t -- succ case
                          -> AExp G t
    DNatCase : forall {t} -> AExp G (D Num) -- condition
                          -> AExp G (D t) -- zero case
                          -> AExp (D Num ∷ G) (D t) -- succ case
                          -> AExp G (D t)
    SSuc : AExp G SNum -> AExp G SNum
    DSuc : AExp G (D Num) -> AExp G (D Num)
    SLam : forall {t2} t1 -> AExp (t1 ∷ G) t2 -> AExp G (SFun t1 t2)
    DLam : forall {t2} t1 -> AExp (D t1 ∷ G) (D t2) -> AExp G (D (Fun t1 t2))
    SApp : forall {t1 t2} -> AExp G (SFun t1 t2) -> AExp G t1 -> AExp G t2
    DApp : forall {t1 t2} -> AExp G (D (Fun t1 t2)) -> AExp G (D t1) -> AExp G (D t2)
    DFix : forall {t} -> AExp (D t ∷ G) (D t ) -> AExp G (D t)
    
  ATInt : Cx -> AType -> Set
  ATInt G SNum = ℕ
  ATInt G (SFun t1 t2) =
    forall {G'} -> G ↝ G' -> ATInt G' t1 -> (ATInt G' t2)
  ATInt G (D t) = Exp G t
 
  data AEnv (G : Cx) : ACx -> Set where
    [] : AEnv G []
    _∷_ : forall {t E} -> ATInt G t -> AEnv G E -> AEnv G (t ∷ E)
    

  elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
  elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
  -- impementation at the end of the file
  
  -- TODO: ↑ is an unfortunate choice for shifting, as it is used for
  -- reflect in the TDPE literature.
  exp↑ : ∀ {τ τ' Γ} → Exp Γ τ' → Exp (τ ∷ Γ) τ'
  exp↑ e = elevate (refl (extend refl)) e
  
  int↑ : ∀ { α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
  int↑ refl v = v
  int↑ {D τ} (extend Γ↝Γ') e = {!exp↑ (int↑ Γ↝Γ' e)!}
  int↑ {SNum} _ v = v
  int↑ {SFun α α₁} Γ↝Γ' f =
    λ Γ'↝Γ'' x → f (Γ↝Γ' ⊕ Γ'↝Γ'') x
  
  env↑ : ∀ { Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
  env↑ _ [] = []
  env↑ Γ↝Γ' (x ∷ ρ) = int↑ Γ↝Γ' x ∷ env↑ Γ↝Γ' ρ
  
  addFresh : ∀ {τ Γ Δ} → AEnv Γ Δ → AEnv (τ ∷ Γ) (D τ ∷ Δ)
  addFresh ρ = Var hd ∷ env↑ (extend refl) ρ
    
  LookUP : forall {t E G} -> t ∈ E -> AEnv G E -> ATInt G t
  LookUP hd (v ∷ env) = v
  LookUP (tl x) (_ ∷ env) = LookUP x env 
  
  
  pe : ∀ { Γ Δ α } → 
           AEnv Γ Δ → AExp Δ α → ATInt Γ α
  pe env (Var x) = LookUP x env
  pe env (SC x) = x
  pe env (DC x) = C x
  pe env (SNatCase e e₁ e₂) with pe env e 
  ... | zero = pe env e₁
  ... | suc n = pe (n ∷ env) e₂ 
  pe env (DNatCase e e₁ e₂) = NatCase (pe env e) (pe env e₁) (pe (addFresh env) e₂)
  pe env (SSuc e) = pe env e
  pe env (DSuc e) = Suc (pe env e)
  pe env (SLam t1 e) = λ G↝G' x → pe (x ∷ env↑ G↝G' env) e
  pe env (DLam t1 e) = Lam t1 (pe (addFresh env) e)
  pe env (SApp e e₁) = pe env  e refl (pe env e₁)
  pe env (DApp e e₁) = App (pe env e) (pe env e₁)
  pe env (DFix e) = Fix (pe (addFresh env) e)
  

  
-- -------------------------------------------------------------------
-- Implementation of elevate-* functions
-- -------------------------------------------------------------------
  elevate-var refl x = x
  elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)
  
  elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
  elevate-var2 (refl x) x₁ = elevate-var x x₁
  elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
  elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)
  
  elevate Γ↝Γ'↝Γ'' (Var x) = Var (elevate-var2 Γ↝Γ'↝Γ'' x)
  elevate Γ↝Γ'↝Γ'' (C x) = C x
  elevate Γ↝Γ'↝Γ'' (NatCase e e₁ e₂) = NatCase (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁) (elevate (extend Γ↝Γ'↝Γ'') e₂)
  elevate Γ↝Γ'↝Γ'' (Suc e) = elevate Γ↝Γ'↝Γ'' e
  elevate Γ↝Γ'↝Γ'' (Lam t1 e) = Lam t1 (elevate (extend Γ↝Γ'↝Γ'') e)
  elevate Γ↝Γ'↝Γ'' (App e e₁) = App (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
  elevate Γ↝Γ'↝Γ'' (Fix e) = Fix (elevate (extend Γ↝Γ'↝Γ'') e)

