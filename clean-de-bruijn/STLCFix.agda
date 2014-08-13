-- Simply typed lambda calculus with a fixpoint combnator.
module STLCFix where

open import Lib

data Type : Set where
  Num : Type
  Fun : Type -> Type -> Type
  
Cx : Set
Cx = List Type

data Exp (G : Cx) : Type -> Set where
  C : ℕ -> Exp G Num
  NatCase : forall {t} -> Exp G Num -- condition
                       -> Exp G t -- zero case
                       -> Exp (Num ∷ G) t -- succ case
                       -> Exp G t
  Suc : Exp G Num -> Exp G Num
  Var : forall {t} -> t ∈ G -> Exp G t
  Lam : forall {t2} t1 -> Exp (t1 ∷ G) t2 -> Exp G (Fun t1 t2)
  App : forall {t1 t2} -> Exp G (Fun t1 t2) -> Exp G t1 -> Exp G t2
  Fix : forall {t} -> Exp (t ∷ G) t -> Exp G t
  
module Examples where
  loop : forall {G} -> Exp G (Fun Num Num) 
  loop = Fix (Lam _ (App (Var (tl hd)) (Var hd)))
  
  nofix : forall {G} -> Exp G Num
  nofix = App (Fix (Lam _ (C 42))) (C 5)
  
  
  iter : forall {G t} -> Exp G (Fun (Fun t t) (Fun t (Fun Num t)))
  iter = Lam _ (Lam _ ((Fix (Lam _ (NatCase (Var hd) (Var (tl (tl hd))) (App (Var (tl (tl hd))) (Var hd)))))))
  

  inc : forall {G} -> Exp G (Fun Num Num)
  inc = (App (App iter (Lam _ (Suc (Var hd)))) (C 1))
  
  
module Evaluation where
  
open import Data.Maybe hiding (map)
open import Category.Functor
open import Category.Monad
import Level
open RawMonad {Level.zero} Data.Maybe.monad

-- Environments, parameterized over the type interpretation
module Env (⟦_⟧ : Type -> Set) where
  data Env : Cx -> Set where
    [] : Env []
    _∷_ : forall {t G} -> ⟦ t ⟧ -> Env G -> Env (t ∷ G)
    
  lookup : forall {t G} -> t ∈ G -> Env G -> ⟦ t ⟧
  lookup hd (v ∷ env) = v
  lookup (tl x) (_ ∷ env) = lookup x env 

-- We could just ignore the fixpoint...
module NoFix where

  ⟦_⟧ : Type -> Set
  ⟦ Num ⟧ = ℕ
  ⟦ Fun t1 t2 ⟧ = ⟦ t1 ⟧ -> Maybe ⟦ t2 ⟧ 
  
  open Env (⟦_⟧)
    
  ev : forall {G t} -> Env G -> Exp G t -> Maybe ⟦ t ⟧
  ev env (C x) = just x
  ev env (NatCase e e₁ e₂) with ev env e
  ... | just zero = ev env e₁
  ... | just (suc n) = ev (n ∷ env) e₂
  ... | nothing = nothing
  ev env (Suc e) = suc <$> ev env e
  ev env (Var x) = just (lookup x env)
  ev env (Lam t1 e) = just (λ x → ev (x ∷ env) e)
  ev env (App e e₁) = join (ev env e ⊛ ev env e₁)
  ev env (Fix e) = nothing
  
  module EvalExamples where
    open Examples
    
    ex1 : ev [] loop ≡ nothing
    ex1 = refl
  
    ex2 : ev [] (App inc (C 3)) ≡ nothing
    ex2 = refl
    
    ex3 : ev [] nofix ≡ nothing
    ex3 = refl
    

-- More useful: step-indexing evaluation
module Step where

  ⟦_⟧ : Type -> Set
  ⟦ Num ⟧ = ℕ
  ⟦ Fun t1 t2 ⟧ = ⟦ t1 ⟧ -> Maybe ⟦ t2 ⟧ 
  
  open Env (λ t -> Maybe ⟦ t ⟧) public
    
  ev : forall {G t} -> (fuel : ℕ) -> Env G -> Exp G t -> Maybe ⟦ t ⟧
  ev zero env e = nothing
  ev (suc fuel) env (C x) = just x
  ev (suc fuel) env (NatCase e e₁ e₂) with ev fuel env e
  ... | just zero = ev fuel env e₁
  ... | just (suc n) = ev fuel (just n ∷ env) e₂
  ... | nothing = nothing
  ev (suc fuel) env (Suc e) = suc <$> ev fuel env e
  ev (suc fuel) env (Var x) = lookup x env
  ev (suc fuel   ) env (Lam t1 e) = just (λ x → ev fuel (just x ∷ env) e)
  ev (suc fuel) env (App e e₁) = join (ev fuel env e ⊛ ev fuel env e₁)
  ev (suc fuel) env (Fix f) = ev fuel (f' ∷ env) f
    where f' = ev fuel env (Fix f)

  module EvalExamples where
    open Examples
    
    ex1 : ev 3000 [] (App loop (C 42)) ≡ nothing
    ex1 = refl
  
    ex2 : ev 3000 [] (App inc (C 3)) ≡ just (suc zero)
    ex2 = refl
    
    ex3 : ev 3000 [] nofix ≡ just 42
    ex3 = refl

module TwoLevel where

  open import CtxExtension public

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
                          -> AExp G t -- zero case
                          -> AExp (D Num ∷ G) t -- succ case
                          -> AExp G t
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
    
  lookup : forall {t E G} -> t ∈ E -> AEnv G E -> ATInt G t
  lookup hd (v ∷ env) = v
  lookup (tl x) (_ ∷ env) = lookup x env 
  
  
  pe : ∀ { Γ Δ α } → 
           AExp Δ α → AEnv Γ Δ → ATInt Γ α
  pe = {!!}
  
    
module LogicalRelation
       where
        
  open Step
  open TwoLevel

  erase : AType -> Type
  erase (D x) = x
  erase (SFun s1 s2) = Fun (erase s1) (erase s2)
  erase SNum = Num
  

  data _⊢_↝_ :
    ∀ {Γ Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
    refl : ∀ {Γ} {ρ : Env Γ} → refl ⊢ ρ ↝ ρ
    extend : ∀ {τ Γ Γ' ρ ρ'} → {Γ↝Γ' : Γ ↝ Γ'} →
               (v :  ⟦ τ ⟧) → Γ↝Γ' ⊢ ρ ↝ ρ' →
               extend Γ↝Γ' ⊢ ρ ↝ (just v ∷ ρ')

  _⊕ρ_ : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
    {ρ ρ' ρ''} → 
    Γ↝Γ' ⊢ ρ ↝ ρ' → Γ'↝Γ'' ⊢ ρ' ↝ ρ'' →
    let Γ↝Γ'' = Γ↝Γ' ⊕ Γ'↝Γ'' in
    Γ↝Γ'' ⊢ ρ ↝ ρ'' 
  _⊕ρ_ ρ↝ρ' (refl) = ρ↝ρ'
  _⊕ρ_ ρ↝ρ' (extend v ρ'↝ρ'') = extend v (ρ↝ρ' ⊕ρ ρ'↝ρ'')

  Equiv-term : forall {s : AType} {G} -> (env : Env G) -> (w : ATInt G s) -> (mv : Maybe ⟦ erase s ⟧) -> Set
  Equiv-term {D x} env w (just v) = (∃₂ (λ v' n -> (ev n env w ≡ just v') × v ≡ v'))
  Equiv-term {SFun s1 s2} {G} env w (just v) = 
    ∀ {Γ' ρ' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ ρ') →
       {xₐ : ATInt Γ' s1} → {x : ⟦ (erase s1) ⟧} →
       Equiv-term ρ' xₐ (just x) → Equiv-term ρ' (w Γ↝Γ' xₐ) (v x)
  Equiv-term {SNum} env w (just v) = w ≡ v
  Equiv-term env w nothing = ⊤
  

  Equiv-div : forall {s : AType} {G} (min-steps : ℕ) (env : Env G) (w : ATInt G s) (v : Maybe ⟦ erase s ⟧) -> Set
  Equiv-div {D x} min-steps env w (just v) = ⊤
  Equiv-div {SNum} min-steps env w (just v) = ⊤
  Equiv-div {SFun s1 s2} min-steps env w (just v) = 
    ∀ {Γ' ρ' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ ρ') →
       {xₐ : ATInt Γ' s1} → 
       ({x : ⟦ (erase s1) ⟧} → Equiv-term ρ' xₐ (just x) → Equiv-div min-steps ρ' (w Γ↝Γ' xₐ) (v x))

  Equiv-div {D x} min-steps env w nothing = ∃ (λ n' → min-steps ≤ n' × ev n' env w ≡ nothing)
  Equiv-div {SFun s1 s2} min-steps env w nothing = ⊥
  Equiv-div {SNum} min-steps env w nothing = ⊥

  -- data Env-Equiv {Γ' : _} (ρ : Env Γ') :
  --   ∀ {Δ} → (ρ' : AEnv Γ' Δ) → (ρ'' : Env (map erase Δ))
  --   → Set where
  -- -- ...
  --   [] : Env-Equiv ρ [] []
  --   cons : ∀ {α Δ} → let τ = erase α
  --                        Γ = map erase Δ in
  --           {ρ'' : Env Γ} → {ρ' : AEnv Γ' Δ} → 
  --           Env-Equiv ρ ρ' ρ'' →
  --           (va : ATInt Γ' α) → (v : τ) → 
  --           Equiv ρ va v → 
  --               Env-Equiv ρ (va ∷ ρ') (v ∷ ρ'')

