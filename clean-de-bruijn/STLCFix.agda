-- Simply typed lambda calculus with a fixpoint combnator.
module STLCFix where

open import Lib

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
  iter = Lam _ (Lam _ ((Fix (Lam _ (NatCase (Var hd)
                                            (Var (tl (tl hd)))
                                            (App (Var (tl (tl (tl (tl hd)))))
                                                 (App (Var (tl (tl hd))) (Var hd)) ))))))
  
  inc : forall {G} -> Exp G (Fun Num Num)
  inc = (App (App iter (Lam _ (Suc (Var hd)))) (C 1))

  inc' : forall {G} -> Exp G (Fun Num Num)
  inc' = (Fix (Lam _ (NatCase (Var hd) (C 1) (Suc (App (Var (tl (tl hd))) (Var hd))))))
  
  add : forall {G} -> Exp G (Fun Num (Fun Num Num))
  add = (Lam _ (App (App iter (Lam _ (App inc (Var hd)))) (Var hd)))
  
module Evaluation where
  
open import Data.Maybe 
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

module Step where

  ⟦_⟧ : Type -> Set
  ⟦ Num ⟧ = ℕ
  ⟦ Fun t1 t2 ⟧ = ⟦ t1 ⟧ -> Maybe ⟦ t2 ⟧ 
  
  open Env (λ t -> Maybe ⟦ t ⟧) public

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
  elevate-var refl x = x
  elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)
  
  elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
  elevate-var2 (refl x) x₁ = elevate-var x x₁
  elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
  elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)
  
  elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
  elevate Γ↝Γ'↝Γ'' (Var x) = Var (elevate-var2 Γ↝Γ'↝Γ'' x)
  elevate Γ↝Γ'↝Γ'' e = {!!}
  
  -- TODO: ↑ is an unfortunate choice for shifting, as it is used for
  -- reflect in the TDPE literature.
  exp↑ : ∀ {τ τ' Γ} → Exp Γ τ' → Exp (τ ∷ Γ) τ'
  exp↑ e = elevate (refl (extend refl)) e
  
  int↑ : ∀ { α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
  int↑ refl v = v
  int↑ {D τ} (extend Γ↝Γ') e = exp↑ (int↑ Γ↝Γ' e)
  int↑ {SNum} _ v = v
  int↑ {SFun α α₁} Γ↝Γ' f =
    λ Γ'↝Γ'' x → f (Γ↝Γ' ⊕ Γ'↝Γ'') x
  
  env↑ : ∀ { Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
  env↑ _ [] = []
  env↑ Γ↝Γ' (x ∷ ρ) = int↑ Γ↝Γ' x ∷ env↑ Γ↝Γ' ρ
  
  addFresh : ∀ {τ Γ Δ} → AEnv Γ Δ → AEnv (τ ∷ Γ) (D τ ∷ Δ)
  addFresh ρ = Var hd ∷ env↑ (extend refl) ρ
    
  lookup : forall {t E G} -> t ∈ E -> AEnv G E -> ATInt G t
  lookup hd (v ∷ env) = v
  lookup (tl x) (_ ∷ env) = lookup x env 
  
  
  pe : ∀ { Γ Δ α } → 
           AEnv Γ Δ → AExp Δ α → ATInt Γ α
  pe env (Var x) = lookup x env
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
  
module TermEquivalence where
  open Step
  open import Coinduction

  -- Equivalence of base language terms
  data EqTerm {G : Cx} {t : Type} ( env : Env G ) (n : ℕ) : Exp G t -> Exp G t -> Set where
    eq : forall {n' e1 e2}  -> n ≤ n' -> ev n' env  e1 ≡ ev n' env e2 ->
         ∞ (EqTerm env (suc n) e1 e2) -> EqTerm env n e1 e2
         
  -- syntax EqTerm [] n e1 e2 = [ e1 ≡∞ e2 ] n
         
--   -- _≡∞_ : forall {G t} -> Exp G t -> Exp G t -> Set
--   -- _≡∞_ {G} {t} = EqTerm {G} {t} 0
         
  module Examples where
  
    open Example-Terms using (add ; inc ; loop ; loop-fun; loop-fun')
    open import Data.Nat.Properties
    
    postulate ext : ∀ {τ₁ τ₂} {f g : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ } →
                    (∀ x → f x ≡ g x) → f ≡ g

                    
    -- helper to assert closed contexts
    -- close : forall {t} -> Exp [] t -> Exp [] t
    -- close x = x

    ex1 : forall {n} -> EqTerm [] n (C 5) (Suc (C 4)) 
    ex1 = eq ≤-refl refl (♯ ex1) 

    ex2 : forall {n} -> EqTerm [] n (C 2) (App inc (C 1))
    ex2 = eq (≤-steps 3 ≤-refl) refl (♯ ex2) 
    
    ex3 : forall {n} ->  EqTerm [] n (C 5) (App (App add (C 3)) (C 2)) 
    ex3 = eq (≤-steps 20 ≤-refl) refl (♯ ex3)
    
    ex-loop : forall {n} -> EqTerm [] n   (App loop-fun' (C 0)) (App loop-fun (C 1))
    ex-loop {zero} = eq ≤-refl refl (♯ ex-loop)
    ex-loop {suc n} with ex-loop {n}  -- it is not even possible to do pattern matching/projection of a structurally recursive call
    ex-loop {suc n} | eq le p-equal _ = eq (s≤s le) p-equal  (♯ ex-loop) 
    
--     -- This of course works...
--     loop-nothing : forall {t} n -> ev {t = t} n [] (App loop (C 0)) ≡ nothing
--     loop-nothing zero = refl
--     loop-nothing {t} (suc n) rewrite loop-nothing {t} n = refl
    
-- -- module Correctness
-- --        where
        
-- --   open Step
-- --   open TwoLevel

-- --   erase : AType -> Type
-- --   erase (D x) = x
-- --   erase (SFun s1 s2) = Fun (erase s1) (erase s2)
-- --   erase SNum = Num
  
  


-- --   data _⊢_↝_ :
-- --     ∀ {Γ Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
-- --     refl : ∀ {Γ} {ρ : Env Γ} → refl ⊢ ρ ↝ ρ
-- --     extend : ∀ {τ Γ Γ' ρ ρ'} → {Γ↝Γ' : Γ ↝ Γ'} →
-- --                (v :  ⟦ τ ⟧) → Γ↝Γ' ⊢ ρ ↝ ρ' →
-- --                extend Γ↝Γ' ⊢ ρ ↝ (just v ∷ ρ')

-- --   _⊕ρ_ : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
-- --     {ρ ρ' ρ''} → 
-- --     Γ↝Γ' ⊢ ρ ↝ ρ' → Γ'↝Γ'' ⊢ ρ' ↝ ρ'' →
-- --     let Γ↝Γ'' = Γ↝Γ' ⊕ Γ'↝Γ'' in
-- --     Γ↝Γ'' ⊢ ρ ↝ ρ'' 
-- --   _⊕ρ_ ρ↝ρ' (refl) = ρ↝ρ'
-- --   _⊕ρ_ ρ↝ρ' (extend v ρ'↝ρ'') = extend v (ρ↝ρ' ⊕ρ ρ'↝ρ'')
  
  

-- --   -------------------------------------------------------------------------------- 
-- --   -- Futile attempt for the logical relation
-- --   --------------------------------------------------------------------------------
-- --   -- 
-- --   -- Equiv-term : forall {s : AType} {G} -> (env : Env G) -> (w : ATInt G s) -> (mv : Maybe ⟦ erase s ⟧) -> Set
-- --   -- Equiv-term {D x} env w (just v) = (∃₂ (λ v' n -> (ev n env w ≡ just v') × v ≡ v'))
-- --   -- Equiv-term {SFun s1 s2} {G} env w (just v) = 
-- --   --   ∀ {Γ' ρ' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ ρ') →
-- --   --      {xₐ : ATInt Γ' s1} → {x : ⟦ (erase s1) ⟧} →
-- --   --      Equiv-term ρ' xₐ (just x) → Equiv-term ρ' (w Γ↝Γ' xₐ) (v x)
-- --   -- Equiv-term {SNum} env w (just v) = w ≡ v
-- --   -- Equiv-term env w nothing = ⊤
  

-- --   -- Equiv-div : forall {s : AType} {G} (min-steps : ℕ) (env : Env G) (w : ATInt G s) (v : Maybe ⟦ erase s ⟧) -> Set
-- --   -- Equiv-div {D x} min-steps env w (just v) = ⊤
-- --   -- Equiv-div {SNum} min-steps env w (just v) = ⊤
-- --   -- Equiv-div {SFun s1 s2} min-steps env w (just v) = 
-- --   --   ∀ {Γ' ρ' Γ↝Γ'} → (Γ↝Γ' ⊢ env ↝ ρ') →
-- --   --      {xₐ : ATInt Γ' s1} → 
-- --   --      ({x : ⟦ (erase s1) ⟧} → Equiv-term ρ' xₐ (just x) → Equiv-div min-steps ρ' (w Γ↝Γ' xₐ) (v x))

-- --   -- Equiv-div {D x} min-steps env w nothing = ∃ (λ n' → min-steps ≤ n' × ev n' env w ≡ nothing)
-- --   -- Equiv-div {SFun s1 s2} min-steps env w nothing = ⊥
-- --   -- Equiv-div {SNum} min-steps env w nothing = ⊥

-- --   -- data Env-Equiv {Γ' : _} (ρ : Env Γ') :
-- --   --   ∀ {Δ} → (ρ' : AEnv Γ' Δ) → (ρ'' : Env (map erase Δ))
-- --   --   → Set where
-- --   -- -- ...
-- --   --   [] : Env-Equiv ρ [] []
-- --   --   cons : ∀ {α Δ} → let τ = erase α
-- --   --                        Γ = map erase Δ in
-- --   --           {ρ'' : Env Γ} → {ρ' : AEnv Γ' Δ} → 
-- --   --           Env-Equiv ρ ρ' ρ'' →
-- --   --           (va : ATInt Γ' α) → (v : τ) → 
-- --   --           Equiv ρ va v → 
-- --   --               Env-Equiv ρ (va ∷ ρ') (v ∷ ρ'')
