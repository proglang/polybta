-- Partial evaluation of the simply typed lambda calculus with a fixpoint combinator.
-- Work in progress
module PE-STLCFix where

open import Lib
open Auxiliaries
open import Terms
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
