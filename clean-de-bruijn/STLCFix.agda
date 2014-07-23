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
  Fix : forall {t1 t2} -> Exp G (Fun (Fun t1 t2) (Fun t1 t2)) -> Exp G (Fun t1 t2)
  
module Examples where
  loop : forall {G} -> Exp G (Fun Num Num) 
  loop = Fix (Lam _ (Var hd))
  
  nofix : forall {G} -> Exp G Num
  nofix = App (Fix (Lam _ (Lam _ (C 42)))) (C 5)
  
  
  iter : forall {G t} -> Exp G (Fun (Fun t t) (Fun t (Fun Num t)))
  iter = Lam _ (Lam _ ((Fix (Lam _ (Lam _ (NatCase (Var hd) (Var (tl (tl hd))) (App (Var (tl (tl hd))) (Var hd))))))))
  

  inc : forall {G} -> Exp G (Fun Num Num)
  inc = (App (App iter (Lam _ (Suc (Var hd)))) (C 1))
  
  
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
    

-- More usefull: step-indexing evaluation

module Step where

  ⟦_⟧ : Type -> Set
  ⟦ Num ⟧ = ℕ
  ⟦ Fun t1 t2 ⟧ = (fuel : ℕ) -> ⟦ t1 ⟧ -> Maybe ⟦ t2 ⟧ 
  
  open Env (⟦_⟧)
    
  -- This does not work... we need to put the recursive value ontop of the environment somehow
  ev : forall {G t} -> (fuel : ℕ) -> Env G -> Exp G t -> Maybe ⟦ t ⟧
  ev' : forall {G t} -> (fuel : ℕ) -> Env G -> Exp G t -> Maybe ⟦ t ⟧ -- checks the gas
  ev _ env (C x) = just x
  ev fuel env (NatCase e e₁ e₂) with ev' fuel env e
  ... | just zero = ev' fuel env e₁
  ... | just (suc n) = ev' fuel (n ∷ env) e₂
  ... | nothing = nothing
  ev fuel env (Suc e) = suc <$> ev' fuel env e
  ev _ env (Var x) = just (lookup x env)
  ev _ env (Lam t1 e) = just (λ fuel x → ev' fuel (x ∷ env) e)
  ev fuel env (App e e₁) = join (ev' fuel env e ⊛ pure fuel ⊛ ev' fuel env e₁)
  ev zero env (Fix e) = nothing -- abort
  ev (suc fuel) env (Fix e) = ev' fuel env (App e (Fix e))
  
  ev' zero env e = nothing
  ev' (suc fuel) env e = ev fuel env e

  -- -- with ev (suc fuel) env e 
  -- -- ... | nothing = nothing
  -- -- ... | just f = f (suc fuel) =<< ev fuel env (App e (Fix e)) --  
  
  -- module EvalExamples where
  --   open Examples
    
  --   ex1 : ev 20 [] loop ≡ nothing
  --   ex1 = refl
  
  --   ex2 : ev 3000 [] (App inc (C 3)) ≡ nothing
  --   ex2 = refl
    
  --   -- BAHHH!
  --   ex3 : ev 300 [] nofix ≡ nothing
  --   ex3 = refl
