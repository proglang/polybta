-- Simply typed lambda calculus with nat streams
module STLCStream where

open import Coinduction
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Stream 
open import Data.Unit

data Type : Set where
  NAT : Type
  FUN : Type → Type → Type
  STREAM : Type

Cx : Set
Cx = List Type

infix 4 In
data In {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → In x (x ∷ xs)
  tl : ∀ {x y xs} → In x xs → In x (y ∷ xs)

data Exp (Γ : Cx) : Type -> Set where
  Var : ∀ {t} → In t Γ → Exp Γ t
  Lam : ∀ {t2} t1 → Exp (t1 ∷ Γ) t2 -> Exp Γ (FUN t1 t2)
  App : ∀ {t1 t2} → Exp Γ (FUN t1 t2) -> Exp Γ t1 -> Exp Γ t2

  Cst : ℕ → Exp Γ NAT
  Op2 : (ℕ → ℕ → ℕ) → Exp Γ NAT → Exp Γ NAT → Exp Γ NAT

  Str : ∀ {t} → Exp Γ t → Exp (t ∷ Γ) NAT → Exp (t ∷ Γ) t → Exp Γ STREAM
  Hd  : Exp Γ STREAM → Exp Γ NAT
  Tl  : Exp Γ STREAM → Exp Γ STREAM

T⟪_⟫ : Type → Set
T⟪ NAT ⟫ = ℕ
T⟪ FUN t t₁ ⟫ = T⟪ t ⟫ → T⟪ t₁ ⟫
T⟪ STREAM ⟫ = Stream ℕ

C⟪_⟫ : Cx → Set
C⟪ [] ⟫ = ⊤
C⟪ t ∷ Γ ⟫ = T⟪ t ⟫ × C⟪ Γ ⟫

evVar : ∀ {Γ t} → In t Γ → C⟪ Γ ⟫ → T⟪ t ⟫
evVar hd (proj₁ , proj₂) = proj₁
evVar (tl p) (proj₁ , proj₂) = evVar p proj₂

evStr : ∀ {S : Set} → S → (S → ℕ) → (S → S) → Stream ℕ
evStr seed head tail = head seed ∷ ♯ evStr (tail seed) head tail

ev : ∀ {Γ t} → Exp Γ t → C⟪ Γ ⟫ → T⟪ t ⟫
ev (Var x) ρ = evVar x ρ
ev (Lam t1 e) ρ = λ y → ev e (y , ρ)
ev (App e e₁) ρ = ev e ρ (ev e₁ ρ)
ev (Cst x) ρ = x
ev (Op2 x e e₁) ρ = x (ev e ρ) (ev e₁ ρ)
ev (Str e e₁ e₂) ρ = evStr (ev e ρ) (λ y → ev e₁ (y , ρ)) (λ y → ev e₂ (y , ρ))
ev (Hd e) ρ = head (ev e ρ)
ev (Tl e) ρ = tail (ev e ρ)

e_ones : Exp [] STREAM
e_ones = Str (Cst 1) (Var hd) (Var hd)

ones : Stream ℕ
ones = ev e_ones tt

e_nats_from : Exp [] (FUN NAT STREAM)
e_nats_from = Lam NAT (Str (Var hd) (Var hd) (Op2 _+_ (Cst 1) (Var hd)))

nats : Stream ℕ
nats = ev (App e_nats_from (Cst 0)) tt
