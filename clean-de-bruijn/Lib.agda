{- General purpose utilities -}
module Lib where

open import Data.Nat public hiding (_<_) 
open import Function public using (_∘_)
open import Data.List public 
open import Data.Product public using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; ∃)
open import Data.Sum public using (_⊎_ ; [_,_]′ ; inj₁ ; inj₂)
open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality public hiding ([_])

open import Category.Functor public

-- Pointer into a list. It is similar to list membership as defined in
-- Data.List.AnyMembership, rather than going through propositional
-- equality, it asserts the existence of the referenced element
-- directly.
infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈ (x ∷ xs)
  tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

mapIdx : {A B : Set} → (f : A → B) →
         {x : A} {xs : List A} → x ∈ xs → f x ∈ map f xs
mapIdx f hd = hd
mapIdx f (tl x₁) = tl (mapIdx f x₁)

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B → C → D) {xa ya xb yb xc yc} →
  xa ≡ ya → xb ≡ yb → xc ≡ yc → f xa xb xc ≡ f ya yb yc
cong₃ f refl refl refl = refl

-- Extension of lists at the front and, as a generalization, extension
-- of lists somewhere in the middle.

-- Extension of a list by consing elements at the front. 
data _↝_ {A : Set} : List A → List A → Set where
  refl   : ∀ {Γ}      → Γ ↝ Γ
  extend : ∀ {Γ Γ' τ} → Γ ↝ Γ' → Γ ↝ (τ ∷ Γ')

_⊕_ : ∀ {A : Set}{Γ Γ' Γ'' : List A} → 
    Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
_⊕_ Γ↝Γ' refl = Γ↝Γ'                                 
_⊕_ Γ↝Γ' (extend Γ'↝Γ'') = extend (Γ↝Γ' ⊕ Γ'↝Γ'')

-- Of course, refl is the identity for combining two extensions.
lem-refl-id : ∀ {A : Set} {Γ Γ' : List A} →
                  (Γ↝Γ' : Γ ↝ Γ') →
                  Γ↝Γ' ≡ (refl ⊕ Γ↝Γ')  
lem-refl-id refl = refl
lem-refl-id (extend Γ↝Γ') =
  cong extend (lem-refl-id Γ↝Γ')
-- TODO: why does this work?
-- lem-refl-id (extend Γ↝Γ') = lem-refl-id (extend Γ↝Γ')

-- Extending a list in the middle: 
data _↝_↝_ {A : Set} : List A → List A → List A → Set where
  -- First prepend the extension list to the common suffix
  refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ'' 
  -- ... and then add the common prefix
  extend : ∀ {Γ Γ' Γ'' τ} →
               Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'') 