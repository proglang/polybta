module Lib where

open import Data.Nat public
open import Data.List public
open import Data.Product public using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; ∃ ; Σ-syntax)
open import Data.Sum public using (_⊎_ ; [_,_]′ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality public hiding ([_])

infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈ (x ∷ xs)
  tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B → C → D) {xa ya xb yb xc yc} →
  xa ≡ ya → xb ≡ yb → xc ≡ yc → f xa xb xc ≡ f ya yb yc
cong₃ f refl refl refl = refl
