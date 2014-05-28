{- The base language; simply typed lambda calculus with nats, addition, sums and products -}
module PBase where
open import PLib
open import Level using (Lift)

data Type : ℕ →  Set where
  Str : ∀ {n} → Type n
  Num : ∀ {n} → Type n
  Fun : ∀ {n} → Type n → Type n → Type n
  All : ∀ {n} → Type (suc n) → Type n
  Var : ∀ {n} → Fin n → Type n

Ctx : ℕ →  Set 
Ctx n = List (Type n)

↑-var : ∀ {n} → Fin (suc (suc n)) → Fin n → Fin (suc n)
↑-var fzero x = fsuc x
↑-var (fsuc j) fzero = fzero
↑-var (fsuc j) (fsuc x) = fsuc (↑-var j x)

-- shift a type except the first j variables
↑ : ∀ {n} → Fin (suc (suc n)) → Type n → Type (suc n)
↑ j Str = Str
↑ j Num = Num
↑ j (Fun τ τ₁) = Fun (↑ j τ) (↑ j τ₁)
↑ j (All τ) = All (↑ (fsuc j) τ)
↑ j (Var x) = Var (↑-var j x)

-- shift every type in the environment
ctx-↑ : ∀ {n} → Ctx n → Ctx (suc n)
ctx-↑ [] = []
ctx-↑ (τ ∷ Γ) = ↑ fzero τ ∷ ctx-↑ Γ

tsubst-var : ∀ {n} → (j : ℕ) → Fin (suc (j + n)) → Type n → Type (j + n)
tsubst-var zero fzero τ' = τ'
tsubst-var zero (fsuc x) τ' = Var x
tsubst-var (suc j) fzero τ' = Var fzero
tsubst-var (suc j) (fsuc x) τ' = ↑ fzero (tsubst-var j x τ')

-- substitute for type variable j
tsubst : ∀ {n} (j : ℕ) → Type (suc (j + n)) → Type n → Type (j + n)
tsubst j Str τ' = Str
tsubst j Num τ' = Num
tsubst j (Fun τ τ₁) τ' = Fun (tsubst j τ τ') (tsubst j τ₁ τ')
tsubst j (All τ) τ' = All (tsubst (suc j) τ τ')
tsubst j (Var x) τ' = tsubst-var j x τ'

-- substitute for type variable 0
_↓_ : ∀ {n} → Type (suc n) → Type n → Type n
Str ↓ τ' = Str
Num ↓ τ' = Num
Fun τ τ₁ ↓ τ' = Fun (τ ↓ τ') (τ₁ ↓ τ')
All τ ↓ τ' = All (tsubst 1 τ τ')
Var fzero ↓ τ' = τ'
Var (fsuc x) ↓ τ' = Var x

data Exp {n : ℕ} (Γ : Ctx n) : Type n → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ') → Exp Γ τ → Exp Γ τ'
  TLam : ∀ {τ} → Exp (ctx-↑ Γ) τ → Exp Γ (All τ)
  TApp : ∀ {τ} → Exp Γ (All τ) → (τ' : Type n) → Exp Γ (τ ↓ τ')

TInt : ∀ {ℓ n} → Type n → Vec (Set (Level.suc ℓ)) n → Set (Level.suc ℓ)
TInt {ℓ} Str η = Set ℓ
TInt Num η = Lift ℕ
TInt (Fun τ τ₁) η = TInt τ η → TInt τ₁ η
TInt {ℓ} (All τ) η = ∀ (A : Set ℓ) → TInt τ (cons (Lift {ℓ = Level.suc ℓ} A) η)
TInt {ℓ} (Var x) η = lookup x η

-- does not work like this

data Env (ℓ : Level.Level) : (n : ℕ) → Ctx n → (η : Vec (Set ℓ) n) → Set (Level.suc ℓ) where 
  []    : Env ℓ 0 [] []
  cons : ∀ {n} (Γ : Ctx n) (A : Set ℓ) (x : A) → (η : Vec (Set ℓ) n) → Env ℓ n Γ η → Env ℓ (suc n) (ctx-↑ Γ) (cons A η)

{-

lookupE : ∀ { ℓ n } {τ : Type n} { Γ : Ctx n } → τ ∈ Γ → (η : Vec (Set ℓ) n) → Env ℓ n Γ η → TInt τ η
lookupE hd η (vcons Γ .η ρ v) = {!!}
lookupE hd (cons _ η) (tcons (τ ∷ Γ) .η _ ρ) = {!!}
lookupE (tl x) η ρ = {!!}
-}

ev : ∀ {ℓ} {n} {τ : Type n} {Γ : Ctx n} → Exp Γ τ → (η : Vec (Set ℓ) n) →  Env ℓ n Γ η → TInt τ η 
ev (EVar x) η ρ = {!!}
ev {Γ = Γ} (ELam e) η ρ = λ z → ev e η {!cons!}
ev (EApp e e₁) η ρ = ev e η ρ (ev e₁ η ρ)
ev {Γ = Γ} (TLam e) η ρ = λ A → ev e (cons (Lift A) η) {!!}
ev {ℓ} (TApp e τ') η ρ with ev e η ρ | ev {Level.suc ℓ} e (vmap (Lift {ℓ = Level.suc ℓ}) η) {!!} | TInt τ' η
... | ev_e | ev_e+ | A' = {!!}


