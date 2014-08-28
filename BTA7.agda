--extended with both iterators and recursors
module BTA7 where
open import Lib
open import Data.Empty

--base types
data Type : Set where
  Num : Type
  Fun : Type → Type → Type
  Prd : Type → Type → Type
  Sum : Type → Type → Type
Ctx = List Type

data Exp (Γ : Ctx) : Type → Set where
  EVar : ∀ {τ} → τ ∈ Γ → Exp Γ τ
  ECst : ℕ → Exp Γ Num
  ESuc : Exp Γ Num → Exp Γ Num
  EIt : ∀ {τ} → Exp Γ Num → Exp Γ τ → Exp Γ (Fun τ τ) → Exp Γ τ
  ERec  : ∀ {τ} → Exp Γ τ → Exp Γ (Fun Num (Fun τ τ)) → Exp Γ Num
                → Exp Γ τ
  EAdd : Exp Γ Num → Exp Γ Num → Exp Γ Num
  ELam : ∀ {τ τ'} → Exp (τ ∷ Γ) τ' → Exp Γ (Fun τ τ')
  EApp : ∀ {τ τ'} → Exp Γ (Fun τ τ') → Exp Γ τ → Exp Γ τ'
  EPair : ∀ {τ τ'} → Exp Γ τ → Exp Γ τ' → Exp Γ (Prd τ τ')
  EFst :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ
  ESnd :  ∀ {τ τ'} → Exp Γ (Prd τ τ') → Exp Γ τ'
  EInl :  ∀ {τ τ'} → Exp Γ τ → Exp Γ (Sum τ τ')
  EInr :  ∀ {τ τ'} → Exp Γ τ' → Exp Γ (Sum τ τ')
  ECase : ∀ {τ τ' τ''} → Exp Γ (Sum τ τ') →
          Exp (τ ∷ Γ) τ'' → Exp (τ' ∷ Γ) τ'' → Exp Γ τ''
 


TInt : Type → Set
TInt Num = ℕ
TInt (Fun τ₁ τ₂) = TInt τ₁ → TInt τ₂
TInt (Prd τ₁ τ₂) = TInt τ₁ × TInt τ₂
TInt (Sum τ₁ τ₂) = TInt τ₁ ⊎ TInt τ₂
data Env : Ctx → Set where 
  [] : Env []
  _∷_ : ∀ {τ Γ} → TInt τ → Env Γ → Env (τ ∷ Γ)

lookupE : ∀ { τ Γ } → τ ∈ Γ → Env Γ → TInt τ
lookupE hd (x ∷ ρ) = x
lookupE (tl v) (_ ∷ ρ) = lookupE v ρ

natrec : ∀ {t : Set} → ℕ → t → (ℕ → (t → t)) → t
natrec zero v0 vs = v0
natrec (suc n) v0 vs = vs n (natrec n v0 vs)

natit : ∀ { t : Set } → ℕ → t → (t → t) → t
natit zero v0 vs = v0
natit (suc n) v0 vs = vs (natit n v0 vs)




ev : ∀ {τ Γ} → Exp Γ τ → Env Γ → TInt τ
ev (EVar v) ρ = lookupE v ρ
ev (ECst x) ρ = x
ev (ESuc e) ρ = suc (ev e ρ)
ev (EIt e e0 es) ρ = natit (ev e ρ) (ev e0 ρ) (ev es ρ)
ev (ERec v u n) ρ = natrec (ev n ρ) (ev v ρ) (ev u ρ)
ev (EAdd e f) ρ = ev e ρ + ev f ρ
ev (ELam e) ρ = λ x → ev e (x ∷ ρ)
ev (EApp e f) ρ = ev e ρ (ev f ρ)
ev (EPair e f) ρ = ev e ρ , ev f ρ
ev (EFst e) ρ = proj₁ (ev e ρ)
ev (ESnd e) ρ = proj₂ (ev e ρ)
ev (EInl e) ρ = inj₁ (ev e ρ)
ev (EInr e) ρ = inj₂ (ev e ρ)
ev (ECase e e₁ e₂) ρ with ev e ρ
... | inj₁ v = ev e₁ (v ∷ ρ)
... | inj₂ v = ev e₂ (v ∷ ρ)


--two-level types
data AType : Set where
  SNum  : AType
  SFun  : AType → AType → AType
  SPrd  : AType → AType → AType
  SSum  : AType → AType → AType
  D     : Type → AType

ACtx = List AType



-- The mapping from annotated types to residual types is straightforward.
erase : AType → Type
erase SNum = Num
erase (SFun α₁ α₂) = Fun (erase α₁) (erase α₂)
erase (SPrd α₁ α₂) = Prd (erase α₁) (erase α₂)
erase (SSum α₁ α₂) = Sum (erase α₁) (erase α₂)
erase (D x) = x

mutual 
  data Liftable : AType → Set where
    D : ∀ τ → Liftable (D τ)
    SCst : Liftable SNum
    SSum : ∀ {α₁ α₂} →
      Liftable α₁ → Liftable α₂ → Liftable (SSum α₁ α₂)
    SPrd : ∀ {α₁ α₂} →
      Liftable α₁ → Liftable α₂ → Liftable (SPrd α₁ α₂)
    SFun : ∀ {α₁ α₂} →
      Liftable⁻ α₁ → Liftable α₂ → Liftable (SFun α₁ α₂)

  data Liftable⁻ : AType → Set where
    D : ∀ τ → Liftable⁻ (D τ)
    SPrd : ∀ {α₁ α₂} →
      Liftable⁻ α₁ → Liftable⁻ α₂ → Liftable⁻ (SPrd α₁ α₂)
    SFun : ∀ {α₁ α₂} →
      Liftable α₁ → Liftable⁻ α₂ → Liftable⁻ (SFun α₁ α₂)

data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  SCst : ℕ → AExp Δ SNum
  SSuc : AExp Δ SNum → AExp Δ SNum
  SIt : ∀ {α} → AExp Δ SNum → AExp Δ α → AExp Δ (SFun α α) → AExp Δ α
  --static recursor
  SRec  : ∀ {α} → AExp Δ α → AExp Δ (SFun SNum (SFun α α)) → AExp Δ SNum 
               → AExp Δ α
  SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
  SLam : ∀ {α₁ α₂} → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
  SApp : ∀ {α₁ α₂} → AExp Δ (SFun α₁ α₂) → AExp Δ α₁ → AExp Δ α₂
  DCst : ℕ → AExp Δ (D Num)
  DSuc : AExp Δ (D Num) → AExp Δ (D Num)
  DIt : ∀ {σ} → AExp Δ (D Num) → AExp Δ (D σ) → AExp Δ (D (Fun σ σ)) → AExp Δ (D σ)
  --dynamic recursor
  DRec  : ∀ {σ} → AExp Δ (D σ) → AExp Δ (D (Fun Num (Fun σ σ))) → AExp Δ (D Num) 
               → AExp Δ (D σ)
  DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
  DLam : ∀ {σ₁ σ₂} → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  DApp : ∀ {σ₁ σ₂} → AExp Δ (D (Fun σ₂ σ₁)) → AExp Δ (D σ₂) → AExp Δ (D σ₁)
  -- Dynamic pairs and sums
  SPair : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ α₂ → AExp Δ (SPrd α₁ α₂)
  SInl   : ∀ {α₁ α₂} → AExp Δ α₁ → AExp Δ (SSum α₁ α₂)
  SInr   : ∀ {α₁ α₂} → AExp Δ α₂ → AExp Δ (SSum α₁ α₂)
  SFst  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₁
  SSnd  : ∀ {α₁ α₂} → AExp Δ (SPrd α₁ α₂) → AExp Δ α₂
  SCase : ∀ {α₁ α₂ α₃} → AExp Δ (SSum α₁ α₂) → AExp (α₁ ∷ Δ) α₃ → AExp (α₂ ∷ Δ) α₃ → AExp Δ α₃
  DPair  : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D σ₂) → AExp Δ (D (Prd σ₁ σ₂))
  DInl   : ∀ {σ₁ σ₂} → AExp Δ (D σ₁) → AExp Δ (D (Sum σ₁ σ₂))
  DInr   : ∀ {σ₁ σ₂} → AExp Δ (D σ₂) → AExp Δ (D (Sum σ₁ σ₂))
  DFst  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₁)
  DSnd  : ∀ {σ₁ σ₂} → AExp Δ (D (Prd σ₁ σ₂)) → AExp Δ (D σ₂)
  DCase : ∀ {σ₁ σ₂ σ₃} → AExp Δ (D (Sum σ₁ σ₂)) → AExp ((D σ₁) ∷ Δ) (D σ₃) → AExp ((D σ₂) ∷ Δ) (D σ₃) → AExp Δ (D σ₃) 
  Lift : {α : AType} →
    Liftable α → AExp Δ α  → AExp Δ (D (erase α))

-- type interpretation
ATInt : Ctx → AType → Set
ATInt _ SNum          = ℕ
ATInt Γ (D σ)         = Exp Γ σ
ATInt Γ (SFun α₁ α₂)  =
  ∀ {Γ'} → Γ ↝ Γ' → ATInt Γ' α₁ → ATInt Γ' α₂
ATInt Γ (SPrd α₁ α₂) = ATInt Γ α₁ × ATInt Γ α₂
ATInt Γ (SSum α₁ α₂) = (ATInt Γ α₁) ⊎ (ATInt Γ α₂)

-- TODO: AEnv is actually an instance of Chlipalas `tuple' type. Env similarly...
data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  _∷_ : ∀ {α Δ} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)


elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var refl τ∈Γ = τ∈Γ
elevate-var (extend Γ↝Γ') τ∈Γ = tl (elevate-var Γ↝Γ' τ∈Γ)

elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ'' 
elevate-var2 (refl x) x₁ = elevate-var x x₁
elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)


elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (ECst x) = ECst x
elevate Γ↝Γ'↝Γ'' (ESuc e) = ESuc (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EIt e e₀ e₁) = EIt (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₀) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ERec v u n) = ERec (elevate Γ↝Γ'↝Γ'' v) (elevate Γ↝Γ'↝Γ'' u) (elevate Γ↝Γ'↝Γ'' n)
elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (EPair e e₁) =  EPair (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (EInl e) = EInl (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EInr e) = EInr (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (EFst e) = EFst (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ESnd e) = ESnd (elevate Γ↝Γ'↝Γ'' e)
elevate Γ↝Γ'↝Γ'' (ECase c e₁ e₂) = ECase (elevate Γ↝Γ'↝Γ'' c) (elevate (extend Γ↝Γ'↝Γ'') e₁) (elevate (extend Γ↝Γ'↝Γ'') e₂)

exp↑ : ∀ {τ τ' Γ} → Exp Γ τ' → Exp (τ ∷ Γ) τ'
exp↑ e = elevate (refl (extend refl)) e

int↑ : ∀ { α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
int↑ refl v = v
int↑ {D τ} (extend Γ↝Γ') e = exp↑ (int↑ Γ↝Γ' e)
int↑ {SNum} _ v = v
int↑ {SFun α α₁} Γ↝Γ' f =
  λ Γ'↝Γ'' x → f (Γ↝Γ' ⊕ Γ'↝Γ'') x
int↑ {SPrd α α₁} Γ↝Γ' (proj₁ , proj₂) = int↑ Γ↝Γ' proj₁ , int↑ Γ↝Γ' proj₂
int↑ {SSum α α₁} Γ↝Γ' (inj₁ x) = inj₁ (int↑ Γ↝Γ' x)
int↑ {SSum α α₁} Γ↝Γ' (inj₂ y) = inj₂ (int↑ Γ↝Γ' y)

env↑ : ∀ { Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ _ [] = []
env↑ Γ↝Γ' (x ∷ ρ) = int↑ Γ↝Γ' x ∷ env↑ Γ↝Γ' ρ

addFresh : ∀ {τ Γ Δ} → AEnv Γ Δ → AEnv (τ ∷ Γ) (D τ ∷ Δ)
addFresh ρ = EVar hd ∷ env↑ (extend refl) ρ

lookup : ∀ {Γ Δ α} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α
lookup hd (v ∷ _) = v 
lookup (tl x) (_ ∷ ρ) = lookup x ρ

-- TODO: these should be called reify/reflect, see also above
mutual 
  lift : ∀ {Γ α} → Liftable α → ATInt Γ α → (Exp Γ (erase α))
  lift (D τ) v = v
  lift SCst v = ECst v
  lift (SSum ty ty₁) (inj₁ a) = EInl (lift ty a)
  lift (SSum ty ty₁) (inj₂ b) = EInr (lift ty₁ b)
  lift (SPrd ty ty₁) (v1 , v2) = EPair (lift ty v1) (lift ty₁ v2)
  lift (SFun {α₁} ty₁ ty₂) f =
    ELam let x = (embed ty₁ (EVar hd)) in
         lift ty₂ (f (extend refl) x)

  embed : ∀ {Γ α} →
    Liftable⁻ α → Exp Γ (erase α) → (ATInt Γ α)
  embed (D τ) e = e
  embed (SPrd ty ty₁) e = embed ty (EFst e) , embed ty₁ (ESnd e)
  embed {Γ} (SFun {α} ty₁ ty₂) e = 
    λ Γ↝Γ' v₁ → embed ty₂ (EApp (int↑ Γ↝Γ' e) (lift ty₁ v₁))

pe : ∀ { Γ Δ α } → 
         AExp Δ α → AEnv Γ Δ → ATInt Γ α
pe (Var x) ρ       = lookup x ρ
pe (DLam e) ρ      = ELam (pe e (addFresh ρ))
pe (SApp f e) ρ    = (pe f ρ) refl (pe e ρ)
pe (SLam {α} e) ρ  = λ Γ↝Γ' x → pe e (x ∷ env↑ Γ↝Γ' ρ)
pe (DApp f e) ρ    = EApp (pe f ρ) (pe e ρ)
pe (SCst x) _      = x
pe (DCst x) _      = ECst x
pe (SSuc e) ρ      = suc (pe e ρ)
pe (DSuc e) ρ      = ESuc (pe e ρ)
pe (SIt e e₀ e₁) ρ = natit (pe e ρ) (pe e₀ ρ) (pe e₁ ρ refl)
pe (DIt e e₀ e₁) ρ = EIt (pe e ρ) (pe e₀ ρ) (pe e₁ ρ)
--partial evaluation of static and dynamic recursors
pe {Γ} (SRec v u n) ρ = natrec (pe n ρ) (pe v ρ) (λ n₁ → pe u ρ {Γ} refl n₁ {Γ} refl)
pe (DRec v u n) ρ = ERec (pe v ρ) (pe u ρ) (pe n ρ)
pe (SAdd e f) ρ    = (pe e ρ) + (pe f ρ) 
pe (DAdd e f) ρ    = EAdd (pe e ρ) (pe f ρ) 
pe (SPair e e₁) ρ = pe e ρ , pe e₁ ρ
pe (SInl e) ρ = inj₁ (pe e ρ)
pe (SInr e) ρ = inj₂ (pe e ρ)
pe (SFst e) ρ = proj₁ (pe e ρ)
pe (SSnd e) ρ = proj₂ (pe e ρ)
pe (SCase e e₁ e₂) ρ with pe e ρ
... | inj₁ v = pe e₁ (v ∷ ρ)
... | inj₂ v = pe e₂ (v ∷ ρ)
pe (DPair e e₁) ρ = EPair (pe e ρ) (pe e₁ ρ)
pe (DInl e) ρ = EInl (pe e ρ)
pe (DInr e) ρ = EInr (pe e ρ)
pe (DFst e) ρ = EFst (pe e ρ)
pe (DSnd e) ρ = ESnd (pe e ρ)
pe (DCase e e₁ e₂) ρ = ECase (pe e ρ) (pe e₁ (addFresh ρ)) (pe e₂ (addFresh ρ))
pe (Lift lftbl e) ρ = lift lftbl (pe e ρ)

--examples

add : AExp [] (SFun SNum (D (Fun Num Num)))
add = SLam (DLam (SIt (Var (tl hd)) (Var hd) (SLam (DSuc (Var hd)))))

pe_add : ℕ → Exp [] (Fun Num Num)
pe_add n = pe (SApp add (SCst n)) []

mult : AExp [] (SFun SNum (D (Fun Num Num)))
mult = SLam (DLam (SIt (Var (tl hd)) (DCst 0) (SLam (DAdd (Var hd) (Var (tl hd))))))

multn : ℕ → AExp [] (D (Fun Num Num))
multn n = SApp mult (SCst n)

pe_mult : ℕ → Exp [] (Fun Num Num)
pe_mult n = pe (multn n) []


dmult : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
dmult = DLam (DLam (DIt (Var (tl hd)) (DCst 0) (DLam (DAdd (Var hd) (Var (tl hd))))))

pe_dmult3 : Exp [] (Fun Num Num)
pe_dmult3 = pe (DApp dmult (DCst 3)) []

power : AExp [] (SFun SNum (D (Fun Num Num)))
power = SLam (DLam (DApp (DLam
        (SIt (Var (tl (tl hd)))
              (DCst 1)
              (SLam (DApp (DApp (Var (tl hd)) (Var hd)) (Var (tl (tl hd))))))) dmult))


pe_power : ℕ → Exp [] (Fun Num Num)
pe_power n = pe (SApp power (SCst n)) []


predecessor : AExp [] (SFun SNum SNum)
predecessor = SLam (SFst (SIt (Var hd) (SPair (SCst 0) (SCst 0))
                                        (SLam (SPair (SSnd (Var hd))
                                              (SSuc (SSnd (Var hd)))))))

pe_predecessor : ℕ → ℕ
pe_predecessor n = pe {[]} (SApp predecessor (SCst n)) []


iter : Exp [] (Fun (Fun Num Num) (Fun Num Num))
iter = ELam (ELam (EIt (ESuc (EVar hd)) (ECst 1) (EVar (tl hd))))


ack : Exp [ Fun (Fun Num Num) (Fun Num Num) ] (Fun Num (Fun Num Num))
ack = ELam (EIt (EVar hd) (ELam (ESuc (EVar hd))) (EVar (tl hd)))


ack-m-n : ℕ → ℕ → ℕ
ack-m-n m n = ev (EApp (EApp ack (ECst m)) (ECst n)) (ev iter [] ∷ [])

    
siter : AExp [] (SFun (D (Fun Num Num)) (SFun SNum (D Num)))
siter = SLam (SLam (SIt (SSuc (Var hd)) (DCst 1) (SLam (DApp (Var (tl (tl hd))) (Var hd)))))


diter : AExp [] (SFun (D (Fun Num Num)) (D (Fun Num Num)))
diter = SLam (DLam (DIt (DSuc (Var hd)) (DCst 1) (Var (tl hd))))


sack : AExp [ D (Fun (Fun Num Num) (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
sack = SLam (SIt (Var hd) (DLam (DSuc (Var hd))) (SLam (DApp (Var (tl (tl hd))) (Var hd))))

sack-m : ℕ → Exp [] (Fun Num Num)
sack-m m = pe (SApp sack (SCst m)) (iter ∷ [])

sack' : AExp [ SFun (D (Fun Num Num)) (D (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
sack' = SLam (SIt (Var hd) (DLam (DSuc (Var hd))) (Var (tl hd)))

sack'-m : ℕ → Exp [] (Fun Num Num)
sack'-m m = pe (SApp (SLam (SApp sack' (SCst m))) diter) []

--application of recursors


Add : AExp [] (SFun SNum (D (Fun Num Num)))
Add = SLam (DLam (SRec (Var hd) (SLam (SLam (DSuc (Var hd)))) (Var (tl hd))))


pe_Add : ℕ → Exp [] (Fun Num Num)
pe_Add n = pe (SApp Add (SCst n)) []


Mult : AExp [] (SFun SNum (D (Fun Num Num)))
Mult = SLam (DLam (SRec (DCst 0) (SLam (SLam (DAdd (Var hd) (Var (tl (tl hd)))))) (Var (tl hd))))


Multn : ℕ → AExp [] (D (Fun Num Num))
Multn n = SApp Mult (SCst n)

pe_Mult : ℕ → Exp [] (Fun Num Num)
pe_Mult n = pe (Multn n) []



dMult : ∀ {Δ} → AExp Δ (D (Fun Num (Fun Num Num)))
dMult = DLam (DLam (DRec (DCst 0) (DLam (DLam (DAdd (Var hd) (Var (tl (tl hd)))))) (Var (tl hd))))


pe_dMult3 : Exp [] (Fun Num Num)
pe_dMult3 = pe (DApp dMult (DCst 3)) []


Power : AExp [] (SFun SNum (D (Fun Num Num)))
Power = SLam (DLam (DApp (DLam
        (SIt (Var (tl (tl hd)))
              (DCst 1)
              (SLam (DApp (DApp (Var (tl hd)) (Var hd)) (Var (tl (tl hd))))))) dMult))


pe_Power : ℕ → Exp [] (Fun Num Num)
pe_Power n = pe (SApp Power (SCst n)) []


Predecessor : AExp [] (SFun SNum SNum)
Predecessor = SLam (SRec (SCst 0) (SLam (SLam (Var (tl hd)))) (Var hd))



pe_Predecessor : ℕ → ℕ
pe_Predecessor n = pe {[]} (SApp Predecessor (SCst n)) []


Iter : Exp [] (Fun (Fun Num Num) (Fun Num Num))
Iter = ELam (ELam (ERec (ECst 1) (ELam (EVar (tl (tl hd)))) (ESuc (EVar hd))))


Ack : Exp [ Fun (Fun Num Num) (Fun Num Num) ] (Fun Num (Fun Num Num))
Ack = ELam (ERec (ELam (ESuc (EVar hd))) (ELam (EVar (tl (tl hd)))) (EVar hd))


Ack-m-n : ℕ → ℕ → ℕ
Ack-m-n m n = ev (EApp (EApp Ack (ECst m)) (ECst n)) (ev Iter [] ∷ [])
    

Siter : AExp [] (SFun (D (Fun Num Num)) (SFun SNum (D Num)))
Siter = SLam (SLam (SRec (DCst 1) (SLam (SLam (DApp (Var (tl (tl (tl hd)))) (Var hd)))) (SSuc (Var hd))))


Diter : AExp [] (SFun (D (Fun Num Num)) (D (Fun Num Num)))
Diter = SLam (DLam (DRec (DCst 1) (DLam (Var (tl (tl hd)))) (DSuc (Var hd))))


Sack : AExp [ D (Fun (Fun Num Num) (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
Sack = SLam (SRec (DLam (DSuc (Var hd))) (SLam (SLam (DApp (Var (tl (tl (tl hd)))) (Var hd)))) (Var hd))


Sack-m : ℕ → Exp [] (Fun Num Num)
Sack-m m = pe (SApp Sack (SCst m)) (Iter ∷ [])


Sack' : AExp [ SFun (D (Fun Num Num)) (D (Fun Num Num)) ] (SFun SNum (D (Fun Num Num)))
Sack' = SLam (SRec (DLam (DSuc (Var hd))) (SLam (Var (tl (tl hd)))) (Var hd))


Sack'-m : ℕ → Exp [] (Fun Num Num)
Sack'-m m = pe (SApp (SLam (SApp Sack' (SCst m))) Diter) []

---------------------------------------------------
-- TODO: examples for higher order lifting
---------------------------------------------------
open import Data.Empty

lift-dec : (α : AType) → Dec (Liftable α)
lift-dec⁻ : (α : AType) → Dec (Liftable⁻ α)

lift-dec SNum = yes SCst
lift-dec (SFun α α₁) with lift-dec⁻ α | lift-dec α₁
... | yes lm | yes l = yes (SFun lm l)
... | no  nlm | _   = no f
  where f : (x : Liftable (SFun α α₁)) → ⊥
        f (SFun x₁ x₂) = nlm x₁
... |  _ | no nl = no f
  where f : (x : Liftable (SFun α α₁)) → ⊥
        f (SFun x₁ x₂) = nl x₂
lift-dec (SPrd α α₁) with lift-dec α | lift-dec α₁
... | yes lm | yes l = yes (SPrd lm l)
... | no  nlm | _   = no f
  where f : (x : Liftable (SPrd α α₁)) → ⊥
        f (SPrd x₁ x₂) = nlm x₁
... |  _ | no nl = no f
  where f : (x : Liftable (SPrd α α₁)) → ⊥
        f (SPrd x₁ x₂) = nl x₂
lift-dec (SSum α α₁) with lift-dec α | lift-dec α₁
... | yes lm | yes l = yes (SSum lm l)
... | no  nlm | _   = no f
  where f : (x : Liftable (SSum α α₁)) → ⊥
        f (SSum x₁ x₂) = nlm x₁
... |  _ | no nl = no f
  where f : (x : Liftable (SSum α α₁)) → ⊥
        f (SSum x₁ x₂) = nl x₂
lift-dec (D x) = yes (D x)
lift-dec⁻ SNum = no (λ ())
lift-dec⁻ (SFun α α₁) with lift-dec α | lift-dec⁻ α₁
... | yes lm | yes l = yes (SFun lm l)
... | no  nlm | _   = no f
  where f : (x : Liftable⁻ (SFun α α₁)) → ⊥
        f (SFun x₁ x₂) = nlm x₁
... |  _ | no nl = no f
  where f : (x : Liftable⁻ (SFun α α₁)) → ⊥
        f (SFun x₁ x₂) = nl x₂
lift-dec⁻ (SPrd α α₁) with lift-dec⁻ α | lift-dec⁻ α₁
... | yes lm | yes l = yes (SPrd lm l)
... | no  nlm | _   = no f
  where f : (x : Liftable⁻ (SPrd α α₁)) → ⊥
        f (SPrd x₁ x₂) = nlm x₁
... |  _ | no nl = no f
  where f : (x : Liftable⁻ (SPrd α α₁)) → ⊥
        f (SPrd x₁ x₂) = nl x₂
lift-dec⁻ (SSum α α₁) = no (λ ())
lift-dec⁻ (D x) = yes (D x)


----------------
-- Proving liftable by reflection
----------------

open import Relation.Nullary.Decidable
open import Data.Product
try-lift : ∀ {α Γ} → AExp Γ α → Dec (Liftable α)
try-lift {α} _ = lift-dec α 

ex-liftable1 : Liftable (SFun (D Num) (D Num))
ex-liftable1 = from-yes (lift-dec (SFun (D Num) (D Num)))

infer-lift' : {α : AType} {Δ : ACtx} → AExp Δ α → From-yes (lift-dec α)
infer-lift' e = from-yes (try-lift e)

infer-lift : ∀ {α Δ} → AExp Δ α → From-yes (lift-dec α) × AExp Δ α
infer-lift e = infer-lift' e , e

lift-id : AExp [] (SFun (D Num) (D Num)) → AExp [] (D (Fun Num Num))
lift-id e = Lift (infer-lift' e) e

ilift : ∀ {α Δ} → Liftable α × AExp Δ α → AExp Δ (D (erase α))
ilift p = uncurry Lift p

-- examples
e1 : AExp [] (SFun (D Num) (D Num))
e1 = (SLam (Var hd))

-- Liftable inferred
e1-lifted : _
e1-lifted = ilift (infer-lift e1)  -- liftable inferred

-- liftable inferred, without type signature; the only type needed is
-- for the function parameter (and the context)
e1-lifted' : AExp [] _
e1-lifted' = ilift (infer-lift (SLam {α₁ = D Num} (Var hd)))


-- duplication of α (first parameter)
e2 : AExp [] (SFun (SFun (D Num) (D Num)) (SFun (D Num) (D (Prd Num Num))))
e2 = (SLam 
       (SLam (DPair (SApp (Var (tl hd)) (Var hd))
             (DApp (ilift (infer-lift {α} (Var (tl hd))) ) (Var hd)))))
  where α = (SFun (D Num) (D Num))
             -- Arrr.. we still need α! 

--correctness proof
residualize : ∀ {α Δ} → AExp Δ α → Exp (Lib.map erase Δ) (erase α)
residualize (Var x) = EVar (mapIdx erase  x)
residualize (SCst x) = ECst x
residualize (SSuc e) = ESuc (residualize e)
residualize (SIt e e₀ e₁) = EIt (residualize e) (residualize e₀) (residualize e₁)
--static recursor
residualize (SRec v u n) = ERec (residualize v) (residualize u) (residualize n)
residualize (SAdd e e₁) = EAdd (residualize e) (residualize e₁)
residualize (SLam e) = ELam (residualize e)
residualize (SApp e e₁)  = EApp (residualize e) (residualize e₁)
residualize (DCst x)  = ECst x
residualize (DSuc e) = ESuc (residualize e)
residualize (DIt e e₀ e₁) = EIt (residualize e) (residualize e₀) (residualize e₁)
--dynamic recursor
residualize (DRec v u n) = ERec (residualize v) (residualize u) (residualize n)
residualize (DAdd e e₁) = EAdd (residualize e) (residualize e₁)
residualize (DLam e)  = ELam (residualize e)
residualize (DApp e e₁)  = EApp (residualize e) (residualize e₁)
residualize (SPair e e₁)  = EPair (residualize e)  (residualize e₁)
residualize (SInl e)  = EInl (residualize e)
residualize (SInr e)  = EInr (residualize e)
residualize (SFst e)  = EFst (residualize e)
residualize (SSnd e)  = ESnd (residualize e)
residualize (SCase e e₁ e₂)  = ECase (residualize e) (residualize e₁) (residualize e₂)
residualize (DPair e e₁)  = EPair (residualize e) (residualize e₁)
residualize (DInl e)  = EInl (residualize e)
residualize (DInr e)  = EInr (residualize e)
residualize (DFst e)  = EFst (residualize e)
residualize (DSnd e)  = ESnd (residualize e)
residualize (DCase e e₁ e₂)  = ECase (residualize e) (residualize e₁) (residualize e₂)
residualize (Lift lftbl e) = residualize e

-- Extending a value environment according to an extension of a
-- type environment

data _⊢_↝_ :
  ∀ {Γ Γ'} → Γ ↝ Γ' → Env Γ → Env Γ' → Set where
  refl : ∀ {Γ} {ρ : Env Γ} → refl ⊢ ρ ↝ ρ
  extend : ∀ {τ Γ Γ' ρ ρ'} → {Γ↝Γ' : Γ ↝ Γ'} →
             (v : TInt τ) → Γ↝Γ' ⊢ ρ ↝ ρ' →
             extend Γ↝Γ' ⊢ ρ ↝ (v ∷ ρ')
_⊕ρ_ : ∀ {Γ Γ' Γ''} {Γ↝Γ' : Γ ↝ Γ'} {Γ'↝Γ'' : Γ' ↝ Γ''}
  {ρ ρ' ρ''} → 
  Γ↝Γ' ⊢ ρ ↝ ρ' → Γ'↝Γ'' ⊢ ρ' ↝ ρ'' →
  let Γ↝Γ'' = Γ↝Γ' ⊕ Γ'↝Γ'' in
  Γ↝Γ'' ⊢ ρ ↝ ρ'' 
_⊕ρ_ ρ↝ρ' (refl) = ρ↝ρ'
_⊕ρ_ ρ↝ρ' (extend v ρ'↝ρ'') = extend v (ρ↝ρ' ⊕ρ ρ'↝ρ'')

-- Equivalent Imp Γ α and EImp τ values (where τ = sinj₂ipα α). As
-- (v : Imp Γ α) is not necessarily closed, equivalence is defined for
-- the closure (Env Γ, ImpΓ α)
postulate ext : ∀ {τ₁ τ₂} {f g : TInt τ₁ → TInt τ₂} →
                (∀ x → f x ≡ g x) → f ≡ g
Equiv : ∀ {α Γ} →
  (ρ : Env Γ) → (vₐ : ATInt Γ α) → (v : TInt (erase α)) → Set
Equiv {SNum} ρ nₐ n = nₐ ≡ n 
Equiv {D x} ρ e v = ev e ρ ≡ v
Equiv {SFun α₁ α₂} {Γ} ρ fₐ f =
  ∀ {Γ' ρ' Γ↝Γ'} → (Γ↝Γ' ⊢ ρ ↝ ρ') →
     {xₐ : ATInt Γ' α₁} → {x : TInt (erase α₁)} →
     Equiv ρ' xₐ x → Equiv ρ' (fₐ Γ↝Γ' xₐ) (f x)
Equiv {SPrd α α₁} ρ (proj₁ , proj₂) (proj₁' , proj₂') =
  Equiv ρ proj₁ proj₁' × Equiv ρ proj₂ proj₂' 
Equiv {SSum α α₁} ρ (inj₁ a) (inj₁ a₁) = Equiv ρ a a₁
Equiv {SSum α α₁} ρ (inj₂ b) (inj₂ b₁) = Equiv ρ b b₁ 
Equiv {SSum α α₁} ρ (inj₁ a) (inj₂ b) = ⊥  
Equiv {SSum α α₁} ρ (inj₂ b) (inj₁ a) = ⊥  


-- Equivalence of AEnv and Env environments. They need to provide
-- Equivalent bindings for a context Δ/sinj₂ipΔ Δ. Again, the
-- equivalence is defined for a closure (Env Γ', AEnv Γ' Δ).
data Env-Equiv {Γ' : _} (ρ : Env Γ') :
  ∀ {Δ} → (ρ' : AEnv Γ' Δ) → (ρ'' : Env (Lib.map erase Δ))
  → Set where
-- ...
  [] : Env-Equiv ρ [] []
  cons : ∀ {α Δ} → let τ = erase α
                       Γ = Lib.map erase Δ in
          {ρ'' : Env Γ} → {ρ' : AEnv Γ' Δ} → 
          Env-Equiv ρ ρ' ρ'' →
          (va : ATInt Γ' α) → (v : TInt τ) → 
          Equiv ρ va v → 
              Env-Equiv ρ (va ∷ ρ') (v ∷ ρ'')

-- Ternary helper relation for environment extensions, analogous to _↝_↝_ for contexts
data _⊢_↝_↝_⊣ : ∀ { Γ Γ' Γ''} → Γ ↝ Γ' ↝ Γ'' → Env Γ → Env Γ' → Env Γ'' → Set where
  refl : ∀ {Γ Γ''} {Γ↝Γ'' : Γ ↝ Γ''} { ρ ρ'' } →
         Γ↝Γ'' ⊢ ρ ↝ ρ'' →
         refl Γ↝Γ'' ⊢ ρ ↝ [] ↝ ρ'' ⊣
  extend : ∀ {Γ Γ' Γ'' τ} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''} { ρ ρ' ρ'' } →
           Γ↝Γ'↝Γ'' ⊢ ρ ↝ ρ' ↝ ρ'' ⊣ →
           (v : TInt τ) → extend Γ↝Γ'↝Γ'' ⊢ (v ∷ ρ) ↝ (v ∷ ρ') ↝ (v ∷ ρ'') ⊣

-- the following lemmas are sinj₂ong versions of the shifting
-- functions, proving that consistent variable renaming preserves
-- equivalence (and not just typing).
lookup-elevate-≡ : ∀ {τ Γ Γ'} {Γ↝Γ' : Γ ↝ Γ'}
                   {ρ : Env Γ} {ρ' : Env Γ'} →
                   Γ↝Γ' ⊢ ρ ↝ ρ' → 
                   (x : τ ∈ Γ) → lookupE x ρ ≡ lookupE (elevate-var Γ↝Γ' x) ρ'
lookup-elevate-≡ (refl) x = refl
lookup-elevate-≡ (extend v ρ↝ρ') x = lookup-elevate-≡ ρ↝ρ' x

lookup-elevate2-≡ : ∀ {τ Γ Γ' Γ''} {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                   {ρ : Env Γ} {ρ' : Env Γ'} {ρ'' : Env Γ''} →
                   Γ↝Γ'↝Γ'' ⊢ ρ ↝ ρ' ↝ ρ'' ⊣ → 
                   (x : τ ∈ Γ) → lookupE x ρ ≡ lookupE (elevate-var2 Γ↝Γ'↝Γ'' x) ρ''
lookup-elevate2-≡ (refl Γ↝Γ') x = lookup-elevate-≡ Γ↝Γ' x
lookup-elevate2-≡ (extend ρ↝ρ'↝ρ'' v) hd = refl
lookup-elevate2-≡ (extend ρ↝ρ'↝ρ'' _) (tl x)
  rewrite lookup-elevate2-≡ ρ↝ρ'↝ρ'' x = refl


elevate-≡ : ∀ {τ Γ Γ' Γ''}
                  {Γ↝Γ'↝Γ'' : Γ ↝ Γ' ↝ Γ''}
                  {ρ : Env Γ} {ρ' : Env Γ'} {ρ'' : Env Γ''} →
                  Γ↝Γ'↝Γ'' ⊢ ρ ↝ ρ' ↝ ρ'' ⊣ →
                  (e : Exp Γ τ) →
                  ev e ρ ≡ ev (elevate Γ↝Γ'↝Γ'' e) ρ''
elevate-≡ ρ↝ρ' (EVar x) = lookup-elevate2-≡ ρ↝ρ' x
elevate-≡ ρ↝ρ' (ECst x) = refl
elevate-≡ ρ↝ρ' (ESuc e) with elevate-≡ ρ↝ρ' e
... | IA = cong suc IA
elevate-≡ ρ↝ρ' (EIt e e₀ e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₀ | elevate-≡ ρ↝ρ' e₁
... | IA | IA₀ | IA₁ = cong₃ natit IA IA₀ IA₁
elevate-≡ ρ↝ρ' (ERec v u n) with elevate-≡ ρ↝ρ' v | elevate-≡ ρ↝ρ' u | elevate-≡ ρ↝ρ' n 
... | IV | IU | IN = cong₃ natrec IN IV IU
elevate-≡ ρ↝ρ' (EAdd e e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₁
... | IA1 | IA2 = cong₂ _+_ IA1 IA2
elevate-≡ {Γ↝Γ'↝Γ'' = Γ↝Γ'↝Γ''}
              {ρ = ρ}
              {ρ'' = ρ''}
              ρ↝ρ' (ELam e) = ext elevate-≡-body
   where elevate-≡-body : ∀ x → ev e (x ∷ ρ) ≡ ev (elevate (extend Γ↝Γ'↝Γ'') e) (x ∷ ρ'')
         elevate-≡-body x = elevate-≡ (extend ρ↝ρ' x) e
elevate-≡ ρ↝ρ' (EApp e e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₁
... | IA1 | IA2  = cong₂ (λ f₁ x → f₁ x) IA1 IA2
elevate-≡ ρ↝ρ' (EPair e e₁) with elevate-≡ ρ↝ρ' e | elevate-≡ ρ↝ρ' e₁
... | IA1 | IA2  = cong₂ (λ x y → x , y) IA1 IA2
elevate-≡ ρ↝ρ' (EInl e)  = cong inj₁ (elevate-≡ ρ↝ρ' e) 
elevate-≡ ρ↝ρ' (EInr e) with elevate-≡ ρ↝ρ' e
... | IA  = cong (λ x → inj₂ x) IA
elevate-≡ ρ↝ρ' (EFst e) with elevate-≡ ρ↝ρ' e 
... | IA  = cong (λ x → proj₁ x) IA
elevate-≡ ρ↝ρ' (ESnd e) with elevate-≡ ρ↝ρ' e
... | IA  = cong (λ x → proj₂ x) IA
elevate-≡ {ρ = ρ}
              {ρ'' = ρ''}
              ρ↝ρ' (ECase e e₁ e₂) rewrite sym (elevate-≡ ρ↝ρ' e)
                                       with ev e ρ
... | inj₁ x = elevate-≡ (extend ρ↝ρ' x) e₁
... | inj₂ y = elevate-≡ (extend ρ↝ρ' y) e₂ 




int↑-equiv : ∀ {α Γ Γ'} → 
                 {Γ↝Γ' : Γ ↝ Γ'} →
                 (va : ATInt Γ α) (v : TInt (erase α)) →
                 {ρ : Env Γ} {ρ' : Env Γ'} → 
                 Γ↝Γ' ⊢ ρ ↝ ρ' → 
                 Equiv ρ va v →
                 Equiv ρ' (int↑ Γ↝Γ' va) v
int↑-equiv va v {.ρ'} {ρ'} (refl) eq = eq 
int↑-equiv {SNum} va v (extend v₁ ρ↝ρ') eq = eq
int↑-equiv {SFun α α₁} va v (extend v₁ ρ↝ρ') eq = 
  λ v₁ρ₁↝ρ' eq₁ → eq ((extend v₁ ρ↝ρ') ⊕ρ v₁ρ₁↝ρ') eq₁
int↑-equiv {D x} va v (extend {ρ' = ρ'} {Γ↝Γ' = Γ↝Γ'} v₁ ρ↝ρ') eq
  rewrite sym (elevate-≡ (refl (extend {ρ' = ρ'} v₁ refl)) (int↑ Γ↝Γ' va)) | int↑-equiv va v ρ↝ρ' eq
    = refl 
int↑-equiv {SPrd α α₁} (ffst , ssnd) (ffst₁ , ssnd₁) (extend v₁ ρ↝ρ') (x , x₁) =
  (int↑-equiv {α} ffst ffst₁ (extend v₁ ρ↝ρ') x) , (int↑-equiv {α₁} ssnd ssnd₁ (extend v₁ ρ↝ρ') x₁)
int↑-equiv {SSum α α₁} (inj₁ a) (inj₁ a₁) (extend v₁ ρ↝ρ') eq = int↑-equiv  a a₁ (extend v₁ ρ↝ρ') eq
int↑-equiv {SSum α α₁} (inj₂ b) (inj₂ b₁) (extend v₁ ρ↝ρ') eq = int↑-equiv  b b₁ (extend v₁ ρ↝ρ') eq
int↑-equiv {SSum α α₁} (inj₁ a) (inj₂ b) (extend v₁ ρ↝ρ') () 
int↑-equiv {SSum α α₁} (inj₂ b) (inj₁ a) (extend v₁ ρ↝ρ') ()

lookup-equiv : ∀ {α Δ Γ'} → let Γ = Lib.map erase Δ in
                   { aρ : AEnv Γ' Δ } {ρ : Env Γ} →
                   (ρ' : Env Γ') →
                   Env-Equiv ρ' aρ ρ →
                   ∀ x → Equiv {α} ρ' (lookup x aρ ) (lookupE (mapIdx erase x) ρ)
lookup-equiv ρ' [] ()
lookup-equiv ρ' (cons  ρeq va v eq) hd = eq
lookup-equiv ρ' (cons  ρeq va v eq) (tl x) = lookup-equiv ρ' ρeq x

env↑-equiv-extend :
  ∀ {σ Γ' Δ} (ρ' : Env Γ') → let Γ = Lib.map erase Δ in
    {ρ : Env Γ} {aρ : AEnv Γ' Δ} →
    Env-Equiv ρ' aρ ρ → (x : TInt σ) →
    Env-Equiv (x ∷ ρ') (env↑ (extend refl) aρ) ρ
env↑-equiv-extend _ [] x = []
env↑-equiv-extend ρ' (cons {α} eqρ va v x) x₁ =
  cons (env↑-equiv-extend ρ' eqρ x₁)
       (int↑ (extend refl) va) v (int↑-equiv va v (extend x₁ (refl)) x)

env↑-equiv :
  ∀ {Γ' Γ'' Δ} → let Γ = Lib.map erase Δ in
    {Γ↝Γ' : Γ' ↝ Γ''}
    {ρ' : Env Γ'} {ρ'' : Env Γ''}
    (ρ'↝ρ'' : Γ↝Γ' ⊢ ρ' ↝ ρ'') →
    {ρ : Env Γ} {aρ : AEnv Γ' Δ} →
    Env-Equiv ρ' aρ ρ → 
    Env-Equiv ρ'' (env↑ Γ↝Γ' aρ) ρ
env↑-equiv ρ'↝ρ'' [] = []
env↑-equiv {Γ↝Γ' = Γ↝Γ'} ρ'↝ρ'' (cons eqρ va v x)
  with env↑-equiv ρ'↝ρ'' eqρ
... | IA = cons IA (int↑ Γ↝Γ' va) v (int↑-equiv va v ρ'↝ρ'' x)


mutual 
  lift-correct : ∀ {Γ α} (lft : Liftable α) (env : Env Γ) (av : ATInt Γ α) (v : TInt (erase α)) →  
                 Equiv env av v → (Equiv env (lift lft av) v)
  lift-correct (D τ) env av v eq = eq
  lift-correct SCst env av v eq = eq
  lift-correct (SSum lft lft₁) env (inj₁ a) (inj₁ a₁) eq with lift-correct lft env a a₁ 
  ... | IA rewrite IA eq = refl
  lift-correct (SSum lft lft₁) env (inj₂ b) (inj₁ a) ()
  lift-correct (SSum lft lft₁) env (inj₁ a) (inj₂ b) ()
  lift-correct (SSum lft lft₁) env (inj₂ b) (inj₂ b₁) eq with lift-correct lft₁ env b b₁ 
  ... | IA rewrite IA eq = refl
  lift-correct (SPrd lft lft₁) env (ffst , ssnd) (ffst₁ , ssnd₁) (x , x₁) 
    rewrite lift-correct lft env ffst ffst₁ x | lift-correct lft₁ env ssnd ssnd₁ x₁ = refl
  lift-correct (SFun x lft) env av v eq =  
    ext (λ x₁ →
           lift-correct lft (x₁ ∷ env)
           (av (extend refl) (embed x (EVar hd))) (v x₁) (eq (extend x₁ (refl)) (embed-correct x (x₁ ∷ env) (EVar hd) x₁ refl)))

  embed-correct : ∀ {Γ α} (lft : Liftable⁻ α) (env : Env Γ) →  (e : Exp Γ (erase α)) → (v : TInt (erase α)) → 
                  ev e env  ≡ v → Equiv env (embed lft e) v
  embed-correct (D τ) env e v eq rewrite eq = refl
  embed-correct (SPrd lft lft₁) env e (fstv , sndv) eq  =
    (embed-correct lft env (EFst e) fstv (subst (λ x → proj₁ x ≡ fstv) (sym eq) refl)) , (embed-correct lft₁ env (ESnd e) sndv (subst (λ x → proj₂ x ≡ sndv) (sym eq) refl))
  embed-correct {α = SFun α₁ α₂} (SFun x lft) env e v eq = f
    where 
          f : ∀ {Γ' env' Γ↝Γ'} (x₁ : Γ↝Γ' ⊢ env ↝ env') {x₂ : ATInt Γ' α₁} {x₃ : TInt (erase α₁)}
                (x₄ : Equiv env' x₂ x₃) →
                Equiv env'
                (embed lft (EApp (int↑ Γ↝Γ' e) (lift x x₂))) (v x₃)
          f {Γ'} {env'} {Γext} envext {av'} {v'} eq' = 
                                                        embed-correct lft env' (EApp (int↑ Γext e) (lift x av')) (v v') 
                                                          g 
            where g : ev (int↑ Γext e) env' (ev (lift x av') env') ≡ v v'
                  g rewrite lift-correct x env' av' v' eq'  
                          | sym (cong (λ f → f v') (int↑-equiv e v (envext) eq))
                          |  (cong (λ f → f v') eq) = refl 

natit-correct :
          ∀ {Δ} → 
          (n : _) →
          (Γ' : List Type)
          (ρ' : AEnv Γ' Δ) (ρ'' : Env (Lib.map erase Δ))
          (α : _)
          (e₀ : AExp Δ α) (e₁ : AExp Δ (SFun α α))
          (env'  : Env Γ')
          (IA₀ : Equiv env' (pe e₀ ρ') (ev (residualize e₀) ρ'')) →
          (IA₁ : {Γ₁' : List Type} {ρ₁' : Env Γ₁'} {Γ↝Γ' : Γ' ↝ Γ₁'} →
                 Γ↝Γ' ⊢ env' ↝ ρ₁' →
                 {xₐ : ATInt Γ₁' α}
                 {x : TInt (erase α)} →
                 Equiv ρ₁' xₐ x →
                 Equiv ρ₁' (pe e₁ ρ' Γ↝Γ' xₐ) (ev (residualize e₁) ρ'' x)) →
          Equiv env'
          (natit n (pe e₀ ρ') (pe e₁ ρ' refl))
          (natit n (ev (residualize e₀) ρ'') (ev (residualize e₁) ρ''))
natit-correct zero Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ = IA₀
natit-correct (suc n) Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
  with natit-correct n Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
... | IA = IA₁ refl IA



natrec-correct :
          ∀ {Δ} → 
          (n : _) →
          (Γ' : List Type)
          (ρ' : AEnv Γ' Δ) (ρ'' : Env (Lib.map erase Δ))
          (α : _)
          (e₀ : AExp Δ α) (e₁ : AExp Δ (SFun SNum (SFun α α)))
          (env'  : Env Γ')
          (IA₀ : Equiv env' (pe e₀ ρ') (ev (residualize e₀) ρ'')) →
          (IA₁ : {m₁ : _} → {m₂ : _} → m₁ ≡ m₂ → 
                 {Γ₁' : List Type} {ρ₁' : Env Γ₁'} {Γ↝Γ' : Γ' ↝ Γ₁'} →
                 Γ↝Γ' ⊢ env' ↝ ρ₁' →
                 {xₐ : ATInt Γ₁' α}
                 {x : TInt (erase α)} →
                 Equiv ρ₁' xₐ x →
                 Equiv ρ₁' (pe e₁ ρ' Γ↝Γ' m₁ refl xₐ) (ev (residualize e₁) ρ'' m₂  x)) →
          Equiv env'
          (natrec n (pe e₀ ρ') (λ n₁ → pe {Γ'} e₁ ρ' {Γ'} refl n₁ {Γ'} refl))
          (natrec n (ev (residualize e₀) ρ'') (ev (residualize e₁) ρ''))
natrec-correct zero Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ =  IA₀
natrec-correct (suc n) Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
  with natrec-correct n Γ' ρ' ρ'' α e₀ e₁ env' IA₀ IA₁ 
... | IA = IA₁ refl refl IA



pe-correct : ∀ { α Δ Γ' } →
  (e : AExp Δ α) →
  (ρ : Env Γ') →
  {ρ' : AEnv Γ' Δ} → {ρ'' : Env (Lib.map erase Δ)} → 
  Env-Equiv ρ ρ' ρ'' → 
  Equiv ρ (pe e ρ') (ev (residualize e) ρ'')
pe-correct (Var x) env' eqenv = lookup-equiv env' eqenv x
pe-correct (SCst x) env' eqenv = refl
pe-correct (SSuc e) env' eqenv rewrite pe-correct e env' eqenv = refl
pe-correct {Δ = Δ} {Γ' = Γ'} (SIt {α} e e₀ e₁) env' {ρ'} {ρ''} eqenv
  with pe-correct e env' eqenv | pe-correct e₀ env' eqenv | pe-correct e₁ env' eqenv
... | IA | IA₀ | IA₁ rewrite IA = natit-correct (ev (residualize e) ρ'') Γ' ρ' ρ'' α e₀ e₁ env' IA₀
                                    IA₁
pe-correct {Δ = Δ} {Γ' = Γ'} (SRec {α} v u n) env' {ρ'} {ρ''} eqenv 
  with pe-correct n env' eqenv | pe-correct v env' eqenv | pe-correct u env' eqenv 
... | IN | IV | IU rewrite IN = natrec-correct (ev (residualize n) ρ'') Γ' ρ' ρ'' α v u env' IV 
    (λ {m₁} {m₂} m₁≡m₂ {Γ₁'} {ρ₁'} {Γ↝Γ'} Γ↝Γ'⊢env'↝ρ₁' → 
     IU {Γ₁'} {ρ₁'} {Γ↝Γ'} Γ↝Γ'⊢env'↝ρ₁' {m₁} {m₂} m₁≡m₂ {Γ₁'} {ρ₁'}
       {refl} refl)
     


pe-correct (SAdd e e₁) env' eqenv 
  rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
pe-correct (SLam e) env' eqenv = 
 λ {_} {env''} env'↝env'' {av'} {v'} eq →
     let eqenv' : _
         eqenv' = env↑-equiv env'↝env'' eqenv
         eqenv'' : _
         eqenv'' = cons eqenv' av' v' eq
     in pe-correct e env'' eqenv''
pe-correct (SApp e e₁) env' eqenv 
  with pe-correct e env' eqenv | pe-correct e₁ env' eqenv
... | IAe | IAf = IAe (refl) IAf
pe-correct (DCst x) env' eqenv = refl
pe-correct (DSuc e) env' eqenv rewrite pe-correct e env' eqenv = refl
pe-correct (DIt e e₀ e₁) env' eqenv rewrite pe-correct e env' eqenv | pe-correct e₀ env' eqenv | pe-correct e₁ env' eqenv = refl
pe-correct (DRec v u n) env' eqenv rewrite pe-correct n env' eqenv | pe-correct v env' eqenv | pe-correct u env' eqenv = refl
pe-correct (DAdd e e₁) env' eqenv
  rewrite pe-correct e env' eqenv | pe-correct e₁ env' eqenv = refl
pe-correct (DLam e) env' eqenv = 
 ext
  (λ x →
     let eqenv₁ : _
         eqenv₁ = env↑-equiv-extend env' eqenv x
         eqenv₂ : _
         eqenv₂ = cons eqenv₁ (EVar hd) x refl
     in pe-correct e (x ∷ env') eqenv₂)
pe-correct (DApp e e₁) env' eqenv 
  with pe-correct e₁ env' eqenv | pe-correct e env' eqenv
... | IA' | IA = cong₂ (λ f x → f x) IA IA'
pe-correct (SPair e e₁) env' eqenv = (pe-correct e env' eqenv) , (pe-correct e₁ env' eqenv)
pe-correct (SInl e) env' eqenv = pe-correct e env' eqenv
pe-correct (SInr e) env' eqenv = pe-correct e env' eqenv
pe-correct (SFst e) env' {ρ' = aenv} {ρ'' = env} eqenv with pe e aenv | ev (residualize e) env | pe-correct e env' eqenv
... | e₁ , e₂ | e₁' , e₂' |  A , B = A
pe-correct (SSnd e) env' {aenv} {env} eqenv with pe e aenv | ev (residualize e) env | pe-correct e env' eqenv
... | e₁ , e₂ | e₁' , e₂' | A , B = B
pe-correct {α} (SCase e e₁ e₂) env' {aenv} {env} eqenv with pe e aenv | ev (residualize e) env | pe-correct e env' eqenv
... | inj₁ c | inj₁ c' | L = pe-correct e₁ env' (cons eqenv c c' L)
... | inj₂ c | inj₂ c' | R = pe-correct e₂ env' (cons eqenv c c' R)
... | inj₂ c | inj₁ c' | ()
... | inj₁ c | inj₂ c' | ()
pe-correct (DPair e e₁) env' eqenv with pe-correct e env' eqenv | pe-correct e₁ env' eqenv 
... | IA | IA' rewrite IA | IA' = refl
pe-correct (DInl e) env' eqenv with pe-correct e env' eqenv
... | IA rewrite IA = refl
pe-correct (DInr e) env' eqenv with pe-correct e env' eqenv 
... | IA rewrite IA = refl
pe-correct (DFst e) env' eqenv with pe-correct e env' eqenv 
... | IA rewrite IA = refl
pe-correct (DSnd e) env' eqenv with pe-correct e env' eqenv
... | IA rewrite IA = refl
pe-correct (DCase e e₁ e₂) env' {aenv} {env} eqenv with ev (pe e aenv) env' | ev (residualize e) env | pe-correct e env' eqenv
... | inj₁ .c' | inj₁ c' | refl = pe-correct e₁ (c' ∷ env') (cons (env↑-equiv (extend c' (refl)) eqenv) (EVar hd) c' refl)
... | inj₂ .c' | inj₂ c' | refl = pe-correct e₂ (c' ∷ env')
                                    (cons (env↑-equiv (extend c' (refl)) eqenv) (EVar hd) c' refl)
... | inj₁ c | inj₂ c' | ()  
... | inj₂ c | inj₁ c' | ()
pe-correct (Lift x e) env' {aenv} {env} eqenv  
  with pe-correct e env' eqenv 
... | IA = lift-correct x env' (pe e aenv) (ev (residualize e) env) IA 


pe-correct-dyn :
  ∀ { τ } → (e : AExp [] (D τ)) →
  ev (pe e []) [] ≡ (ev (residualize e) [])
pe-correct-dyn e = pe-correct e [] []