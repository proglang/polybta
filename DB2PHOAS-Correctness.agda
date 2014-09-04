--------------------------------------
--correctness proof of the translation
--------------------------------------
module DB2PHOAS-Correctness where

open import Lib
open Auxiliaries
open DB&PHOAS

open import DB2PHOAS
open PE-DB
open PE-PHOAS
open DB→PHOAS

-----------------------------------------------------
--module "DB→PHOAS-Correct"
--note: it includes
--a)[Exp2exp] translation from "base-level"
--  DB terms [Exp] to "base-levl"
--  PHOAS terms [exp];
--b)[similar-exp] equivalence relation
--  between two "universes" of base-level PHOAS
--  terms(terms which are structurally identical);
--c)[Similar] equivalence relation
--  between partial evaluation [PE] of a term 
--  and partial evaluation [pe] of its projection;
--d)[similar-env] equivalence between DB environment 
--  [AEnv] and PHOAS environment [Env];
--e)[project-correct] proof of correctness of
--  the projection [proj] from DB terms to PHOAS terms.
-------------------------------------------------------
module DB→PHOAS-Correct where
  
  ----------------------------------------- 
  --module "Exp2exp"
  --note: 
  --a)given an environment over
  --  base type interpreter [var],
  --  each [Exp] term is translated 
  --  into the corresponding [exp]
  --  term;
  --b)if the term being translated 
  --  is a variable then the corresponding
  --  "target term" can be obtained by
  --  "look-up" in the environment.
  ----------------------------------------    
  module Exp2exp where 
    open import Data.Product
    
    --------------------------------
    --module "auxiliaries"
    --note: some auxiliary functions
    --------------------------------
    module auxiliaries-Exp2exp where
     

      en₁2Ctx : ∀ {var : Type → Set} → (Γ : List (Σ[ A ∈ Type ] (var A))) → Ctx
      en₁2Ctx [] = []
      en₁2Ctx ((proj₁ , proj₂) ∷ en₁) = proj₁ ∷ en₁2Ctx en₁
    
    open auxiliaries-Exp2exp public


    Exp2exp : ∀ {a} {var : Type → Set} → 
              (Γ : List (Σ[ A ∈ Type ] (var A))) →
              Exp (en₁2Ctx Γ) a →
              exp var a 
    Exp2exp [] (EVar ())
    Exp2exp ((proj₁ , proj₂) ∷ Γ) (EVar hd) = EVar proj₂
    Exp2exp ((proj₁ , proj₂) ∷ Γ) (EVar (tl x₁)) = Exp2exp Γ (EVar x₁)
    Exp2exp Γ (ECst x) = ECst x
    Exp2exp Γ (EAdd e e₁) = EAdd (Exp2exp Γ e) (Exp2exp Γ e₁)
    Exp2exp {Fun A B} {var} Γ (ELam e) = ELam (λ v → Exp2exp {B} ((A , v) ∷ Γ) e)
    Exp2exp Γ (EApp e e₁) = EApp (Exp2exp Γ e) (Exp2exp Γ e₁)

    -------------------------------------------
    --module "Exp2exp-≡"
    --note: some equalities involving [Exp2exp]
    ------------------------------------------- 
    module Exp2exp-≡ where
     
      Exp2expELam≡ : ∀ {A B var Γ} {e : Exp (A ∷ en₁2Ctx Γ) B} →
                        Exp2exp {Fun A B} {var} Γ (ELam e) ≡ ELam (λ v → Exp2exp {B} ((A , v) ∷ Γ) e)
      Exp2expELam≡ {A} {B} {var} {[]} = λ {e} → refl
      Exp2expELam≡ {A} {B} {var} {x ∷ Γ} = λ {e} → refl 

      Exp2expEApp≡ : ∀ {A B var Γ} {f : Exp (en₁2Ctx Γ) (Fun A B)} {e : Exp (en₁2Ctx Γ) A} →
                        Exp2exp {B} {var} Γ (EApp f e) ≡ EApp (Exp2exp Γ f) (Exp2exp Γ e)
      Exp2expEApp≡ {A} {B} {var} {[]} {f} {e} = refl
      Exp2expEApp≡ {A} {B} {var} {x ∷ Γ} {f} {e} = refl 
      
      Exp2exp-EInt≡ : ∀ {n} {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} → 
                         Exp2exp Γ (ECst n) ≡ ECst n
      Exp2exp-EInt≡ {n} {var} {[]} = refl
      Exp2exp-EInt≡ {n} {var} {x ∷ Γ} = refl

      Exp2exp-EAdd≡ : ∀ {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} {e e₁} → 
                         Exp2exp Γ (EAdd e e₁) ≡ EAdd (Exp2exp Γ e) (Exp2exp Γ e₁)
      Exp2exp-EAdd≡ {var} {[]} {e} {e₁} = refl
      Exp2exp-EAdd≡ {var} {x ∷ Γ} = refl

      Exp2exp-ELam≡ : ∀ {A B} {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} {e} →
                         Exp2exp {Fun A B} {var} Γ (ELam e) ≡ ELam (λ v → Exp2exp {B} ((A , v) ∷ Γ) e)
      Exp2exp-ELam≡ {A} {B} {var} {[]} {e} = refl
      Exp2exp-ELam≡ {A} {B} {var} {x ∷ Γ} = refl

      Exp2exp-EApp≡ : ∀ {A B} {var : Type → Set} {Γ : List (Σ[ A ∈ Type ] (var A))} {f} {v} →
                         Exp2exp {B} {var} Γ (EApp {τ = A} f v) ≡ EApp (Exp2exp Γ f) (Exp2exp Γ v)
      Exp2exp-EApp≡ {A} {B} {var} {[]} {f} {v}= refl
      Exp2exp-EApp≡ {A} {B} {var} {x ∷ Γ} = refl

      data _⊂_ {A : Set} : List A → List A → Set where
        extend-hd  : ∀ {Γ Γ'} → Γ ↝ Γ' → Γ ⊂ Γ'
        extend-mid : ∀ {Γ Γ' τ} → Γ ⊂ Γ' → (τ ∷ Γ) ⊂ (τ ∷ Γ')
   
      etG2S' : ∀ {var : Type → Set} 
                {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ' : List (Σ[ A ∈ Type ] (var A))} →
                 Γ ↝ Γ' →
                 en₁2Ctx Γ ↝ en₁2Ctx Γ'
      etG2S' refl = refl
      etG2S' (extend etG) = extend (etG2S' etG)
    
      ⊂2↝ : ∀  {var : Type → Set}
               {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ'' : List (Σ[ A ∈ Type ] (var A))} → 
                Γ ⊂ Γ'' → Σ Ctx (λ Γ' → en₁2Ctx {var} Γ ↝ Γ' ↝ en₁2Ctx {var} Γ'') 
      ⊂2↝ (extend-hd x) = [] , refl (etG2S' x)
      ⊂2↝ (extend-mid {τ = (a , v)} Γ⊂Γ'') = (a ∷ proj₁ (⊂2↝ Γ⊂Γ'')) , extend (proj₂ (⊂2↝ Γ⊂Γ''))

      
      postulate
        ext : ∀ {A B : Set} {f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g


      lemmaExp2exp≡ : ∀ {τ τ'} {var : Type → Set} {v : var τ}
                        {Γ : List (Σ[ A ∈ Type ] (var A))} {Γ' : List (Σ[ A ∈ Type ] (var A))}
                        {et : Γ ⊂ Γ'}
                        {e : Exp (τ ∷ en₁2Ctx Γ) τ'} →
                         Exp2exp ((τ , v) ∷ Γ) e ≡ Exp2exp ((τ , v) ∷ Γ') (elevate (extend (proj₂ (⊂2↝ {var} {Γ} {Γ'} et))) e)
      lemmaExp2exp≡ {τ} {.τ} {var} {v} {Γ} {Γ'} {extend-hd x} {EVar hd} = refl
      lemmaExp2exp≡ {τ} {τ'} {var} {v} {.Γ'} {Γ'} {extend-hd refl} {EVar (tl x₁)} = refl
      lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {τ₁ ∷ Γ'} {extend-hd (extend x)} {EVar (tl x₁)} 
            = lemmaExp2exp≡ {τ} {τ'} {var} {v} {Γ} {Γ'} {extend-hd x} {EVar (tl x₁)}
      lemmaExp2exp≡ {τ} {.τ} {var} {v} {τ₁ ∷ Γ} {.τ₁ ∷ Γ'} {extend-mid et} {EVar hd} = refl
      lemmaExp2exp≡ {τ} {τ'} {var} {v} {τ₁ ∷ Γ} {.τ₁ ∷ Γ'} {extend-mid et} {EVar (tl x)} 
            = lemmaExp2exp≡ {proj₁ τ₁} {τ'} {var} {proj₂ τ₁} {Γ} {Γ'} {et} {EVar x}
      lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {ECst x} = refl
      lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {EAdd e e₁} 
              rewrite lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {e} |
                      lemmaExp2exp≡ {τ} {Num} {var} {v} {Γ} {Γ'} {et} {e₁}
            = refl
      lemmaExp2exp≡ {τ} {(Fun τ₁ τ')} {var} {v} {Γ} {Γ'} {et} {ELam e} 
            = cong ELam
                   (ext {var τ₁} {exp var τ'}
                   {λ v₁ → Exp2exp ((τ₁ , v₁) ∷ (τ , v) ∷ Γ) e}
                   {λ v₁ →
                        Exp2exp ((τ₁ , v₁) ∷ (τ , v) ∷ Γ')
                        (elevate (extend (extend (proj₂ (⊂2↝ et)))) e)}
                   (λ v₁ →
                        lemmaExp2exp≡ {τ₁} {τ'} {var} {v₁} {(τ , v) ∷ Γ} {(τ , v) ∷ Γ'}
                        {extend-mid {τ = τ , v} et} {e}))
      lemmaExp2exp≡ {τ} {B} {var} {v} {Γ} {Γ'} {et} {EApp {τ = A} e e₁} 
              rewrite lemmaExp2exp≡ {τ} {Fun A B} {var} {v} {Γ} {Γ'} {et} {e} |
                      lemmaExp2exp≡ {τ} {A} {var} {v} {Γ} {Γ'} {et} {e₁}  
            = refl

      
    open Exp2exp-≡ public 
 
  

  --------------------------------------
  --module "similar-exp"
  --note: equivalence between two
  --      base-level PHOAS terms
  --      of two different universes
  --a)they are structurally equivalent;
  --b)each corresponding pair of "holes"
  --  are "registered" as equivalent 
  --  (by a corresponding "environment"
  --  , a list of pairs of interpretation
  --  of holes).
  --------------------------------------
  module Similar-exp where
    open import Data.Product
    
    data similar-exp {var₁ var₂} (Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A))))
         : ∀ {A} → exp var₁ A → exp var₂ A → Set where
      similar-EVar  : ∀ {A x₁ x₂} → (A , x₁ , x₂) ∈ Γ → similar-exp Γ (EVar x₁) (EVar x₂)
      similar-ECst  : ∀ {n} → similar-exp Γ (ECst n) (ECst n)
      similar-EAdd  : ∀ {a₁ a₂ b₁ b₂} → similar-exp Γ a₁ b₁ → similar-exp Γ a₂ b₂ → similar-exp Γ (EAdd a₁ a₂) (EAdd b₁ b₂)
      similar-ELam  : ∀ {A B} {f₁ : var₁ A → exp var₁ B} {f₂ : var₂ A → exp var₂ B} →
                        (∀ (v₁ : var₁ A) → (v₂ : var₂ A) → similar-exp ((A , v₁ , v₂) ∷ Γ) (f₁ v₁) (f₂ v₂) ) →
                        similar-exp Γ (ELam f₁) (ELam f₂)
      similar-EApp  : ∀ {A B} {f₁ : exp var₁ (Fun A B)} {f₂ : exp var₂ (Fun A B)} {a₁ : exp var₁ A} {a₂ : exp var₂ A} →
                      similar-exp Γ f₁ f₂ → similar-exp Γ a₁ a₂ →
                      similar-exp Γ (EApp f₁ a₁) (EApp f₂ a₂)
  
  open Similar-exp public
  
  ------------------------------------
  --module "similar"
  --note:[Similar] specifying the
  --     equivalence relation between
  --     partial evaluation [PE] and
  --     [pe] of terms of the same
  --     type
  -------------------------------------
  module similar where
    open Exp2exp 
    open Similar-exp
    open import Data.Product

    module auxiliaries-similar where
     
      Γ2en₁ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} → (Γ : List (Σ[ A ∈ Type ] (var₁ A × var₂ A))) → List (Σ[ A ∈ Type ] (var₁ A))
      Γ2en₁ [] = []
      Γ2en₁ ((proj₁ , proj₂ , proj₃) ∷ Γ) = (proj₁ , proj₂) ∷ Γ2en₁ Γ 

      etG2S : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
              {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
              Γ ↝ Γ' →
              en₁2Ctx (Γ2en₁ Γ) ↝ en₁2Ctx (Γ2en₁ Γ')
      etG2S refl = refl
      etG2S (extend etG) = extend (etG2S etG)

      -----------------------------------
      --module "etG2S-≡" 
      --note: equalites involving [etG2S]
      -----------------------------------
      module etG2S-≡ where
          
         etG2S'' : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
                     {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
                      Γ ↝ Γ' →
                      Γ2en₁ Γ ↝ Γ2en₁ Γ'
         etG2S'' refl = refl
         etG2S'' (extend etG) = extend (etG2S'' etG)

         etG2S≡ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
                    {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                    {et : Γ ↝ Γ'} → 
                     etG2S et ≡  etG2S' (etG2S'' et)
         etG2S≡ {var₁} {var₂} {.Γ'} {Γ'} {refl} = refl
         etG2S≡ {var₁} {var₂} {Γ} {(τ ∷ Γ')} {extend et} = cong extend this 
                  where this : (etG2S et) ≡ (etG2S' (etG2S'' et))
                        this  rewrite etG2S≡ {var₁} {var₂} {Γ} {Γ'} {et} = refl

         etG2S-trans≡ : ∀ {var₁ : Type → Set} {var₂ : Type → Set} 
                          {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                          {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                          {Γ'' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                          {et : Γ ↝ Γ'} {et₁ : Γ' ↝ Γ''} →
                           lem-↝-trans (etG2S et) (etG2S et₁) ≡ etG2S (lem-↝-trans et et₁)
         etG2S-trans≡ {var₁} {var₂} {Γ} {.Γ''} {Γ''} {et} {refl} = refl
         etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {(τ ∷ Γ'')} {et} {extend et₁}  = cong extend this
                  where this : (lem-↝-trans (etG2S et) (etG2S et₁)) ≡ (etG2S (lem-↝-trans et et₁))
                        this rewrite etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {Γ''} {et} {et₁} = refl 
      
      open etG2S-≡ public
    
    open auxiliaries-similar public
      
    
    Similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set}  → (Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))) → ATInt (en₁2Ctx (Γ2en₁ Γ)) A → 
                atint var₂ A → Set
    Similar {SNum} Γ e e' = e ≡ e'
    Similar {SFun A A₁} {var₁} {var₂} Γ e e' = {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {v : ATInt (en₁2Ctx (Γ2en₁ {var₁} {var₂} Γ')) A} 
                                               {v' : atint var₂ A} →
                                               (et : Γ ↝ Γ') →
                                               Similar Γ' v v' → Similar Γ' (e (etG2S et) v) (e' v')
    Similar {D x} Γ e e' = similar-exp Γ (Exp2exp (Γ2en₁ Γ) e) e'

    
 
  -----------------------------------
  --module "similar-env"
  --note:[similar-env] specify the
  --     equivalence relation between
  --     two environments [AEnv] and 
  --     [Env] based upon [Similar].
  -----------------------------------
  module Similar-env where
    open Exp2exp
    open similar
    open import Data.Product
 
    data similar-env {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
        : ∀ {Δ : ACtx} → AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ → Env var₂ Δ → Set₁ where
      []    : similar-env [] [] 
      scons  : ∀ {A : AType} {Δ : ACtx} {e : ATInt (en₁2Ctx (Γ2en₁ Γ)) A} {e' : atint var₂ A} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} {en : Env var₂ Δ} 
                  → Similar Γ e e'  → similar-env {var₁} {var₂} {Γ} {Δ} aen en → similar-env (cons e aen) (cons e' en)
  
  
    
    

  module Project-correct where
    open Exp2exp
    open Similar-exp
    open similar
    open Similar-env
 
    --------------------------------------------
    --module "auxiliaries-correct"
    --note: some helpers for [proj-correct]
    --a)[lift-similar] equivalence between
    --  partial evaluation results holds
    --  under "lifting";
    --b)[lift-similar-env] equivalence between
    --  envirionments hold under "lifting";
    --c)[ similar-Exp2Similar-Embed] helper
    --  for [proj-correct] in case of liftable
    --  terms
    ---------------------------------------------
    module auxiliaries-correct where

      module Lift-similar where
        open import Data.Product
        
    
        
        --------------------------------------
        --module "auxiliaries-Lift-similar"
        --note: auxiliaries for [lift-similar]
        --------------------------------------
        module auxiliaries-Lift-similar where
          open import Data.Product
       
          lemma1≡ :  ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} 
                      {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                      {et : Γ ↝ Γ'} 
                      {e : Exp (en₁2Ctx (Γ2en₁ Γ)) A} →
                       Exp2exp (Γ2en₁ Γ) e ≡ Exp2exp (Γ2en₁ Γ') (elevate (refl (etG2S et)) e)
          lemma1≡ {A} {var₁} {var₂} {.Γ'} {Γ'} {refl} {EVar x} = refl
          lemma1≡ {A} {var₁} {var₂} {Γ} {τ ∷ Γ'} {extend et} {EVar x} = lemma1≡ {A} {var₁} {var₂} {Γ} {Γ'} {et} {EVar x}
          lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {ECst x} 
              rewrite Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ} | Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ'}
            = refl
          lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {EAdd e e₁}
              rewrite     Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ} {e} {e₁} | 
                          Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ'} {elevate (refl (etG2S et)) e} {elevate (refl (etG2S et)) e₁} |
                          lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {e} |
                          lemma1≡ {Num} {var₁} {var₂} {Γ} {Γ'} {et} {e₁}
            = refl
          lemma1≡ {(Fun τ τ')} {var₁} {var₂} {Γ} {Γ'} {et} {ELam e} 
              rewrite     Exp2exp-ELam≡ {τ} {τ'} {var₁} {Γ2en₁ Γ} {e} | 
                          Exp2exp-ELam≡ {τ} {τ'} {var₁} {Γ2en₁ Γ'} {elevate (extend (refl (etG2S et))) e} 
            =   cong ELam
                 (ext {var₁ τ} {exp var₁ τ'} {λ v → Exp2exp ((τ , v) ∷ Γ2en₁ Γ) e}
                      {λ v →
                         Exp2exp ((τ , v) ∷ Γ2en₁ Γ')
                         (elevate (extend (refl (etG2S et))) e)}
                         (λ v → this {v}))
                               where   this : ∀ {v} → Exp2exp ((τ , v) ∷ Γ2en₁ Γ) e ≡
                                              Exp2exp ((τ , v) ∷ Γ2en₁ Γ')
                                                      (elevate (extend (refl (etG2S et))) e)
                                       this {v} rewrite etG2S≡ {var₁} {var₂} {Γ} {Γ'} {et}
                                            = lemmaExp2exp≡ {τ} {τ'} {var₁} {v} {Γ2en₁ Γ} {Γ2en₁ Γ'} {extend-hd (etG2S'' et)} {e}
          lemma1≡ {B} {var₁} {var₂} {Γ} {Γ'} {et} {EApp {τ = A} e e₁} 
             rewrite Exp2exp-EApp≡ {A} {B} {var₁} {Γ2en₁ Γ} {e} {e₁} |
                     Exp2exp-EApp≡ {A} {B} {var₁} {Γ2en₁ Γ'} {elevate (refl (etG2S et)) e} {elevate (refl (etG2S et)) e₁} |
                     lemma1≡ {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {e} |
                     lemma1≡ {A} {var₁} {var₂} {Γ} {Γ'} {et} {e₁}
            = refl 

          id-extend : ∀ {A : Set} {a : A} {b : A} {Γ : List A} → a ∈ Γ → a ∈ (b ∷ Γ)
          id-extend hd = tl hd
          id-extend (tl a∈Γ) = tl (tl a∈Γ)


          lemma2-EVar : ∀ {var₁ : Type → Set} {var₂ : Type → Set} {a}
                     {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} →
                     Γ ⊂ Γ' →
                     a ∈ Γ →
                     a ∈ Γ'
          lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-hd refl) a∈Γ = a∈Γ
          lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-hd (extend x)) a∈Γ = id-extend (lemma2-EVar (extend-hd x) a∈Γ)
          lemma2-EVar {var₁} {var₂} {.proj₁ , .proj₂ , .proj₃} (extend-mid {Γ} {Γ'} {proj₁ , proj₂ , proj₃} Γ⊂Γ') hd = hd
          lemma2-EVar {var₁} {var₂} {A , x₁ , x₂} (extend-mid {Γ} {Γ'} {proj₁ , proj₂ , proj₃} Γ⊂Γ') (tl a∈Γ) = tl (lemma2-EVar Γ⊂Γ' a∈Γ)


          lemma2  : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} 
                      {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                      {et : Γ ⊂ Γ'}
                      {e : exp var₁ A} {e' : exp var₂ A} →
                       similar-exp Γ e e' →
                       similar-exp Γ' e e' 
          lemma2 {A} {var₁} {var₂} {Γ} {Γ'} {et} {EVar x₁} {EVar x₂} (similar-EVar x) = similar-EVar (lemma2-EVar et x)
          lemma2 similar-ECst = similar-ECst
          lemma2 {Num} {var₁} {var₂} {Γ} {Γ'} {et} {EAdd a₁ a₂} {EAdd b₁ b₂} (similar-EAdd sim sim₁) 
             = similar-EAdd (lemma2 {Num} {var₁} {var₂} {Γ} {Γ'} {et} {a₁} {b₁} sim) 
                            (lemma2 {Num} {var₁} {var₂} {Γ} {Γ'} {et} {a₂} {b₂} sim₁) 
          lemma2 {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {ELam f₁} {ELam f₂} (similar-ELam sim) 
             = similar-ELam {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} (λ v₁ v₂ →
                                                            lemma2 {B} {var₁} {var₂} {(A , v₁ , v₂) ∷ Γ} {(A , v₁ , v₂) ∷ Γ'}
                                                            {extend-mid et} (sim v₁ v₂))
          lemma2 {B} {var₁} {var₂} {Γ} {Γ'} {et} {EApp {A}  f₁ a₁} {EApp {.A} f₂ a₂} (similar-EApp sim sim₁) 
             = similar-EApp (lemma2 {Fun A B} {var₁} {var₂} {Γ} {Γ'} {et} {f₁} {f₂} sim) 
                            (lemma2 {A} {var₁} {var₂} {Γ} {Γ'} {et} {a₁} {a₂} sim₁) 


        open auxiliaries-Lift-similar public

        lift-similar : ∀ {A var₁ var₂} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                      {et : Γ ↝ Γ'} {e : ATInt (en₁2Ctx (Γ2en₁ Γ)) A} {e' : atint var₂ A} →  
                      Similar {A} {var₁} {var₂} Γ e e' → 
                      Similar {A} {var₁} {var₂} Γ' (int↑ A (etG2S et) e) e'
        lift-similar {SNum} sim = sim
        lift-similar {SFun A A₁} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} sim 
             = λ {Γ''} {v} {v'} et₁ simvv' → this {Γ''} {v} {v'} et₁ simvv'
                   where this : ∀ {Γ''} {v} {v'} et₁ simvv' → Similar Γ'' (e (lem-↝-trans (etG2S et) (etG2S et₁)) v) (e' v')
                         this {Γ''} {v} {v'} et₁ simvv' rewrite etG2S-trans≡ {var₁} {var₂} {Γ} {Γ'} {Γ''} {et} {et₁}
                                = sim {Γ''} {v} {v'} (lem-↝-trans et et₁) simvv'
        lift-similar {D x} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} sim rewrite lemma1≡ {x} {var₁} {var₂} {Γ} {Γ'} {et} {e} 
             = lemma2 {x} {var₁} {var₂} {Γ} {Γ'} {extend-hd et} {Exp2exp (Γ2en₁ Γ') (elevate (refl (etG2S et)) e)} {e'} sim

      open Lift-similar public

   
      module Lift-similar-env where
        open import Data.Product

        lift-similar-env : ∀ {Δ var₁ var₂} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {Γ' : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} 
                          {et : Γ ↝ Γ'} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} {en : Env var₂ Δ} →
                           similar-env {var₁} {var₂} {Γ} {Δ} aen en → 
                           similar-env {var₁} {var₂} {Γ'} {Δ} (env↑ (etG2S et) aen) en 
        lift-similar-env [] = []
        lift-similar-env {A ∷ Δ} {var₁} {var₂} {Γ} {Γ'} {et} {cons e aen} {cons e' en}  (scons x sim) 
             = scons (lift-similar {A} {var₁} {var₂} {Γ} {Γ'} {et} {e} {e'} x) 
                     (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim) 
     
      open Lift-similar-env public

      module helper-↑ where
        open import Data.Product

        mutual
          similar-Exp2Similar-Embed : ∀ {α} {l : liftable1 α}
                                     {var₁ : Type → Set} {var₂ : Type → Set} 
                                     {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))}
                                     {e : Exp (en₁2Ctx (Γ2en₁ Γ)) (typeof α)} {e' : exp var₂ (typeof α)} →
                                     similar-exp Γ (Exp2exp (Γ2en₁ Γ) e) e' →
                                     Similar Γ (Embed l e) (embed l e')
          similar-Exp2Similar-Embed {SNum} {()} sim
          similar-Exp2Similar-Embed {SFun α α₁} {Func l l₁} {var₁} {var₂} {Γ} {e} {e'} sim 
               = λ {Γ'} {v} {v'} et simvv' →
                   similar-Exp2Similar-Embed {α₁} {l₁} {var₁} {var₂} {Γ'}
                   {EApp (elevate (refl (etG2S et)) e) (Lift l v)}
                   {EApp e' (lift l v')} (that {Γ'} {et} {v} {v'} {simvv'})   
                        where that : ∀ {Γ'} {et : Γ ↝ Γ'} {v} {v'} {simvv' : Similar Γ' v v'} →       
                                     similar-exp Γ'
                                     (Exp2exp (Γ2en₁ Γ') (EApp (elevate (refl (etG2S et)) e) (Lift l v)))
                                      (EApp e' (lift l v'))
                              that {Γ'} {et} {v} {v'} {simvv'}
                                   rewrite Exp2exp-EApp≡ {typeof α} {typeof α₁} {var₁} {Γ2en₁ Γ'} {elevate (refl (etG2S et)) e} {Lift l v}
                                     = similar-EApp (this {Γ'} {et})
                                        (Lift-Similar {α} {var₁} {var₂} {Γ'} {l} {v} {v'} simvv') 
                                         where
                                           this : ∀ {Γ'} {et : Γ ↝ Γ'} → similar-exp Γ' (Exp2exp (Γ2en₁ Γ') (elevate (refl (etG2S et)) e)) e'
                                           this {Γ'} {et}
                                              rewrite sym (lemma1≡ {Fun (typeof α) (typeof α₁)} {var₁} {var₂} {Γ} {Γ'} {et} {e})
                                               = lemma2 {Fun (typeof α) (typeof α₁)} {var₁} {var₂} {Γ} {Γ'}
                                                        {extend-hd et} {Exp2exp (Γ2en₁ Γ) e} {e'} sim 
          similar-Exp2Similar-Embed {D x} {base} sim = sim

          Lift-Similar : ∀ {A} {var₁ : Type → Set} {var₂ : Type → Set} {Γ : List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {l : liftable1 A} 
                        {v : ATInt (en₁2Ctx (Γ2en₁ Γ)) A} {v' : atint var₂ A} →
                         Similar Γ v v' →
                         similar-exp Γ (Exp2exp (Γ2en₁ Γ) (Lift l v)) (lift l v')
          Lift-Similar {(D x)} {var₁} {var₂} {Γ} {base} sim = sim
          Lift-Similar {(SFun α₁ α₂)} {var₁} {var₂} {Γ} {Func l l₁} {v} {v'} sim 
                    rewrite Exp2expELam≡ {typeof α₁} {typeof α₂} {var₁} {Γ2en₁ Γ} {Lift l₁ (v (extend refl) (Embed l (EVar hd)))}
                = similar-ELam (λ v₁ v₂ →
                                Lift-Similar {α₂} {var₁} {var₂} {(typeof α₁ , v₁ , v₂) ∷ Γ} {l₁}
                               {v (extend refl) (Embed l (EVar hd))} {v' (embed l (EVar v₂))}
                               (sim {(typeof α₁ , v₁ , v₂) ∷ Γ} {Embed l (EVar hd)}
                               {embed l (EVar v₂)} (extend refl)
                               (similar-Exp2Similar-Embed {α₁} {l} {var₁} {var₂}
                               {(typeof α₁ , v₁ , v₂) ∷ Γ} {EVar hd} {EVar v₂} (this {v₁} {v₂}))))
                                  where this : ∀ {v₁} {v₂} → similar-exp ((typeof α₁ , v₁ , v₂) ∷ Γ) (Exp2exp (Γ2en₁ ((typeof α₁ , v₁ , v₂) ∷ Γ)) (EVar hd)) (EVar v₂)
                                        this {v₁} {v₂} = similar-EVar hd 
       
      open helper-↑ public

      --------------------------------
      --module "proof"
      --note: the correctness proof
      --      of the projection [proj]
      --      from DB terms to PHOAS 
      --      terms.
      --------------------------------
      module proof where
        open import Data.Product
        
        proj-correct : ∀ {Δ A var₁ var₂} {Γ :  List (Σ[ A ∈ Type ] ((var₁ A) × (var₂ A)))} {e : AExp Δ A} {aen : AEnv (en₁2Ctx (Γ2en₁ Γ)) Δ} 
                      {en : Env var₂ Δ} →
                      similar-env {var₁} {var₂} {Γ} {Δ} aen en → 
                      let e' = proj e en in
                      Similar {A} {var₁} {var₂} Γ (PE e aen) (pe e')
        proj-correct {[]} {A} {var₁} {var₂} {Γ} {Var ()} []
        proj-correct {A₁ ∷ Δ} {.A₁} {var₁} {var₂} {Γ} {Var hd} (scons x₁ sim) = x₁
        proj-correct {A₁ ∷ Δ} {A} {var₁} {var₂} {Γ} {Var (tl x)} (scons x₁ sim) 
                   = proj-correct {Δ} {A} {var₁} {var₂} {Γ} {Var x} sim
        proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {SCst x} sim = refl
        proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {SAdd e e₁} sim 
           rewrite proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {e} sim | proj-correct {Δ} {SNum} {var₁} {var₂} {Γ} {e₁} sim
                   = refl
        proj-correct {Δ} {(SFun α₁ α₂)} {var₁} {var₂} {Γ} {SLam e} {aen} {en} sim 
                   = λ {Γ'} {v} {v'} et simvv' →
                       proj-correct {α₁ ∷ Δ} {α₂} {var₁} {var₂} {Γ'} {e}
                       {cons v (env↑ (etG2S et) aen)} {cons v' en}
                       (scons {A = α₁} {Δ = Δ} {e = v} {e' = v'}
                       {aen = env↑ (etG2S et) aen} {en = en} simvv'
                        (lift-similar-env {Δ} {var₁} {var₂} {Γ} {Γ'} {et} {aen} {en} sim))
        proj-correct {Δ} {B} {var₁} {var₂} {Γ} {SApp {α₂ = A} e e₁} {aen} {en} sim 
                   = proj-correct {Δ} {SFun A B} {var₁} {var₂} {Γ} {e} {aen} {en} sim
                     {Γ} {PE e₁ aen} {pe (proj e₁ en)} refl
                     (proj-correct {Δ} {A} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
        proj-correct {Δ} {(D Num)} {var₁} {var₂} {Γ} {DCst x} sim 
           rewrite Exp2exp-EInt≡ {x} {var₁} {Γ2en₁ Γ}
                   = similar-ECst
        proj-correct {Δ} {(D Num)} {var₁} {var₂} {Γ} {DAdd e e₁} {aen} {en} sim 
           rewrite Exp2exp-EAdd≡ {var₁} {Γ2en₁ Γ} {PE e aen} {PE e₁ aen}
                   = similar-EAdd (proj-correct {Δ} {D Num} {var₁} {var₂} {Γ} {e} {aen} {en} sim) 
                     (proj-correct {Δ} {D Num} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
        proj-correct {Δ} {(D (Fun τ₁ τ₂))} {var₁} {var₂} {Γ} {DLam e} {aen} {en} sim 
           rewrite Exp2exp-ELam≡ {τ₁} {τ₂} {var₁} {Γ2en₁ Γ} {PE e (cons (EVar hd) (env↑ (extend refl) aen))}
                   = similar-ELam {A = τ₁} {B = τ₂} 
                     {f₁ = λ v → Exp2exp ((τ₁ , v) ∷ Γ2en₁ Γ)(PE e (cons (EVar hd) (env↑ (extend refl) aen)))} 
                     {f₂ = λ v → pe (proj e (cons (EVar v) en))}  
                     (λ v₁ v₂ →
                      proj-correct {D τ₁ ∷ Δ} {D τ₂} {var₁} {var₂} {(τ₁ , v₁ , v₂) ∷ Γ}
                     {e} {cons (EVar hd) (env↑ (extend refl) aen)}
                     {cons (EVar v₂) en} (this {v₁} {v₂}))
                         where this : ∀ {v₁} {v₂} → similar-env (cons (EVar hd) (env↑ (extend refl) aen)) (cons (EVar v₂) en)
                               this {v₁} {v₂} = scons (similar-EVar hd) (lift-similar-env sim)
        proj-correct {Δ} {(D τ₁)} {var₁} {var₂} {Γ} {DApp {τ₂ = τ₂} e e₁} {aen} {en} sim 
                  rewrite Exp2exp-EApp≡ {τ₂} {τ₁} {var₁} {Γ2en₁ Γ} {PE e aen} {PE e₁ aen}
                   = similar-EApp (proj-correct {Δ} {D (Fun τ₂ τ₁)} {var₁} {var₂} {Γ} {e} {aen} {en} sim) 
                                  (proj-correct {Δ} {D τ₂} {var₁} {var₂} {Γ} {e₁} {aen} {en} sim)
        proj-correct {Δ} {.(D (typeof α))} {var₁} {var₂} {Γ} {e = ↑ {α} l e} {aen} {en} sim 
                   = Lift-Similar {α} {var₁} {var₂} {Γ} {l} {PE e aen} {pe (proj e en)}
                                  (proj-correct {e = e} sim)
