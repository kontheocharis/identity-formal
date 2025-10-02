module Model where

open import Data.Nat hiding (_^_)
open import Data.Fin
open import Data.Unit
open import Data.Maybe
open import Data.Product hiding (∃)


data ∃ (A : Set) (P : A → Prop) : Prop where
  _,_ : (x : A) → P x → ∃ A P
  
data _AND_ (P Q : Prop) : Prop where
  _,_ : P → Q → P AND Q
  
data _＝_ {A : Set} (x : A) : A → Prop where
  refl : x ＝ x
  
syntax ∃ A (λ x → P) = ∃[ x ∈ A ] P

record Model : Set2 where
  field
    -- Logical
    ConL : Set1
    SubL : ConL → ConL → Set
    TyL : ConL → Set1
    TmL : ∀ ΓL → TyL ΓL → Set
    
    -- Computational
    ConC : Set
    ∙C : ConC
    SubC : ConC → ConC → Set
    TmC : ConC → Set
    _[p*] : ∀ {ΓC} → TmC ∙C → TmC ΓC
    
    -- Total
    Con : ConL → ConC → Set1
    Sub : ∀ {ΓL ΔL ΓC ΔC} → Con ΓL ΓC → Con ΔL ΔC → SubL ΓL ΔL → SubC ΓC ΔC → Set
    Ty : ∀ ΓL → TyL ΓL → Set1
    Tm : ∀ {ΓL ΓC TL} → Con ΓL ΓC → Ty ΓL TL → TmL ΓL TL → TmC ΓC → Set
    
    -- Specialization types
    Spec : ∀ {ΓL TL} → Ty ΓL TL → TmC ∙C → Ty ΓL TL
    spec : ∀ {ΓL ΓC TL Γ T aL aC} → Tm {ΓL} {ΓC} {TL} Γ T aL (aC [p*]) → Tm Γ (Spec T aC) aL (aC [p*])
    unspec : ∀ {ΓL ΓC TL Γ T aL aC aC'} → Tm {ΓL} {ΓC} {TL} Γ (Spec T aC) aL aC' → Tm Γ T aL (aC [p*])
    

record PCA : Set1 where
  field
    ∣_∣ : Set
    app : ∣_∣ → ∣_∣ → Maybe ∣_∣
    S K : ∣_∣

variable
  A : PCA
  m n k : ℕ
  
module PCAWithVars where
  open PCA public

  ∣_∣? : PCA → Set
  ∣ A ∣? = Maybe (∣ A ∣)
      
  data ∣_[_]∣ (A : PCA) : ℕ → Set where
    var : Fin n → ∣ A [ n ]∣
    lit : ∣ A ∣ → ∣ A [ n ]∣
    app' : ∣ A [ n ]∣ → ∣ A [ n ]∣ → ∣ A [ n ]∣
    
  eval : ∣ A [ n ]∣ → (Fin n → ∣ A ∣?) → ∣ A ∣?
  eval (var x) σ = σ x
  eval (lit x) σ = just x
  eval {A = A} (app' a b) σ with eval a σ | eval b σ
  ... | just f | just x = app A f x
  ... | _ | _ = nothing
  
  ∣_[_]∣^_ : (A : PCA) → ℕ → ℕ → Set
  ∣ A [ k ]∣^ l = Fin l → ∣ A [ k ]∣

  ∣_∣^_ : (A : PCA) → ℕ → Set
  ∣ A ∣^ l = Fin l → ∣ A ∣
  
  wk : (n : ℕ) → ∣ A [ n ]∣ → ∣ A [ suc n ]∣
  wk n (var x) = var (suc x)
  wk n (lit x) = lit x
  wk n (app' a b) = app' (wk n a) (wk n b)
  
  extract : ∣ A [ zero ]∣ → ∣ A ∣?

  opn : (n : ℕ) → ∣ A [ zero ]∣ → ∣ A [ n ]∣
  opn zero x = x
  opn (suc n) x = wk n (opn n x)

module PCACombinators (A : PCA) where
  open PCAWithVars
  
  -- @@TODO
  I : ∣ A ∣
  pair : ∣ A ∣ → ∣ A ∣ → ∣ A ∣
  lam : ∣ A [ 1 ]∣ → ∣ A ∣
  ΣA : (∣ A ∣^ n) → ∣ A ∣
  ΠA : (∣ A [ n ]∣) → ∣ A ∣
  
  ΠA-opn : ∀ {n a k} → app A (ΠA (opn n a)) k ＝ extract a
  
  ΠΣA : (∣ A [ m ]∣^ n) → ∣ A ∣

module Realizability (A : PCA) where
  open PCA public
  open PCAWithVars public
  open PCACombinators A public

  RRel : Set → Set1
  RRel X = ∣ A ∣ → X → Prop
  
  _⊩[_]_ : ∀ {X} (a : ∣ A ∣?) (R : RRel X) (x : X) → Prop
  a ⊩[ R ] x = ∃[ a' ∈ (∣ A ∣)] ((a ＝ just a') AND (R a' x))
  
  Total : ∀ {X} → RRel X → Prop
  Total {X} R = (x : X) → ∃[ a ∈ ∣ A ∣ ] (R a x)
  
  _-Cart_ : ∀ {X} → (n : ℕ) → RRel X → Prop
  _-Cart_ {X} n R = (x : X) → (a : ∣ A ∣) → R a x → (∃[ k ∈ ( ∣ A ∣^ n )] (a ＝ ΣA k))
  
  Tracked : ∀ {X : Set} {Y : X → Set} (f : (x : X) → Y x) (fR : ∣ A ∣) (RX : RRel X) (RY : (x : X) → RRel (Y x)) → Prop
  Tracked {X} {Y} f fR RX RY = (x : X) → (a : ∣ A ∣) → RX a x → (app A fR a) ⊩[ RY x ] (f x)

module RealizabilityModel (A : PCA) where

  open Realizability A

  record Conᴿ (ΓLᴿ : Set) (ΓCᴿ : ℕ) : Set1 where
    field
      ∣_∣ : ΓLᴿ → Set
      _ᴿᴿ : RRel (Σ[ γ ∈ ΓLᴿ ] ∣_∣ γ)
      cart : ΓCᴿ -Cart _ᴿᴿ
      
  open Conᴿ

  record Subᴿ {ΓLᴿ ΓCᴿ ΔLᴿ ΔCᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Δᴿ : Conᴿ ΔLᴿ ΔCᴿ)
    (σLᴿ : ΓLᴿ → ΔLᴿ)
    (σCᴿ : ∣ A [ ΓCᴿ ]∣^ ΔCᴿ) : Set where
    field
      ∣_∣ : ∀ γ → ∣ Γᴿ ∣ γ → ∣ Δᴿ ∣ (σLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (σLᴿ γ , ∣_∣ γ γ')) (ΠΣA σCᴿ) (Γᴿ ᴿᴿ) (λ _ → Δᴿ ᴿᴿ)

  open Subᴿ

  record Tyᴿ (ΓLᴿ : Set) (TLᴿ : ΓLᴿ → Set) : Set1 where
    field
      ∣_∣ : ∀ γ {ΓCᴿ} {Γᴿ : Conᴿ ΓLᴿ ΓCᴿ} (γ' : ∣ Γᴿ ∣ γ) → TLᴿ γ → Set
      _ᴿᴿ : ∀ γ {ΓCᴿ} {Γᴿ} γ' → RRel (Σ[ t ∈ TLᴿ γ ] ∣_∣ γ {ΓCᴿ} {Γᴿ} γ' t)
      total : ∀ γ {ΓCᴿ} {Γᴿ} γ' → Total (_ᴿᴿ γ {ΓCᴿ} {Γᴿ} γ')

  open Tyᴿ

  record Tmᴿ {ΓLᴿ ΓCᴿ TLᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Tᴿ : Tyᴿ ΓLᴿ TLᴿ)
    (aLᴿ : (γ : ΓLᴿ) → TLᴿ γ)
    (aCᴿ : ∣ A [ ΓCᴿ ]∣) : Set where
    field
      ∣_∣ : ∀ γ (γ' : ∣ Γᴿ ∣ γ) → ∣ Tᴿ ∣ γ {ΓCᴿ} {Γᴿ} γ' (aLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (aLᴿ γ , ∣_∣ γ γ')) (ΠA aCᴿ) (Γᴿ ᴿᴿ) (λ (γ , γ') → (Tᴿ ᴿᴿ) γ {ΓCᴿ} {Γᴿ} γ')


  open Tmᴿ

  R : Model

  R .Model.ConL = Set
  R .Model.ConC = ℕ
  R .Model.Con ΓLᴿ ΓCᴿ = Conᴿ ΓLᴿ ΓCᴿ

  R .Model.∙C = zero

  R .Model.SubL ΓLᴿ ΔLᴿ = ΓLᴿ → ΔLᴿ
  R .Model.SubC ΓCᴿ ΔCᴿ = ∣ A [ ΓCᴿ ]∣^ ΔCᴿ
  R .Model.Sub Γᴿ Δᴿ σLᴿ σCᴿ = Subᴿ Γᴿ Δᴿ σLᴿ σCᴿ

  R .Model.TyL ΓLᴿ = ΓLᴿ → Set
  R .Model.TmL ΓLᴿ TLᴿ = (γ : ΓLᴿ) → TLᴿ γ

  R .Model.TmC ΓCᴿ = ∣ A [ ΓCᴿ ]∣

  (R Model.[p*]) {ΓC = n} t = opn n t

  R .Model.Ty ΓLᴿ TLᴿ = Tyᴿ ΓLᴿ TLᴿ
  R .Model.Tm Γᴿ Tᴿ aLᴿ aCᴿ = Tmᴿ Γᴿ Tᴿ aLᴿ aCᴿ

  ∣ R .Model.Spec T c ∣ γ {Γᴿ = Γᴿ} γ' t
    = Σ[ t' ∈ (∣ T ∣ γ {Γᴿ = Γᴿ} γ' t) ]
      ((γR : ∣ A ∣) → (Γᴿ ᴿᴿ) γR (γ , γ') → (app A {!   !} γR) ⊩[ (T ᴿᴿ) γ {Γᴿ = Γᴿ} γ' ] (t , t')) 
  -- (R .Model.Spec T c ᴿᴿ) γ a (t , t' , p) = a ＝ ΠA c
  -- R .Model.Spec T c .total γ (t , t' , p) = ΠA c , refl

  ∣ R .Model.spec t ∣ γ γ' = ∣ t ∣ γ γ' , let tᵀᴿ = (t ᵀᴿ) (γ , γ') in {!   !}
  (R .Model.spec t ᵀᴿ) x a x₁ = {!   !}

  ∣ R .Model.unspec t ∣ γ x = {!   !}
  (R .Model.unspec t ᵀᴿ) x a x₁ = {!   !}