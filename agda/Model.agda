module Model where

open import Data.Nat hiding (_^_)
open import Data.Fin
open import Data.Unit
open import Data.Maybe
open import Data.Product hiding (∃)


record Model : Set2 where
  field
    -- Logical
    ConL : Set1
    SubL : ConL → ConL → Set
    TyL : ConL → Set1
    TmL : ∀ ΓL → TyL ΓL → Set
    
    -- Computational
    ConC : Set
    SubC : ConC → ConC → Set
    TmC : ConC → Set
    
    -- Total
    Con : ConL → ConC → Set1
    Sub : ∀ {ΓL ΔL ΓC ΔC} → Con ΓL ΓC → Con ΔL ΔC → SubL ΓL ΔL → SubC ΓC ΔC → Set
    Ty : ∀ ΓL → TyL ΓL → Set1
    Tm : ∀ {ΓL ΓC AL} → Con ΓL ΓC → Ty ΓL AL → TmL ΓL AL → TmC ΓC → Set
    

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


module PCACombinators (A : PCA) where
  open PCAWithVars
  
  I : ∣ A ∣
  
  pair : ∣ A ∣ → ∣ A ∣ → ∣ A ∣
  lam : ∣ A [ 1 ]∣ → ∣ A ∣
  
  ΣA : (∣ A ∣^ n) → ∣ A ∣
  ΣA {n = zero} f = I
  ΣA {n = suc n} f = pair (f zero) (ΣA (λ i → f (suc i)))
  
  ΠA : (∣ A [ n ]∣) → ∣ A ∣
  ΠA {n = zero} x = {!  eval x ? !}
  ΠA {n = suc n} x = {!   !}

  ΠΣA : (∣ A [ m ]∣^ n) → ∣ A ∣

data ∃ (A : Set) (P : A → Prop) : Prop where
  _,_ : (x : A) → P x → ∃ A P
  
data _AND_ (P Q : Prop) : Prop where
  _,_ : P → Q → P AND Q
  
data _＝_ {A : Set} (x : A) : A → Prop where
  refl : x ＝ x
  
syntax ∃ A (λ x → P) = ∃[ x ∈ A ] P

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
      ∣_∣ : ∀ γ → TLᴿ γ → Set
      _ᴿᴿ : ∀ γ → RRel (Σ[ t ∈ TLᴿ γ ] ∣_∣ γ t)
      total : ∀ γ → Total (_ᴿᴿ γ)

  open Tyᴿ

  record Tmᴿ {ΓLᴿ ΓCᴿ TLᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Tᴿ : Tyᴿ ΓLᴿ TLᴿ)
    (aLᴿ : (γ : ΓLᴿ) → TLᴿ γ)
    (aCᴿ : ∣ A [ ΓCᴿ ]∣) : Set where
    field
      ∣_∣ : ∀ γ → ∣ Γᴿ ∣ γ → ∣ Tᴿ ∣ γ (aLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (aLᴿ γ , ∣_∣ γ γ')) (ΠA aCᴿ) (Γᴿ ᴿᴿ) (λ (γ , γ') → (Tᴿ ᴿᴿ) γ )


  open Tmᴿ

  R : Model

  R .Model.ConL = Set
  R .Model.ConC = ℕ
  R .Model.Con ΓLᴿ ΓCᴿ = Conᴿ ΓLᴿ ΓCᴿ

  R .Model.SubL ΓLᴿ ΔLᴿ = ΓLᴿ → ΔLᴿ
  R .Model.SubC ΓCᴿ ΔCᴿ = ∣ A [ ΓCᴿ ]∣^ ΔCᴿ
  R .Model.Sub Γᴿ Δᴿ σLᴿ σCᴿ = Subᴿ Γᴿ Δᴿ σLᴿ σCᴿ

  R .Model.TyL ΓLᴿ = ΓLᴿ → Set
  R .Model.TmL ΓLᴿ TLᴿ = (γ : ΓLᴿ) → TLᴿ γ

  R .Model.TmC ΓCᴿ = ∣ A [ ΓCᴿ ]∣

  R .Model.Ty ΓLᴿ TLᴿ = Tyᴿ ΓLᴿ TLᴿ
  R .Model.Tm Γᴿ Tᴿ aLᴿ aCᴿ = Tmᴿ Γᴿ Tᴿ aLᴿ aCᴿ