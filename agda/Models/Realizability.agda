module Models.Realizability where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc) renaming (zero to f0)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; [_]; []; _∷_; lookup; map; tabulate)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst; sym)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Agda.Primitive

open import Model
open import Realizability
open import Utils

module _ {ℓ'} (A : PCA) where
  open Realizability.Relations A public
  open OpTT
  open OpTT-sorts
  open OpTT-subs
  open OpTT-str
  
  record Conᴿ : Set (lsuc (lsuc ℓ')) where
    field
      syn : ℕ
      sem : ∣ A [ 0 ]∣^ syn → Set ℓ'
      
  open Conᴿ
      
  record Subᴿ (Γ Δ : Conᴿ) : Set (lsuc ℓ') where
    field
      syn : ∣ A [ Γ .syn ]∣^ Δ .syn
      sem : ∀ γ → Γ .sem γ → Δ .sem (compose syn γ)

  open Subᴿ
      
  record Tyᴿ (Γ : Conᴿ) : Set (lsuc (lsuc ℓ')) where
    field
      sem : ∀ γ (γ' : Γ .sem γ) → ∣ A [ 0 ]∣^ 1 → Set ℓ'
      
  open Tyᴿ

  record Tmzᴿ (Γ : Conᴿ) (T : Tyᴿ Γ) : Set (lsuc ℓ') where
    field
      sem : ∀ γ γ' → T .sem γ γ' ([ ⌜ I ⌝ ])

  open Tmzᴿ

  record Tmᴿ (Γ : Conᴿ) (T : Tyᴿ Γ) (t : Tmzᴿ Γ T) : Set (lsuc ℓ') where
    field
      syn : ∣ A [ 0 ]∣^ 1
      sem' : ∀ γ γ' → T .sem γ γ' syn
      proj : ∀ γ γ' → (T .sem) γ γ' syn → (T .sem) γ γ' ([ ⌜ I ⌝ ])
      
  record Exᴿ (Γ : Conᴿ) : Set (lsuc ℓ') where
    field
      syn : ∣ A [ 0 ]∣^ 1
  
  M-sorts : OpTT-sorts {lsuc (lsuc ℓ')} {lsuc ℓ'}
  M-sorts .Con = Conᴿ
  M-sorts .Sub = Subᴿ
  M-sorts .Ty = Tyᴿ
  M-sorts .Tmz = Tmzᴿ
  M-sorts .Tm = Tmᴿ
  M-sorts .Ex = Exᴿ
  M-sorts .$ = {!   !}

  M : OpTT {lsuc (lsuc ℓ')} {lsuc ℓ'}
  M .sorts = M-sorts
  M .subs = {!   !}
  M .str = {!   !}