{-# OPTIONS --prop --type-in-type #-}
module Experiments.Internal where

open import Relation.Binary.PropositionalEquality.Core 

-- ᵏ : ∀ {A B : Set} → A → (A → B) → B
  
{-# BUILTIN REWRITE _≡_ #-}

postulate
  $ : Prop
  # : Prop
  
●$_ : ({{_ : $}} → Set) → Set
●$_ A = {{_ : $}} → A
  
●#_ : ({{_ : #}} → Set) → Set
●#_ A = {{_ : #}} → A

data _≡#_ {A : Set} : ●# A → ●# A → Set where
  refl :  (a : ●# A) → a ≡# a

{-# BUILTIN REWRITE _≡#_ #-}

data _≡$_ {A : Set} : ●$ A → ●$ A → Set where
  refl :  (a : ●$ A) → a ≡$ a

{-# BUILTIN REWRITE _≡$_ #-}
  
postulate
  Ty : Set
  Tm : ●# Ty → Set
  Tm$ : Set
  
variable
  A B C : ●# Ty
  a b c : Tm A
  a$ b$ c$ : Tm$
  
postulate
  $∣_∣ : ●$ Tm A → Tm$
  $⟨_⟩ : Tm$ → ●$ Tm A
  
postulate
  Raw : Ty
  raw : Tm$ → Tm Raw
  unraw : Tm Raw → Tm$

  raw-$ : $∣ raw a$ ∣ ≡ a$
  {-# REWRITE raw-$ #-}
  
  raw-unraw : raw (unraw a) ≡ a
  unraw-raw : unraw (raw a$) ≡ a$
  {-# REWRITE raw-unraw unraw-raw #-}
  
postulate
  Spec : Ty → Tm Raw → Ty

  spec : (t : Tm A) → Tm (Spec A (raw $∣ t ∣))
  unspec : Tm (Spec A a) → Tm A
  
  spec-$ : $∣ spec a ∣ ≡ $∣ a ∣
  unspec-$ : $∣ unspec {a = b} a ∣ ≡ unraw b
  {-# REWRITE spec-$ unspec-$ #-}
  
  spec-unspec : unspec (spec a) ≡ a
  unspec-spec : spec (unspec a) ≡ a
  {-# REWRITE spec-unspec unspec-spec #-}
  
postulate
  ze : Tm$
  su : Tm$ → Tm$
  nat-rec : Tm$ → (Tm$ → Tm$ → Tm$) → Tm$ → Tm$
  nat-rec-η1 : nat-rec ze (λ x y → su x) $∣ a ∣ ≡$ $∣ a ∣
  nat-rec-η2 : nat-rec ze (λ x y → su y) $∣ a ∣ ≡$ $∣ a ∣

postulate
  Nat : Ty
  zero : Tm Nat
  suc : Tm Nat → Tm Nat
  nat-ind : (P : ●# Tm Nat → Ty) →
            Tm (P zero) →
            ((n : Tm Nat) → Tm (P n) → Tm (P (suc n))) →
            (n : Tm Nat) → Tm (P n)
  nat-ind-zero : ∀ {P z s} → nat-ind P z s zero ≡# z
  nat-ind-suc : ∀ {P z s n} → nat-ind P z s (suc n) ≡# s n (nat-ind P z s n)
  
  zero-$ : $∣ zero ∣ ≡ ze
  suc-$ : $∣ suc a ∣ ≡ su $∣ a ∣
  nat-ind-$ : ∀ {P z s n}
    → $∣ nat-ind P z s n ∣ ≡ nat-rec $∣ z ∣ (λ x y → $∣ s $⟨ x ⟩ $⟨ y ⟩ ∣) $∣ n ∣
  
postulate
  Fin : ●# Tm Nat → Ty  
  fzero : {n : ●# Tm Nat} → Tm (Fin (suc n))
  fsuc : {n : ●# Tm Nat} → Tm (Fin n) → Tm (Fin (suc n))
  fin-ind : (P : {n : ●# Tm Nat} → ●# Tm (Fin n) → Ty)
            → ({n : ●# Tm Nat} → Tm (P (fzero {n})))
            → ({n : ●# Tm Nat} → (k : ●# Tm (Fin n)) → Tm (P k) → Tm (P (fsuc k)))
            → {n : ●# Tm Nat} → (k : ●# Tm (Fin n)) → Tm (P k)

  fzero-$ : ∀ {n} → $∣ fzero {n} ∣ ≡ ze
  fsuc-$ : ∀ {n k} → $∣ fsuc {n} k ∣ ≡ su $∣ k ∣
  fin-ind-$ : ∀ {P : {n : ●# Tm Nat} → ●# Tm (Fin n) → Ty}
      {fz : {n : ●# Tm Nat} → Tm (P (fzero {n}))}
      {fs : {n : ●# Tm Nat} → (k : ●# Tm (Fin n)) → Tm (P k) → Tm (P (fsuc k))}
      {k : {n : ●# Tm Nat} → ●# Tm (Fin n)}
    → $∣ fin-ind P fz fs k ∣ ≡ nat-rec $∣ fz ∣ {!   !} {!   !}

--  {{_ : $}}  

  -- unspec : (t : Tm# A) → Tm (Spec A t)

  -- Spec : (A : # → Ty) → Tm# → Prop

