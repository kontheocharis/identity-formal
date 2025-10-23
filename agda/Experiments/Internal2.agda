{-# OPTIONS --prop --type-in-type #-}
module Experiments.Internal2 where

open import Relation.Binary.PropositionalEquality.Core 
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂)
  
{-# BUILTIN REWRITE _≡_ #-}

postulate
  $ : Prop
  
M$_ : ({{_ : $}} → Set) → Set
M$_ A = {{p : $}} → A

data Mode : Set where
  z : Mode
  ω : Mode
  
_*_ : Mode → Mode → Mode
z * j = z
j * z = z
ω * ω = ω

variable
  i j : Mode
  
postulate
  Ty : Set
  Tmz : Ty → Set
  Tm : (A : Ty) → Tmz A → Set
  Ex : Set

variable
  A B C : Ty
  X Y Z : Tmz _ → Ty
  X' Y' Z' : ∀ {a} → Tm _ a → Ty
  a b c : Tmz _
  a' b' c' : Tm _ _
  f g h : (a : Tmz _) → Tmz _
  a$ b$ c$ : Ex
  
postulate
  ∅ : M$ Tmz A
  ∣_∣ : {A : M$ Ty} {a : M$ Tmz A} → M$ (Tm A a) → Ex
  un∣_∣ : Ex → M$ Tm A ∅
  
postulate
  Spec : Ty → Ex → Ty

  specz : (t : Tmz A) → Tmz (Spec A a$)
  spec : (a' : Tm A a) → Tm (Spec A ∣ a' ∣) (specz a)
  unspecz : Tmz (Spec A a$) → Tmz A
  unspec : Tm (Spec A a$) a → Tm A (unspecz a)
  
  ∣spec∣ : ∣ spec a' ∣ ≡ ∣ a' ∣
  ∣unspec∣ : ∣ unspec {A = A} {a$ = a$} a' ∣ ≡ a$
  
postulate

  ze : Ex
  su : Ex → Ex
  rec : Ex → (Ex → Ex) → Ex → Ex
  rec-η : {a' : Tm A a} → rec ze su ∣ a' ∣ ≡ ∣ a' ∣
  -- rec-η2 : rec ze (λ x y → su y) ∣ a ∣ ≡ ∣ a ∣
  
postulate
  lm : (Ex → Ex) → Ex
  ap : Ex → Ex → Ex

postulate
  Π0 : (A : Ty) → (Tmz A → Ty) → Ty
  lam0z : ((a : Tmz A) → Tmz (X a)) → Tmz (Π0 A X)
  app0z : Tmz (Π0 A X) → (a : Tmz A) → Tmz (X a)
  lam-app : app0z (lam0z f) a ≡ f a
  app-lam : lam0z (app0z a) ≡ a

  lam0 : ((a : Tmz A) → Tm (X a) (f a)) → Tm (Π0 A X) (lam0z f)
  app0 : Tm (Π0 A X) b → (a : Tmz A) → Tm (X a) (app0z b a)

  Π : (A : Ty) → (∀ {a} → Tm A a → Ty) → Ty
  lamz : (∀ {a} (a' : Tm A a) → Tmz (X' a')) → Tmz (Π A X')
  appz : Tmz (Π A X') → (a : Tmz A) → Tmz (X {!   !})
  
-- ↑ : ∀ {M : Set} → (Tm z A → M) → (Tm j A → M) 
-- ↑ x t = x [ t ]'
  
  -- lam : ((a : Tm j A) → Tm i (X (↑ a))) → Tm i (Π j A X)
  -- app : Tm i (Π j A X) → (a : Tm (i * j) A) → Tm i (X (↑ a))
  -- lam-app : app {i = z} (lam f) a ≡ f a

  -- ∣lam∣ : ∀ {A} {X} {f : (a : Tm ω A) → Tm ω (↑ X a)}
  --   → ∣ lam {X = X} f ∣ ≡ lm (λ x → ∣ f (un∣ x ∣) ∣)
  -- ∣app∣ : {a : Tm ω (Π ω A X)} {b : Tm ω A} → ∣ app a b ∣ ≡ ap (∣ a ∣) (∣ b ∣)
  -- ∣lamz∣ : {f : (a : Tm z A) → Tm ω (↑ X a)} → ∣ lam {X = X} f ∣ ≡ ∣ f ∅ ∣
  -- ∣appz∣ : {a : Tm ω (Π z A X)} {b : Tm z A} → ∣ app a b ∣ ≡ ∣ a ∣
  
  -- [lam] : [ lam f ] ≡ lam (λ x → [ f x ])
  -- [app] : [ app a b ] ≡ app [ a ] [ b ]


-- postulate
--   Nat : Ty
--   zero : Tm Nat
--   suc : Tm Nat → Tm Nat
--   nat-ind : (P : ●# Tm Nat → Ty) →
--             Tm (P zero) →
--             ((n : Tm Nat) → Tm (P n) → Tm (P (suc n))) →
--             (n : Tm Nat) → Tm (P n)
--   nat-ind-zero : ∀ {P z s} → nat-ind P z s zero ≡# z
--   nat-ind-suc : ∀ {P z s n} → nat-ind P z s (suc n) ≡# s n (nat-ind P z s n)
  
--   zero-$ : $∣ zero ∣ ≡ ze
--   suc-$ : $∣ suc a ∣ ≡ su $∣ a ∣
--   nat-ind-$ : ∀ {P z s n}
--     → $∣ nat-ind P z s n ∣ ≡ nat-rec $∣ z ∣ (λ x y → $∣ s $⟨ x ⟩ $⟨ y ⟩ ∣) $∣ n ∣
  
-- postulate
--   Fin : ●# Tm Nat → Ty  
--   fzero : {n : ●# Tm Nat} → Tm (Fin (suc n))
--   fsuc : {n : ●# Tm Nat} → Tm (Fin n) → Tm (Fin (suc n))
--   fin-ind : (P : {n : ●# Tm Nat} → ●# Tm (Fin n) → Ty)
--             → ({n : ●# Tm Nat} → Tm (P (fzero {n})))
--             → ({n : ●# Tm Nat} → (k : ●# Tm (Fin n)) → Tm (P k) → Tm (P (fsuc k)))
--             → {n : ●# Tm Nat} → (k : ●# Tm (Fin n)) → Tm (P k)

--   fzero-$ : ∀ {n} → $∣ fzero {n} ∣ ≡ ze
--   fsuc-$ : ∀ {n k} → $∣ fsuc {n} k ∣ ≡ su $∣ k ∣
--   fin-ind-$ : ∀ {P : {n : ●# Tm Nat} → ●# Tm (Fin n) → Ty}
--       {fz : {n : ●# Tm Nat} → Tm (P (fzero {n}))}
--       {fs : {n : ●# Tm Nat} → (k : ●# Tm (Fin n)) → Tm (P k) → Tm (P (fsuc k))}
--       {k : {n : ●# Tm Nat} → ●# Tm (Fin n)}
--     → $∣ fin-ind P fz fs k ∣ ≡ nat-rec $∣ fz ∣ {!   !} {!   !}

-- --  {{∅ : $}}  

--   -- unspec : (t : Tm# A) → Tm (Spec A t)

--   -- Spec : (A : # → Ty) → Tm# → Prop
