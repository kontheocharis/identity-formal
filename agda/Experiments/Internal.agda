{-# OPTIONS --prop --type-in-type #-}
module Experiments.Internal where

open import Relation.Binary.PropositionalEquality.Core 
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂)
  
{-# BUILTIN REWRITE _≡_ #-}

postulate
  $ # : Prop
  
M$_ : ({{_ : $}} → Set) → Set
M$_ A = {{p : $}} → A

M#_ : ({{_ : #}} → Set) → Set
M#_ A = {{p : #}} → A

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
  Tm : Mode → M# Ty → Set
  Ex : Set

variable
  A B C : Ty
  X Y Z : Tm _ _ → M# Ty
  a b c : Tm _ _
  f g h : (a : Tm _ _) → Tm _ _
  a$ b$ c$ : Ex
  
postulate
  [_] : M# Tm ω A → Tm z A 
  un[_] : Tm z A → M# Tm ω A 

  ∣_∣ : {A : M$ Ty} → M$ (Tm ω A) → Ex
  un∣_∣ : Ex → M$ Tm ω A
  ∅ : M$ Tm z A

un∣_∣by_ : Ex → $ → Tm ω A
un∣ e ∣by p = un∣_∣ e {{p = p}} 

abs : {A : M$ Ty} → ((p : $) → Tm ω (A {{p}})) → Ex
abs f = ∣ (λ {{p}} → f p) ∣

↑_ : Tm i A → M# Tm j A 
↑_ {i = z} {j = z} a = a
↑_ {i = z} {j = ω} a = un[ a ]
↑_ {i = ω} {j = z} a = [ a ]
↑_ {i = ω} {j = ω} a = a

syntax abs (λ p → x) = ∣ p ⇒ x ∣

[_]' : Tm j A → Tm z A
[_]' {j = ω} a = [ a ]
[_]' {j = z} a = a
  
postulate
  Spec : Ty → Ex → Ty

  spec : (t : Tm ω A) → Tm ω (Spec A ∣ t ∣)
  specz : (t : Tm z A) → Tm z (Spec A a$)
  unspec : Tm i (Spec A a$) → Tm i A
  
  ∣spec∣ : ∣ spec a ∣ ≡ ∣ a ∣
  ∣unspec∣ : ∣ unspec {A = A} {a$ = a$} a ∣ ≡ a$
  
  [spec] : [ spec a ] ≡ specz [ a ]
  [unspec] : [ unspec a ] ≡ unspec [ a ]
  
postulate

  ze : Ex
  su : Ex → Ex
  rec : Ex → (Ex → Ex) → Ex → Ex
  rec-η : {a : Tm ω A} → rec ze su ∣ a ∣ ≡ ∣ a ∣
  -- rec-η2 : rec ze (λ x y → su y) ∣ a ∣ ≡ ∣ a ∣
  
postulate
  lm : (Ex → Ex) → Ex
  ap : Ex → Ex → Ex

  Π : (j : Mode) → (A : Ty) → (Tm j A → M# Ty) → Ty
  
-- ↑ : ∀ {M : Set} → (Tm z A → M) → (Tm j A → M) 
-- ↑ x t = x [ t ]'
  
postulate
  lam : ((a : Tm j A) → Tm i (X a)) → Tm i (Π j A X)
  app : Tm i (Π j A X) → (a : Tm (i * j) A) → Tm i (X (↑ a))
  lam-app : app {i = z} (lam f) a ≡ f a

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

-- --  {{_ : $}}  

--   -- unspec : (t : Tm# A) → Tm (Spec A t)

--   -- Spec : (A : # → Ty) → Tm# → Prop

