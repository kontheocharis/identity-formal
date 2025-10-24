{-# OPTIONS --prop --type-in-type #-}
module Experiments.Internal3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂)
open import Axiom.Extensionality.Propositional using (Extensionality)
open Relation.Binary.PropositionalEquality.≡-Reasoning
  
{-# BUILTIN REWRITE _≡_ #-}

postulate
  funext : Extensionality _ _
  $ : Prop
  
M$_ : ({{_ : $}} → Set) → Set
M$_ A = {{p : $}} → A

data Mode : Set where
  z : Mode
  ω : Mode
  
postulate
  _*_ : Mode → Mode → Mode

variable
  i j : Mode

postulate
  j*ω : j * ω ≡ j
  ω*j : ω * j ≡ j
  z*j : z * j ≡ z
  j*z : j * z ≡ z

  {-# REWRITE j*ω ω*j z*j j*z #-}

  
postulate
  Ty : Set
  Tm : Mode → Ty → Set
  Ex : Set

variable
  A B C : Ty
  X Y Z : Tm _ _ → Ty
  a b c : Tm _ _
  f g h : (a : Tm _ _) → Tm _ _
  a$ b$ c$ : Ex
  p : _ ≡ _
  
coe : {A B : Ty} → (A ≡ B) → Tm i A → Tm i B
coe refl a = a

postulate
  [_] : Tm ω A → Tm z A 

  ∣_∣ : {A : M$ Ty} → M$ (Tm i A) → Ex
  ⟨_⟩ : Ex → M$ Tm i A
  
  ∣[]∣ : ∀ {A} {a : Tm ω A} → ∣ [ a ] ∣ ≡ ∣ a ∣
  ∣⟨⟩∣ : ∀ {A : M$ Ty} {e : Ex} → ∣_∣ {i = i} {A = A} (⟨ e ⟩) ≡ e
  -- ⟨∣∣⟩ : ∀ {A} {a : M$ Tm i A} → ⟨ ∣ a ∣ ⟩ ≡ a
  
  {-# REWRITE ∣[]∣ ∣⟨⟩∣ #-}

↑_ : Tm i A → Tm z A 
↑_ {i = z} a = a
↑_ {i = ω} a = [ a ]

↓_ : Tm ω A → Tm i A
↓_ {i = ω} a = a
↓_ {i = z} a = [ a ]

postulate
  Spec : Ty → Ex → Ty

  spec : (t : Tm i A) → ∣ t ∣ ≡ a$ → Tm i (Spec A a$)
  unspec : Tm i (Spec A a$) → Tm i A
  
  ∣spec∣ : ∀ {A : M$ Ty} {t : M$ Tm i A} {p : M$ (∣ t ∣ ≡ a$)} → ∣ spec t p ∣ ≡ ∣ t ∣
  ∣unspec∣ : ∣ unspec {A = A} {a$ = a$} a ∣ ≡ a$
  
  [spec] : [ spec a p ] ≡ spec [ a ] p
  [unspec] : [ unspec a ] ≡ unspec [ a ]

  {-# REWRITE ∣spec∣ ∣unspec∣ [spec] [unspec] #-}
  
postulate
  ∅ : Ex
  ze : Ex
  su : Ex → Ex
  rec : Ex → (Ex → Ex) → Ex → Ex
  rec-η : {a : Tm ω A} → rec ze su ∣ a ∣ ≡ ∣ a ∣
  -- rec-η2 : rec ze (λ x y → su y) ∣ a ∣ ≡ ∣ a ∣
  {-# REWRITE rec-η #-}
  
postulate
  lm : (Ex → Ex) → Ex
  ap : Ex → Ex → Ex
  
postulate
  Π : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
  lam : ((a : Tm j A) → Tm i (X (↑ a))) → Tm i (Π j A X)
  app : Tm i (Π j A X) → (a : Tm (i * j) A) → Tm i (X (↑ a))
  lam-app : app {i = z} (lam f) a ≡ f a

  ∣lam∣ : ∀ {A} {X} {f : (a : Tm ω A) → Tm j (X (↑ a))}
    → ∣ lam {X = X} f ∣ ≡ lm (λ x → ∣ f ⟨ x ⟩ ∣)
  ∣app∣ : {a : Tm j (Π ω A X)} {b : Tm j A} → ∣ app a b ∣ ≡ ap (∣ a ∣) (∣ b ∣)
  ∣lamz∣ : {f : (a : Tm z A) → Tm j (X (↑ a))} → ∣ lam {X = X} f ∣ ≡ ∣ f ⟨ ∅ ⟩ ∣
  ∣appz∣ : {a : Tm j (Π z A X)} {b : Tm z A} → ∣ app a b ∣ ≡ ∣ a ∣
  
  [lam] : [ lam f ] ≡ lam (λ x → [ f x ])
  [app] : [ app a b ] ≡ app [ a ] [ b ]
  
  {-# REWRITE ∣lam∣ ∣app∣ ∣lamz∣ ∣appz∣ [lam] [app] #-}


syntax Π j A (λ z → X) = Π j [ z ∈ A ] X

ΠID : (A : Ty) → (Tm z A → Ty) → Ty
ΠID A X = Π ω [ z ∈ A ] Spec (X z) ∣ z ∣

lamID : (f : (a : Tm ω A) → Tm i (X (↑ a)))
  → ((a : M$ Tm ω A) → ∣ f a ∣ ≡ ∣ a ∣)
      -- ^^ the rec eta rule won't work with this!
  → Tm i (ΠID A X)
lamID f p = lam (λ a → spec (f a) (p a))

appID : Tm i (ΠID A X) → (a : Tm i A) → Tm i (X (↑ a))
appID b a = unspec (app b a)

|lamID| : ∀ {p} → ∣ lamID {A} {i} {X} f p ∣ ≡ lm (λ x → x)
|lamID| {A} {i} {X} {f} {p} = begin
  lm (λ x → ∣ (λ ⦃ q ⦄ → spec (f ⟨ x ⟩) (p ⟨ x ⟩)) ∣)
    ≡⟨⟩
  lm (λ x → ∣ (λ ⦃ q ⦄ → (f ⟨ x ⟩) ) ∣)
    ≡⟨ cong lm (funext λ q → p (⟨ q ⟩)) ⟩
  lm (λ x → x)
    ∎
    
∣appID∣ : {b : Tm i (ΠID A X)} {a : Tm i A} → ∣ appID b a ∣ ≡ ∣ a ∣
∣appID∣ {i = z} {b = b} {a = a} = begin
  ∣ unspec (app b a) ∣
    ≡⟨⟩
  ∣ a ∣
    ∎
∣appID∣ {i = ω} {b = b} {a = a} = begin
  ∣ unspec (app b a) ∣
    ≡⟨⟩
  ∣ a ∣
    ∎
    
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
