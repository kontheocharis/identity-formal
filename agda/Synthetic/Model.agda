{-# OPTIONS --prop --cubical #-}
module Synthetic.Model where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  
{-# BUILTIN REWRITE _≡_ #-}

-- Mode is either 0 (irrelevant) or ω (relevant)

data Mode : Set where
  z : Mode
  ω : Mode

opaque
  _*_ : Mode → Mode → Mode
  j * ω = j
  ω * j = j
  z * j = z

variable
  i j : Mode
    
opaque
  unfolding _*_

  j*ω : j * ω ≡ j
  j*ω {z} = refl
  j*ω {ω} = refl

  ω*j : ω * j ≡ j
  ω*j {z} = refl
  ω*j {ω} = refl

  z*j : z * j ≡ z
  z*j {z} = refl
  z*j {ω} = refl

  j*z : j * z ≡ z
  j*z {z} = refl
  j*z {ω} = refl

-- Better definitional computation for _*_
{-# REWRITE j*ω ω*j z*j j*z #-}

variable
  ℓ ℓ' ℓp ℓty ℓtm : Level

record OpTT-sorts {ℓp} {ℓty} {ℓtm} : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    $ : Prop ℓp
    Ty : Type ℓty
    Tm : Mode → Ty → Type ℓtm
    Ex : Type ℓtm
    
    
module _ (sorts : OpTT-sorts {ℓp} {ℓty} {ℓtm}) where
  open OpTT-sorts sorts
  
  variable
    A B C : Ty
    A~ B~ C~ : $ → Ty
    X Y Z : Tm _ _ → Ty
    X~ Y~ Z~ : (p : $) → Tm _ _ → Ty
    t u v : Tm _ _
    t~ u~ v~ : (p : $) → Tm _ _
    f g h : (a : Tm _ _) → Tm _ _
    f~ g~ h~ : (p : $) → (a : Tm _ _) → Tm _ _
    e s w : Ex
    eq : _ ≡ _
    eq~ : (p : $) → _ ≡ _
    
  coe : A ≡ B → Tm i A → Tm i B
  coe {i = i} p a = transport ((λ k → Tm i (p k))) a
  

  record OpTT-ctors : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm ⊔ ℓ)) where
    field
      -- Conversion between Tm and Ex
      ∣_∣ : ((p : $) → Tm i (A~ p)) → Ex
      ⟨_⟩ : Ex → ((p : $) → Tm i (A~ p))
      ∣⟨⟩∣ : ∣_∣ {i} {A~} (⟨ e ⟩) ≡ e
      ⟨∣∣⟩ : ⟨ ∣ t~ ∣ ⟩ ≡ t~
      
    _∋⟨_⟩_ : (A~ : $ → Ty) → Ex → ((p : $) → Tm i (A~ p))
    A~ ∋⟨ e ⟩ p = ⟨_⟩ {A~ = A~} e p
      
    field
      
      -- Irrelevant terms are ∅
      ∅ : Ex
      ∣z∣ : {t~ : $ → Tm z A} → ∣ t~ ∣ ≡ ∅

      -- Conversion from Tm i to Tm z
      [_] : Tm i A → Tm z A
      -- identity when i = z
      [z] : (a : Tm z A) → [ a ] ≡ a
      
    coe[] : ∀ (X : Tm z A → Ty) {t} → Tm i (X [ t ]) → Tm i (X t)
    coe[] X {t} = coe λ k → X ([z] t k)
      
    field

      -- -- Ex primitives
      -- lm : (Ex → Ex) → Ex
      -- ap : Ex → Ex → Ex
      ze : Ex
      su : Ex → Ex
      rec : Ex → (Ex → Ex → Ex) → Ex → Ex

      -- -- Pi types
      -- Π : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
      -- lam : ((a : Tm j A) → Tm i (X [ a ])) → Tm i (Π j A X)
      -- app : Tm i (Π j A X) → (a : Tm (i * j) A) → Tm i (X [ a ])
      -- -- Beta rules for irrelevant fragment
      -- lam-app-z : lam {i = z} (app t) ≡ t
      -- app-lam-z : app {i = z} (lam f) t ≡ f t
      -- -- Computation rules for ∣_∣
      -- ∣lam-ω∣ :
      --   ∣ (λ p → lam {ω} {A~ p} {ω} {X~ p} (f~ p)) ∣
      --     ≡ lm (λ x → ∣ (λ p → f~ p (A~ ∋⟨ x ⟩ p)) ∣)
      -- ∣app-ω∣ :
      --   ∣ (λ p → app {ω} {ω} {A~ p} {X~ p} (t~ p) (u~ p)) ∣
      --     ≡ ap ∣ t~ ∣ ∣ u~ ∣
      -- ∣lam-z∣ :
      --   ∣ (λ p → lam {z} {A~ p} {ω} {X~ p} (f~ p)) ∣
      --     ≡ ∣ (λ p → f~ p (A~ ∋⟨ ∅ ⟩ p)) ∣
      -- ∣app-z∣ :
      --   ∣ (λ p → app {ω} {z} {A~ p} {X~ p} (t~ p) (u~ p)) ∣
      --     ≡ ∣ t~ ∣
      -- [lam] : [ lam f ] ≡ lam (λ a → [ f a ])
      -- [app] : {t : Tm ω (Π j A X)} {u : Tm (j * ω) A} →
      --   [ app {ω} {j} {A} {X} t u ] ≡ coe[] X (app [ t ] [ u ])
        
      -- -- Internalised Ex (only in z)
      -- * : Ty
      -- ⌜_⌝ : Ex → Tm z *
      -- ⌞_⌟ : Tm z * → Ex
      -- ⌞⌟-⌜⌝ : ⌞ ⌜ e ⌝ ⌟ ≡ e
      -- ⌜⌝-⌞⌟ : ⌜ ⌞ t ⌟ ⌝ ≡ t
        
      -- -- Spec types
      -- Spec : (A : Ty) → Tm z * → Ty
      -- specz : (t : Tm z A) → Tm z (Spec A u)
      -- spec : (t : Tm ω A) → ⌜ ∣ (λ p → t) ∣ ⌝ ≡ u → Tm ω (Spec A u)
      -- unspec : Tm i (Spec A u) → Tm i A
      -- ∣spec∣ : {A~ : $ → Ty} {t~ : (p : $) → Tm ω (A~ p)}
      --   {eq~ : (p : $) → ⌜ ∣ (λ p' → (t~ p)) ∣ ⌝ ≡ u~ p}
      --     → ∣ (λ p → spec (t~ p) (eq~ p)) ∣ ≡ ∣ t~ ∣
      -- ∣unspec∣ : {A~ : $ → Ty} {t~ : (p : $) → Tm i (Spec (A~ p) u)}
      --     → ∣ (λ p → unspec (t~ p)) ∣ ≡ ⌞ u ⌟
      -- [spec] : [ spec t eq ] ≡ specz [ t ]
      -- [unspec] : [ unspec t ] ≡ unspec [ t ]
      
      -- Natural numbers
      Nat : Ty
      zero : Tm i Nat
      succ : Tm i Nat → Tm i Nat
      elim-Nat : (X : Tm z Nat → Ty)
        → (Tm i (X [ zero {i} ]))
        → ((n : Tm i Nat) → Tm i (X [ n ]) → Tm i (X [ succ n ]))
        → (n : Tm i Nat) → Tm i (X [ n ])
      elim-Nat-zero-z : ∀ {mz ms}
        → elim-Nat {i = z} X mz ms zero ≡ mz
      elim-Nat-succ-z : ∀ {mz ms n}
        → elim-Nat {i = z} X mz ms (succ n) ≡ ms n (elim-Nat {i = z} X mz ms n)

      -- ∣zero∣ : ∣ (λ p → zero {ω}) ∣ ≡ ze
      -- ∣succ∣ : ∣ (λ p → succ {ω} (t~ p)) ∣ ≡ su (∣ t~ ∣)
      -- ∣elim-Nat-ω∣ : ∀ {X~ : (p : $) → Tm z Nat → Ty}
      --   → {mz~ : (p : $) → Tm ω (X~ p [ zero {ω} ])}
      --   → {ms~ : (p : $) → (n : Tm ω Nat) → Tm ω (X~ p [ n ]) → Tm ω (X~ p [ succ n ])}
      --   → {n~ : (p : $) → Tm ω Nat}
      --   → ∣ (λ p → elim-Nat (X~ p) (mz~ p) (ms~ p) (n~ p)) ∣
      --       ≡ rec
      --         (∣ mz~ ∣)
      --         (λ a b →
      --           ∣ (λ p → ms~ p
      --             ((λ _ → Nat) ∋⟨ a ⟩ p)
      --             ((λ p → X~ p [ (λ _ → Nat) ∋⟨ a ⟩ p ]) ∋⟨ b ⟩ p)) ∣)
      --         (∣ n~ ∣)
              
      [zero] : [ zero {ω} ] ≡ zero
      [succ] : [ succ {ω} t ] ≡ succ [ t ]
      [elim-Nat] : ∀ {mz ms n}
        → [ elim-Nat {ω} X mz ms n ]
            ≡ coe {!   !}
              (elim-Nat {z} X (coe (λ k → X ([z] ([zero] k) (~ k))) [ mz ])
              (λ n mn → coe {!   !} [ ms {!   !} {!   !} ])
              {!   !})