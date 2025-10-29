{-# OPTIONS --prop --cubical -WnoUnsupportedIndexedMatch #-}
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

private
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

private
  variable
    ℓ ℓ' ℓp ℓty ℓtm : Level

record OpTT-sorts {ℓp} {ℓty} {ℓtm} : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    $ : Prop ℓp
    Ty : Type ℓty
    Tm : Mode → Ty → Type ℓtm
    Ex : Type ℓtm

    -- Map to irrelevant
    [_]' : ∀ {A} → Tm ω A → Tm z A

  [_] : ∀ {i A} → Tm i A → Tm z A
  [_] {z} = λ x → x
  [_] {ω} = [_]'

  coe : ∀ {A B} → A ≡ B → Tm i A → Tm i B
  coe {i = i} p a = transport ((λ k → Tm i (p k))) a
    
module _ (sorts : OpTT-sorts {ℓp} {ℓty} {ℓtm}) where
  open OpTT-sorts sorts
  
  private
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
      p q r : $
  
  -- Telescopes
  data Tel : Type (ℓtm ⊔ ℓty)
  data Tms : Mode → Tel → Type (ℓtm ⊔ ℓty)

  variable
    Γ Γ' : Tel
    Δ Δ' : Tm _ _ → Tel
    X' Y' Z' : Tms _ _ → Ty
    f' g' h' : (δ : Tms _ _) → Tm _ _
    γ δ : Tms _ _

  data Tel where
    ∙ : Tel
    _at_,_ : (A : Ty) → Mode → (Tm z A → Tel) → Tel

  data Tms where
    ε : Tms i ∙
    _,_ : (a : Tm (i * j) A) → Tms i (Δ [ a ]) → Tms i (A at j , Δ)
    
  first : Tms i (A at j , Δ) → Tm (i * j) A
  first (a , γ) = a
    
  coes : Γ ≡ Γ' → Tms i Γ → Tms i Γ'
  coes {i = i} p γ = transport (λ k → Tms i (p k)) γ
    
  [[_]] : Tms i Γ → Tms z Γ
  [[_]] {i = z} γ = γ
  [[ ε ]] = ε
  [[_]] (_,_ {Δ = Δ} a γ) = [ a ] , [[ γ ]]
  
  record OpTT-ctors : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
    field
      -- Conversion between Tm and Ex
      ∣_∣ : ((p : $) → Tm ω (A~ p)) → Ex
      ⟨_⟩ : Ex → ((p : $) → Tm i (A~ p))
      ∣⟨⟩∣ : ∣_∣ {A~} (⟨ e ⟩) ≡ e
      ⟨∣∣⟩ : {t~ : (p : $) → Tm ω (A~ p)} → ⟨ ∣ t~ ∣ ⟩ ≡ t~
      
    _∋⟨_⟩_ : (A~ : $ → Ty) → Ex → ((p : $) → Tm i (A~ p))
    A~ ∋⟨ e ⟩ p = ⟨_⟩ {A~ = A~} e p
      
    field
      -- Irrelevant terms are ∅
      ∅ : Ex
      [⟨⟩] : [ A~ ∋⟨ e ⟩ p ]' ≡ A~ ∋⟨ e ⟩ p 
      
      -- We can use an irrelevant term to bind a relevant argument
      -- as long as we eliminate to an irrelevant term
      bind : ((δ : Tms ω Γ) → Tm z (X' [[ δ ]])) → (γ : Tms z Γ) → Tm z (X' γ)
      bind[]-1 : bind {Γ} {X'} f' [[ γ ]] ≡ f' γ
      bind[]-2 : bind {Γ} {X'} (λ δ → f' [[ δ ]]) ≡ f'

      -- Ex primitives
      lm : (Ex → Ex) → Ex
      ap : Ex → Ex → Ex
      ze : Ex
      su : Ex → Ex
      rec : Ex → (Ex → Ex → Ex) → Ex → Ex

      -- Pi types
      Π : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
      lam : ((a : Tm j A) → Tm i (X [ a ])) → Tm i (Π j A X)
      app : Tm i (Π j A X) → (a : Tm (i * j) A) → Tm i (X [ a ])
      -- Beta rules for irrelevant fragment
      lam-app-z : lam {i = z} (app t) ≡ t
      app-lam-z : app {i = z} (lam f) t ≡ f t
      -- Computation rules for ∣_∣
      ∣lam-ω∣ :
        ∣ (λ p → lam {ω} {A~ p} {ω} {X~ p} (f~ p)) ∣
          ≡ lm (λ x → ∣ (λ p → f~ p (A~ ∋⟨ x ⟩ p)) ∣)
      ∣app-ω∣ :
        ∣ (λ p → app {ω} {ω} {A~ p} {X~ p} (t~ p) (u~ p)) ∣
          ≡ ap ∣ t~ ∣ ∣ u~ ∣
      ∣lam-z∣ :
        ∣ (λ p → lam {z} {A~ p} {ω} {X~ p} (f~ p)) ∣
          ≡ ∣ (λ p → f~ p (A~ ∋⟨ ∅ ⟩ p)) ∣
      ∣app-z∣ :
        ∣ (λ p → app {ω} {z} {A~ p} {X~ p} (t~ p) (u~ p)) ∣
          ≡ ∣ t~ ∣
      [lam] : [ lam f ] ≡ lam (λ a → [ f a ])
      [app] : {t : Tm ω (Π j A X)} {u : Tm (j * ω) A}
        → [ app {ω} {j} {A} {X} t u ] ≡ app [ t ] [ u ]
        
      -- Internalised Ex (only in z)
      -- * : Ty
      -- ⌜_⌝ : Ex → Tm z *
      -- ⌞_⌟ : Tm z * → Ex
      -- ⌞⌟-⌜⌝ : ⌞ ⌜ e ⌝ ⌟ ≡ e
      -- ⌜⌝-⌞⌟ : ⌜ ⌞ t ⌟ ⌝ ≡ t
        
      -- Spec types
      Spec : (A : Ty) → Ex → Ty
      specz : (t : Tm z A) → Tm z (Spec A e)
      spec : (t : Tm ω A) → ∣ (λ p → t) ∣ ≡ e → Tm ω (Spec A e)
      unspec : Tm i (Spec A e) → Tm i A
      ∣spec∣ : {A~ : $ → Ty} {t~ : (p : $) → Tm ω (A~ p)}
        {eq~ : (p : $) → ∣ (λ p' → (t~ p)) ∣ ≡ e}
          → ∣ (λ p → spec (t~ p) (eq~ p)) ∣ ≡ ∣ t~ ∣
      ∣unspec∣ : {A~ : $ → Ty} {t~ : (p : $) → Tm ω (Spec (A~ p) e)}
          → ∣ (λ p → unspec (t~ p)) ∣ ≡ e
      [spec] : [ spec t eq ] ≡ specz [ t ]
      [unspec] : [ unspec t ] ≡ unspec [ t ]
      
      -- Natural numbers
      Nat : Ty
      zero : Tm i Nat
      succ : Tm i Nat → Tm i Nat
      elim-Nat : (X : Tm z Nat → Ty)
        → (Tm i (X zero))
        → ((δ : Tms i (Nat at ω , λ n → X [ n ] at ω , λ _ → ∙)) → Tm i (X (succ (first [[ δ ]]))))
        → (n : Tm i Nat) → Tm i (X [ n ])
      elim-Nat-zero-z : ∀ {mz ms}
        → elim-Nat {z} X mz ms zero ≡ mz
      elim-Nat-succ-z : ∀ {mz ms n}
        → elim-Nat {z} X mz ms (succ n) ≡ ms (n , elim-Nat {z} X mz ms n , ε)

      ∣zero∣ : ∣ (λ p → zero {ω}) ∣ ≡ ze
      ∣succ∣ : ∣ (λ p → succ {ω} (t~ p)) ∣ ≡ su (∣ t~ ∣)
      ∣elim-Nat-ω∣ : ∀ {X~ : (p : $) → Tm z Nat → Ty}
        → {mz~ : (p : $) → Tm ω (X~ p zero)}
        → {ms~ : (p : $) → (δ : Tms ω (Nat at ω , λ n → X~ p [ n ] at ω , λ _ → ∙)) → Tm ω (X~ p (succ (first [[ δ ]])))}
        → {n~ : (p : $) → Tm ω Nat}
        → ∣ (λ p → elim-Nat (X~ p) (mz~ p) (ms~ p) (n~ p)) ∣
            ≡ rec
              (∣ mz~ ∣)
              (λ x px → ∣ (λ p → ms~ p ((_ ∋⟨ x ⟩ p) , (((λ p → X~ p [ _ ∋⟨ x ⟩ p ]') ∋⟨ px ⟩ p)) , ε)) ∣)
              (∣ n~ ∣)
              
      [zero] : [ zero {ω} ] ≡ zero
      [succ] : [ succ {ω} t ] ≡ succ [ t ]
      [elim-Nat] : ∀ {mz ms n}
        → [ elim-Nat {ω} X mz ms n ] ≡ (elim-Nat {z} X [ mz ] (bind (λ δ' → [ ms δ' ])) [ n ])

      -- Classifying numeric expressions
      Num : Ex → Ty
      nat-num : (t : Tm ω Nat) → Tm z (Num ∣ (λ p → t) ∣)
        
      -- Computation for rec
      rec-η-1 : Tm z (Num e) → rec ze (λ m pm → su m) e ≡ e
      rec-η-2 : Tm z (Num e) → rec ze (λ m pm → su pm) e ≡ e
              
record OpTT {ℓp} {ℓty} {ℓtm} : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    sorts : OpTT-sorts {ℓp} {ℓty} {ℓtm}
  open OpTT-sorts sorts public
  field
    ctors : OpTT-ctors sorts
  open OpTT-ctors ctors public
