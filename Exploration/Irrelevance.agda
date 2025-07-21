{-# OPTIONS --rewriting #-}
module Irrelevance where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- A failed experiment

data Con : Set
data Ty : Con → Set
data Sub : Con → Con → Set
data Tm : ∀ Γ → Ty Γ → Set
data 0Tm : ∀ Γ → Ty Γ → Set

variable  
  Γ Γ' Δ Δ' : Con
  A A' B B' : Ty _
  a a' b b' : Tm _ _
  σ σ' : Sub _ _
  
{-# BUILTIN REWRITE _≡_ #-}

coe : A ≡ B → Tm Γ A → Tm Γ B
coe refl a = a

0coe : A ≡ B → 0Tm Γ A → 0Tm Γ B
0coe refl a = a

data Con where
  ∙ : Con
  _,_ : ∀ Γ → Ty Γ → Con
  _,0_ : ∀ Γ → Ty Γ → Con

-- Types
data Ty where
  _[_] : Ty Δ → Sub Γ Δ → Ty Γ
  
`0` : Con → Con
`0`s : Sub Γ Δ → Sub (`0` Γ) (`0` Δ)

_₀T : Ty Γ → Ty (`0` Γ)
_₀t : 0Tm Γ A → 0Tm (`0` Γ) (A ₀T)

`0` ∙ = ∙
`0` (Γ , A) = (`0` Γ) ,0 (A ₀T)
`0` (Γ ,0 A) = (`0` Γ) ,0 (A ₀T)

(A [ σ ]) ₀T = (A ₀T) [ `0`s σ ]

data Sub where
  -- Category
  ε : Sub Γ ∙

  p : Sub (Γ , A) Γ
  _,_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]) → Sub Γ (Δ , A)

  p0 : Sub (Γ ,0 A) Γ
  _,0_ : (σ : Sub Γ Δ) → 0Tm Γ (A [ σ ]) → Sub Γ (Δ ,0 A)

  $0 : Sub (Γ , A) (Γ ,0 A)

id : Sub Γ Γ
_∘_ : Sub Γ Δ → Sub Γ' Γ → Sub Γ' Δ

  
data 0Tm where
  _[_] : 0Tm Δ A → (σ : Sub Γ Δ) → 0Tm Γ (A [ σ ])
  q0 : 0Tm (Γ ,0 A) (A [ p0 ])
  ∣_∣ : Tm Γ A → 0Tm Γ A
  
data Tm where
  _[_] : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
  q : Tm (Γ , A) (A [ p ])

[][] : (A [ σ ]) [ σ' ] ≡ A [ σ ∘ σ' ]
{-# REWRITE [][] #-}

postulate
  $0p : p ≡ p0 {A = A} ∘ $0
  {-# REWRITE $0p #-}

  ∣q∣ : ∣ q {A = A} ∣ ≡ q0 {A = A} [ $0 ]
  {-# REWRITE ∣q∣ #-}

∅ : Sub Γ (`0` Γ)
∅ {Γ = ∙} = id
∅ {Γ = Γ ,0 A} = (∅ ∘ p0) ,0 {!   !}
∅ {Γ = Γ , A} = (∅ ∘ p) ,0 ∣ {!   !} ∣
  
postulate
  -- Ty Γ ≃ Ty (`0` Γ)
  ₀[∅] : (A ₀T) [ ∅ ] ≡ A
  [∅]₀ : (A [ ∅ ]) ₀T ≡ A

0$ : Sub (Γ ,0 A) ((`0` Γ) ,0 (A ₀T))
0$ = ∅
