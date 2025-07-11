module Syntax where

data Con : Set
data Ty : Con → Set
data Sub : Con → Con → Set
data Tm : ∀ Γ → Ty Γ → Set

data Con where
  ∙ : Con
  _,_ : ∀ Γ → Ty Γ → Con

variable  
  Γ Γ' Δ Δ' : Con
  A A' B B' : Ty _
  a a' b b' : Tm _ _

-- Types
data Ty where
  _[_] : Ty Δ → Sub Γ Δ → Ty Γ
  Π : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  U : Ty Γ
  El : Tm Γ U → Ty Γ
  
data Sub where
  p : Sub (Γ , A) Γ
  id : Sub Γ Γ
  _,_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]) → Sub Γ (Δ , A)
  <_> : Tm Γ A → Sub Γ (Γ , A)

data Tm where
  _[_] : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
  q : Tm (Γ , A) (A [ p ])
  lam : Tm (Γ , A) B → Tm Γ (Π A B)
  ap : Tm Γ (Π A B) → Tm (Γ , A) B