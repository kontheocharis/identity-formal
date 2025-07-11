module Syntax where

data Con : Set
data Ty : Con → Set
data Sub : Con → Con → Set
data Tm : ∀ Γ → Ty Γ → Set
data 0Tm : ∀ Γ → Ty Γ → Set

data Con where
  ∙ : Con
  _,_ : ∀ Γ → Ty Γ → Con
  _,0_ : ∀ Γ → Ty Γ → Con
  0×_ : Con → Con

variable  
  Γ Γ' Δ Δ' : Con
  A A' B B' : Ty _
  a a' b b' : Tm _ _

-- Types
data Ty where
  _[_] : Ty Δ → Sub Γ Δ → Ty Γ
  Π : (A : Ty Γ) → Ty (Γ ,0 A) → Ty Γ
  Π0 : (A : Ty Γ) → Ty (Γ ,0 A) → Ty Γ
  U : Ty Γ
  El : Tm Γ U → Ty Γ

data Sub where
  id : Sub Γ Γ
  _∘_ : Sub Γ Δ → Sub Γ' Γ → Sub Γ' Δ
  ε : Sub Γ ∙

  p : Sub (Γ , A) Γ
  p0 : Sub (Γ ,0 A) Γ

  _,0× : Sub Γ Δ → Sub Γ (0× Δ)
  _,_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]) → Sub Γ (Δ , A)
  _,0_ : (σ : Sub Γ Δ) → 0Tm Γ (A [ σ ]) → Sub Γ (Δ ,0 A)

  -- Derivable: (if we have the proper equations)
  none : Sub (Γ , A) (Γ ,0 A)
  <_> : Tm Γ A → Sub Γ (Γ , A)
  <_>0 : 0Tm Γ A → Sub Γ (Γ ,0 A)
  
data 0Tm where
  _[_] : 0Tm Δ A → (σ : Sub Γ Δ) → 0Tm Γ (A [ σ ])
  q0 : 0Tm (Γ ,0 A) (A [ p0 ])

  π : Tm (0× Γ) A → 0Tm Γ (A [ id ,0× ])
  
  -- Derivable:
  π' : Tm Γ A → 0Tm Γ A

  -- Derivable:
  lam : 0Tm (Γ , A) (B [ none ]) → 0Tm Γ (Π A B)
  lam0 : 0Tm (Γ ,0 A) B → 0Tm Γ (Π0 A B)
  app : 0Tm Γ (Π A B) → (a : 0Tm Γ A) → 0Tm Γ (B [ < a >0 ])
  app0 : 0Tm Γ (Π0 A B) → (a : 0Tm Γ A) → 0Tm Γ (B [ < a >0 ])
  
data Tm where
  _[_] : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
  q : Tm (Γ , A) (A [ p ])

  lam : Tm (Γ , A) (B [ none ]) → Tm Γ (Π A B)
  ap : Tm Γ (Π A B) → Tm (Γ , A) (B [ none ])

  lam0 : Tm (Γ ,0 A) B → Tm Γ (Π0 A B)
  ap0 : Tm Γ (Π A B) → Tm (Γ ,0 A) B

  π† : 0Tm Γ (A [ id ,0× ]) → Tm (0× Γ) A
  
  -- Derivable:
  app : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ < π' a >0 ])
  app0 : Tm Γ (Π0 A B) → (a : 0Tm Γ A) → Tm Γ (B [ < a >0 ])
  