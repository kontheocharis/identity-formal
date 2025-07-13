module DispComp where

-- Base CWF sorts are the 'realisers', i.e. computational content
-- this is just untyped LC
data 0Con : Set
data 0Sub : 0Con → 0Con → Set
data 0Tm : 0Con → Set

variable  
  0Γ 0Γ' 0Δ 0Δ' : 0Con
  0a 0a' 0b 0b' : 0Tm _
  0σ 0σ' 0σ'' : 0Sub _ _

-- Displayed CWF sorts
data Con : 0Con → Set
data Ty : Con 0Γ → Set
data Sub : ∀ {0Γ 0Δ} → Con 0Γ → Con 0Δ → 0Sub 0Γ 0Δ → Set
data Tm : ∀ {0Γ} → (Γ : Con 0Γ) → (A : Ty Γ) → 0Tm 0Γ → Set

variable  
  Γ Γ' Δ Δ' : Con _
  A A' B B' : Ty _
  a a' b b' : Tm _ _ _
  σ σ' σ'' : Sub _ _ _

data 0Con where
  ∙ : 0Con
  _, : 0Con → 0Con
  
data 0Sub where
  id : 0Sub 0Γ 0Γ
  _∘_ : 0Sub 0Γ 0Γ' → 0Sub 0Δ 0Γ → 0Sub 0Δ 0Γ'

  p : 0Sub (0Γ ,) 0Γ
  _,_ : (0σ : 0Sub 0Γ 0Δ) → 0Tm 0Γ → 0Sub 0Γ (0Δ ,)

  ε : 0Sub 0Γ ∙
  
data 0Tm where
  _[_] : 0Tm 0Δ → (0σ : 0Sub 0Γ 0Δ) → 0Tm 0Γ
  q : 0Tm (0Γ ,)
  lam : 0Tm (0Γ ,) → 0Tm 0Γ
  app : 0Tm 0Γ → 0Tm (0Γ ,)
  
-- Displayed CWF constructors

data Con where
  ∙ : Con ∙
  _,_ : (Γ : Con 0Γ) → (A : Ty Γ) → Con (0Γ ,)
  
data Ty where
  _[_] : Ty Δ → Sub Γ Δ 0σ → Ty Γ
  U : Ty Γ
  El : Tm Γ U 0a → Ty Γ
  Π : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  
  -- Computational equivalence
  _≈_ : Tm Γ A 0a → Tm Γ B 0b → Ty Γ

  Π≈ : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  
data Sub where
  id : Sub Γ Γ id
  _∘_ : Sub Γ Γ' 0σ → Sub Δ Γ 0σ' → Sub Δ Γ' (0σ ∘ 0σ')
  ε : Sub Γ ∙ ε
  
  p : Sub (Γ , A) Γ p
  _,_ : (σ : Sub Γ Δ 0σ) → Tm Γ (A [ σ ]) 0a → Sub Γ (Δ , A) (0σ , 0a)

data Tm where
  _[_] : Tm Δ A 0a → Sub Γ Δ 0σ → Tm Γ (A [ σ ]) (0a [ 0σ ])
  q : Tm (Γ , A) (A [ p ]) q
  
  lam : Tm (Γ , A) B 0a → Tm Γ (Π A B) (lam 0a)
  app : Tm Γ (Π A B) 0a → Tm (Γ , A) B (app 0a)
  
  same : (a : Tm Γ A 0a) → (b : Tm Γ B 0a) → Tm Γ (a ≈ b) 0a

  lam≈ : (f : Tm (Γ , A) B 0a) → Tm (Γ , A) (q ≈ f) 0a → Tm Γ (Π≈ A B) (lam q)
  -- app≈ : Tm Γ (Π A B) 0a → Tm (Γ , A) B (app 0a)