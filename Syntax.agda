module Syntax where

-- Base CWF sorts are the 'realisers', i.e. computational content
-- this is just untyped LC
data CCon : Set
data CSub : CCon → CCon → Set
data CTm : CCon → Set

-- Irrelevant CWF sorts are the 'logical content'
data ICon : Set
data ISub : ICon → ICon → Set
data Ty : ICon → Set
data ITm : ∀ IΓ → Ty IΓ → Set

variable  
  IΓ IΓ' IΔ IΔ' : ICon
  CΓ CΓ' CΔ CΔ' : CCon
  Ia Ia' Ib Ib' : ITm _ _
  Ca Ca' Cb Cb' : CTm _
  Iσ Iσ' Iσ'' : ISub _ _
  Cσ Cσ' Cσ'' : CSub _ _

-- Displayed CWF sorts
data Con : ICon → CCon → Set
data Sub : ∀ {IΓ IΔ CΓ CΔ} → Con IΓ CΓ → Con IΔ CΔ → ISub IΓ IΔ → CSub CΓ CΔ → Set
data Tm : ∀ {IΓ CΓ} → (Γ : Con IΓ CΓ) → (A : Ty IΓ) → ITm IΓ A → CTm CΓ → Set

variable  
  Γ Γ' Δ Δ' : Con _ _
  A A' B B' : Ty _
  a a' b b' : Tm _ _ _ _
  σ σ' σ'' : Sub _ _ _ _

-- Comp

data CCon where
  ∙ : CCon
  _, : CCon → CCon
  
data CSub where
  id : CSub CΓ CΓ
  _∘_ : CSub CΓ CΓ' → CSub CΔ CΓ → CSub CΔ CΓ'

  p : CSub (CΓ ,) CΓ
  _,_ : (Cσ : CSub CΓ CΔ) → CTm CΓ → CSub CΓ (CΔ ,)

  ε : CSub CΓ ∙
  
data CTm where
  _[_] : CTm CΔ → (Cσ : CSub CΓ CΔ) → CTm CΓ
  q : CTm (CΓ ,)
  lam : CTm (CΓ ,) → CTm CΓ
  app : CTm CΓ → CTm (CΓ ,)

-- Irr

data ICon where
  ∙ : ICon
  _,_ : ∀ IΓ → Ty IΓ → ICon
  
data Ty where
  _[_] : Ty IΔ → ISub IΓ IΔ → Ty IΓ
  U : Ty IΓ
  El : ITm IΓ U → Ty IΓ
  Π : (A : Ty IΓ) → Ty (IΓ , A) → Ty IΓ
  
data ISub where
  id : ISub IΓ IΓ
  _∘_ : ISub IΓ IΓ' → ISub IΔ IΓ → ISub IΔ IΓ'
  p : ISub (IΓ , A) IΓ
  _,_ : (Iσ : ISub IΓ IΔ) → ITm IΓ (A [ Iσ ]) → ISub IΓ (IΔ , A)
  ε : ISub IΓ ∙
  
data ITm where
  _[_] : ITm IΔ A → (Iσ : ISub IΓ IΔ) → ITm IΓ (A [ Iσ ]) 
  q : ITm (IΓ , A) (A [ p ])
  lam : ITm (IΓ , A) B → ITm IΓ (Π A B)
  app : ITm IΓ (Π A B) → ITm (IΓ , A) B
  
-- Displayed CWF constructors

data Con where
  ∙ : Con ∙ ∙
  _,_ : (Γ : Con IΓ CΓ) → (A : Ty IΓ) → Con (IΓ , A) (CΓ ,)
  
data Sub where
  id : Sub Γ Γ id id
  _∘_ : Sub Γ Γ' Iσ Cσ → Sub Δ Γ Iσ' Cσ' → Sub Δ Γ' (Iσ ∘ Iσ') (Cσ ∘ Cσ')
  ε : Sub Γ ∙ ε ε 
  
  p : Sub (Γ , A) Γ p p
  _,_ : Sub Γ Δ Iσ Cσ → Tm Γ (A [ Iσ ]) Ia Ca → Sub Γ (Δ , A) (Iσ , Ia) (Cσ , Ca)

data Tm where
  _[_] : Tm Δ A Ia Ca → Sub Γ Δ Iσ Cσ → Tm Γ (A [ Iσ ]) (Ia [ Iσ ]) (Ca [ Cσ ])
  q : Tm (Γ , A) (A [ p ]) q q
  
  lam : Tm (Γ , A) B Ia Ca → Tm Γ (Π A B) (lam Ia) (lam Ca)
  app : Tm Γ (Π A B) Ia Ca → Tm (Γ , A) B (app Ia) (app Ca)
  
  -- same : (a : Tm Γ A Ca) → (b : Tm Γ B Ca) → Tm Γ (a ≈ b) Ca

  -- lam≈ : (f : Tm (Γ , A) B Ca) → Tm (Γ , A) (q ≈ f) Ca → Tm Γ (Π≈ A B) (lam q)
  -- app≈ : Tm Γ (Π A B) Ca → Tm (Γ , A) B (app Ca)