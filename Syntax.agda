{-# OPTIONS --cubical #-}
module Syntax where

open import Cubical.Core.Primitives using (_≡_)
import Cubical.Core.Glue 

-- CONSTRUCTORS

-- Computational CWF sorts are the 'realisers', i.e. computational content
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

-- Displayed CWF sorts are indexed over computational and logical content.
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
  
Cq' : CTm (CΓ ,)
_[_]C' : CTm CΔ → (Cσ : CSub CΓ CΔ) → CTm CΓ

data CSub where
  id : CSub CΓ CΓ
  _∘_ : CSub CΓ CΓ' → CSub CΔ CΓ → CSub CΔ CΓ'
  id∘ : id ∘ Cσ ≡ Cσ
  ∘id : Cσ ∘ id ≡ Cσ
  ∘assoc : (Cσ ∘ Cσ') ∘ Cσ'' ≡ Cσ ∘ (Cσ' ∘ Cσ'')

  p : CSub (CΓ ,) CΓ
  _,_ : (Cσ : CSub CΓ CΔ) → CTm CΓ → CSub CΓ (CΔ ,)
  p∘, : p ∘ (Cσ , Ca) ≡ Cσ
  p,q : (p {CΓ} , Cq') ≡ id
  ,∘ : (Cσ , Ca) ∘ Cσ' ≡ ((Cσ ∘ Cσ') , (Ca [ Cσ' ]C'))

  ε : CSub CΓ ∙
  εη : Cσ ≡ ε
  
data CTm where
  _[_] : CTm CΔ → (Cσ : CSub CΓ CΔ) → CTm CΓ
  q : CTm (CΓ ,)
  lam : CTm (CΓ ,) → CTm CΓ
  app : CTm CΓ → CTm (CΓ ,)
  
  [id] : Ca [ id ]C' ≡ Ca
  [∘] : Ca [ Cσ ∘ Cσ' ]C' ≡ (Ca [ Cσ ]C') [ Cσ ]C'
  q[,] : q [ Cσ , Ca ]C' ≡ Ca
  
  lam[] : (lam Ca) [ Cσ ]C' ≡ lam ({!   !})

-- Irr

data ICon where
  ∙ : ICon
  _,_ : ∀ IΓ → Ty IΓ → ICon
  
data Ty where
  _[_] : Ty IΔ → ISub IΓ IΔ → Ty IΓ
  U : Ty IΓ
  El : ITm IΓ U → Ty IΓ
  Π : (A : Ty IΓ) → Ty (IΓ , A) → Ty IΓ
  Π0 : (A : Ty IΓ) → Ty (IΓ , A) → Ty IΓ
  Π-ID : (A : Ty IΓ) → Ty (IΓ , A) → Ty IΓ
  
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

  lam0 : ITm (IΓ , A) B → ITm IΓ (Π0 A B)
  app0 : ITm IΓ (Π0 A B) → ITm (IΓ , A) B

  lam-ID : ITm (IΓ , A) B → ITm IΓ (Π-ID A B)
  app-ID : ITm IΓ (Π-ID A B) → ITm (IΓ , A) B
  
-- Displayed CWF constructors

data Con where
  ∙ : Con ∙ ∙
  _,_ : (Γ : Con IΓ CΓ) → (A : Ty IΓ) → Con (IΓ , A) (CΓ ,)
  _,I_ : (Γ : Con IΓ CΓ) → (A : Ty IΓ) → Con (IΓ , A) CΓ
  
data Sub where
  id : Sub Γ Γ id id
  _∘_ : Sub Γ Γ' Iσ Cσ → Sub Δ Γ Iσ' Cσ' → Sub Δ Γ' (Iσ ∘ Iσ') (Cσ ∘ Cσ')
  ε : Sub Γ ∙ ε ε 
  
  p : Sub (Γ , A) Γ p p
  _,_ : Sub Γ Δ Iσ Cσ → Tm Γ (A [ Iσ ]) Ia Ca → Sub Γ (Δ , A) (Iσ , Ia) (Cσ , Ca)
  
  pI : Sub (Γ ,I A) Γ p id
  _,I_ : Sub Γ Δ Iσ Cσ → (Ia : ITm IΓ (A [ Iσ ])) → Sub Γ (Δ ,I A) (Iσ , Ia) Cσ

data Tm where
  _[_] : Tm Δ A Ia Ca → Sub Γ Δ Iσ Cσ → Tm Γ (A [ Iσ ]) (Ia [ Iσ ]) (Ca [ Cσ ])
  q : Tm (Γ , A) (A [ p ]) q q
  
  lam : Tm (Γ , A) B Ia Ca → Tm Γ (Π A B) (lam Ia) (lam Ca)
  app : Tm Γ (Π A B) Ia Ca → Tm (Γ , A) B (app Ia) (app Ca)

  lam0 : Tm (Γ ,I A) B Ia Ca → Tm Γ (Π0 A B) (lam0 Ia) Ca
  app0 : Tm Γ (Π0 A B) Ia Ca → Tm (Γ ,I A) B (app0 Ia) Ca

  lam-ID : Tm (Γ , A) B Ia q → Tm Γ (Π-ID A B) (lam-ID Ia) (lam q)
  app-ID : Tm Γ (Π-ID A B) Ia Ca → Tm (Γ , A) B (app-ID Ia) q

-- EQUATIONS


