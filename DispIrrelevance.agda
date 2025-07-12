module DispIrrelevance where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Displayed style is soo much better damn

data 0Con : Set
data Con : 0Con → Set

data Ty : 0Con → Set

data 0Sub : 0Con → 0Con → Set
data Sub : ∀ {0Γ 0Δ} → Con 0Γ → Con 0Δ → 0Sub 0Γ 0Δ → Set

data 0Tm : ∀ 0Γ → Ty 0Γ → Set
data Tm : ∀ {0Γ} → (Γ : Con 0Γ) → (A : Ty 0Γ) → 0Tm 0Γ A → Set

variable  
  0Γ 0Γ' 0Δ 0Δ' : 0Con
  Γ Γ' Δ Δ' : Con _
  A A' B B' : Ty _
  0a 0a' 0b 0b' : 0Tm _ _
  a a' b b' : Tm _ _ _
  0σ 0σ' : 0Sub _ _
  σ σ' : Sub _ _ _

data 0Con where
  ∙ : 0Con
  _,_ : ∀ 0Γ → Ty 0Γ → 0Con

data Con where
  ∙ : Con ∙
  _,_ : ∀ {0Γ} → (Γ : Con 0Γ) → (A : Ty 0Γ) → Con (0Γ , A)
  _,0_ : ∀ {0Γ} → (Γ : Con 0Γ) → (A : Ty 0Γ) → Con (0Γ , A)
  
data Ty where
  _[_] : Ty 0Δ → 0Sub 0Γ 0Δ → Ty 0Γ
  U : Ty 0Γ
  El : 0Tm 0Γ U → Ty 0Γ

  Π : (A : Ty 0Γ) → Ty (0Γ , A) → Ty 0Γ
  Π0 : (A : Ty 0Γ) → Ty (0Γ , A) → Ty 0Γ
  
data 0Sub where
  id : 0Sub 0Γ 0Γ
  _∘_ : 0Sub 0Γ 0Γ' → 0Sub 0Δ 0Γ → 0Sub 0Δ 0Γ'
  ε : 0Sub 0Γ ∙
  
  p : 0Sub (0Γ , A) 0Γ
  _,_ : (0σ : 0Sub 0Γ 0Δ) → 0Tm 0Γ (A [ 0σ ]) → 0Sub 0Γ (0Δ , A)
  
data Sub where
  id : Sub Γ Γ id
  _∘_ : Sub Γ Γ' 0σ → Sub Δ Γ 0σ' → Sub Δ Γ' (0σ ∘ 0σ')
  ε : Sub Γ ∙ ε
  
  p : Sub (Γ , A) Γ p
  _,_ : (σ : Sub Γ Δ 0σ) → Tm Γ (A [ 0σ ]) 0a → Sub Γ (Δ , A) (0σ , 0a)

  p0 : Sub (Γ ,0 A) Γ p
  _,0_ : (σ : Sub Γ Δ 0σ) → (0a : 0Tm 0Γ (A [ 0σ ])) → Sub Γ (Δ ,0 A) (0σ , 0a)

data 0Tm where
  _[_] : 0Tm 0Δ A → (0σ : 0Sub 0Γ 0Δ) → 0Tm 0Γ (A [ 0σ ])
  q : 0Tm (0Γ , A) (A [ p ])
  
  lam : 0Tm (0Γ , A) B → 0Tm 0Γ (Π A B)
  app : 0Tm 0Γ (Π A B) → 0Tm (0Γ , A) B 
  
  lam0 : 0Tm (0Γ , A) B → 0Tm 0Γ (Π0 A B)
  app0 : 0Tm 0Γ (Π0 A B) → 0Tm (0Γ , A) B 

data Tm where
  _[_] : Tm Δ A 0a → Sub Γ Δ 0σ → Tm Γ (A [ 0σ ]) (0a [ 0σ ])
  q : Tm (Γ , A) (A [ p ]) q
  q0 : Tm (Γ ,0 A) (A [ p ]) q
  
  lam : Tm (Γ , A) B 0a → Tm Γ (Π A B) (lam 0a)
  app : Tm Γ (Π A B) 0a → Tm (Γ , A) B (app 0a)
  
  lam0 : Tm (Γ ,0 A) B 0a → Tm Γ (Π0 A B) (lam0 0a)
  app0 : Tm Γ (Π0 A B) 0a → Tm (Γ ,0 A) B (app0 0a)
  
  
-- Resourced CWF:

record RCon : Set where
  constructor _×_
  field
    0con : 0Con
    con : Con 0con

open RCon

𝐔 : RCon → 0Con
𝐔 = 0con

record RSub (Γ : RCon) (Δ : RCon) : Set where
  constructor _×_
  field
    0sub : 0Sub (Γ .0con) (Δ .0con)
    sub : Sub (Γ .con) (Δ .con) 0sub
    
open RSub
    
𝐔-sub : ∀ {Γ Δ} → RSub Γ Δ → 0Sub (𝐔 Γ) (𝐔 Δ)
𝐔-sub = 0sub
    
record RTm (Γ : RCon) (A : Ty (𝐔 Γ)) : Set where
  constructor _×_
  field
    0tm : 0Tm (Γ .0con) A
    tm : Tm (Γ .con) A 0tm
    
open RTm

𝐔-tm : ∀ {Γ A} → RTm Γ A → 0Tm (𝐔 Γ) A
𝐔-tm = 0tm