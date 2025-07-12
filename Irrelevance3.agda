module Irrelevance3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

data 0Con : Set
data Con : 0Con → Set

data Sz : 0Con → Set

data 0Ty : 0Con → Set
data Ty : ∀ 0Γ → 0Ty 0Γ → Sz 0Γ → Set

data 0Sub : 0Con → 0Con → Set
data Sub : ∀ {0Γ 0Δ} → Con 0Γ → Con 0Δ → 0Sub 0Γ 0Δ → Set

data 0Tm : ∀ 0Γ → 0Ty 0Γ → Set
data Tm : ∀ {0Γ 0A b} → (Γ : Con 0Γ) → (A : Ty 0Γ 0A b) → 0Tm 0Γ 0A → Set

variable  
  0Γ 0Γ' 0Δ 0Δ' : 0Con
  Γ Γ' Δ Δ' : Con _
  0A 0A' 0B 0B' 0C 0C' : 0Ty _
  A A' B B' C C' : Ty _ _ _
  0a 0a' 0b 0b' : 0Tm _ _
  a a' : Tm _ _ _
  0σ 0σ' : 0Sub _ _
  σ σ' : Sub _ _ _
  b b' : Sz _

data 0Con where
  ∙ : 0Con
  _,_ : ∀ 0Γ → 0Ty 0Γ → 0Con
  
data 0Ty where
  _[_] : 0Ty 0Δ → 0Sub 0Γ 0Δ → 0Ty 0Γ
  U : Sz 0Γ → 0Ty 0Γ
  El : 0Tm 0Γ (U b) → 0Ty 0Γ
  Π : (A : 0Ty 0Γ) → 0Ty (0Γ , A) → 0Ty 0Γ
  Σ : (A : 0Ty 0Γ) → 0Ty (0Γ , A) → 0Ty 0Γ
  
data 0Sub where
  id : 0Sub 0Γ 0Γ
  _∘_ : 0Sub 0Γ 0Γ' → 0Sub 0Δ 0Γ → 0Sub 0Δ 0Γ'
  ε : 0Sub 0Γ ∙
  
  p : 0Sub (0Γ , 0A) 0Γ
  _,_ : (0σ : 0Sub 0Γ 0Δ) → 0Tm 0Γ (0A [ 0σ ]) → 0Sub 0Γ (0Δ , 0A)

<_> : 0Tm 0Γ 0A → 0Sub 0Γ (0Γ , 0A)

data 0Tm where
  _[_] : 0Tm 0Δ 0A → (0σ : 0Sub 0Γ 0Δ) → 0Tm 0Γ (0A [ 0σ ])
  q : 0Tm (0Γ , 0A) (0A [ p ])

  lam : 0Tm (0Γ , 0A) 0B → 0Tm 0Γ (Π 0A 0B)
  app : 0Tm 0Γ (Π 0A 0B) → 0Tm (0Γ , 0A) 0B 

  pair : (a : 0Tm 0Γ 0A) → 0Tm 0Γ (0B [ < a > ]) → 0Tm 0Γ (Σ 0A 0B)
  fst : 0Tm 0Γ (Σ 0A 0B) → 0Tm 0Γ 0A
  snd : (p : 0Tm 0Γ (Σ 0A 0B)) → 0Tm 0Γ (0B [ < fst p > ])
  
< t > = id , (t [ id ])

data Sz where
  _[_] : Sz 0Δ → 0Sub 0Γ 0Δ → Sz 0Γ

  `0` : Sz 0Γ
  ptr : Sz 0Γ
  idx : Sz 0Γ
  _+_ : Sz 0Γ → Sz 0Γ → Sz 0Γ
  _⨾_ : (A : Ty 0Γ 0A b) → Sz (0Γ , 0A) → Sz 0Γ

-- Skeleton of Sz
data By : Set where
  `0` : By 
  ptr : By 
  idx : By 
  _+_ : By → By → By
  
by : Sz 0Γ → By
by (b [ σ ]) = by b
by `0` = `0`
by ptr = ptr
by idx = idx
by (b + b') = by b + by b'
by (_⨾_ {b = b} _ b') = by b + by b'

data Con where
  ∙ : Con ∙
  _,0_ : ∀ {0Γ} → (Γ : Con 0Γ) → (0A : 0Ty 0Γ) → Con (0Γ , 0A)
  _,_ : ∀ {0Γ} → (Γ : Con 0Γ) → ∀ {0A b} (A : Ty 0Γ 0A b) → Con (0Γ , 0A)
  
data Ty where
  _[_] : Ty 0Δ 0A b → (0σ : 0Sub 0Γ 0Δ) → Ty 0Γ (0A [ 0σ ]) (b [ 0σ ])
  El : (0a : 0Tm 0Γ (U b)) → Ty 0Γ (El 0a) b
  
  Box : Ty 0Γ 0A b → Ty 0Γ 0A ptr
  Make : Ty 0Γ 0A b → Ty 0Γ 0A ptr
  Irr : 0Ty 0Γ → Ty 0Γ 0A `0`

  Π* : (A : Ty 0Γ 0A b) → Ty (0Γ , 0A) 0B b' → Ty 0Γ (Π 0A 0B) ptr
  Π> : (A : Ty 0Γ 0A b) → Ty (0Γ , 0A) 0B b' → Ty 0Γ (Π 0A 0B) idx
  Π0 : (0A : 0Ty 0Γ) → ∀ {0B} → Ty (0Γ , 0A) 0B (b' [ p ]) → Ty 0Γ (Π 0A 0B) b'
  
  Σ : (A : Ty 0Γ 0A b) → Ty (0Γ , 0A) 0B (b' [ p ]) → Ty 0Γ (Σ 0A 0B) (b + b')
  ΣD : (A : Ty 0Γ 0A b) → Ty (0Γ , 0A) 0B b' → Ty 0Γ (Σ 0A 0B) (A ⨾ b')
  
data Sub where
  id : Sub Γ Γ id
  _∘_ : Sub Γ Γ' 0σ → Sub Δ Γ 0σ' → Sub Δ Γ' (0σ ∘ 0σ')
  ε : Sub Γ ∙ ε
  
  p : Sub (Γ , A) Γ p
  _,_ : (σ : Sub Γ Δ 0σ) → Tm Γ (A [ 0σ ]) 0a → Sub Γ (Δ , A) (0σ , 0a)

  p0 : Sub (Γ ,0 0A) Γ p
  _,0_ : (σ : Sub Γ Δ 0σ) → (0a : 0Tm 0Γ (0A [ 0σ ])) → Sub Γ (Δ ,0 0A) (0σ , 0a)

data Tm where
  _[_] : Tm Δ A 0a → Sub Γ Δ 0σ → Tm Γ (A [ 0σ ]) (0a [ 0σ ])
  q : Tm (Γ , A) (A [ p ]) q
  
  irr : (0a : 0Tm 0Γ 0A) → Tm Γ (Irr 0A) 0a
  
  lam* : Tm (Γ , A) B 0a → Tm Γ (Π> A B) (lam 0a)
  app* : Tm Γ (Π> A B) 0a → Tm (Γ , A) B (app 0a)

  lam0 : Tm (Γ ,0 0A) B 0a → Tm Γ (Π0 0A B) (lam 0a)
  app0 : Tm Γ (Π0 0A B) 0a → Tm (Γ ,0 0A) B (app 0a)

  app> : Tm Γ (Π> A B) 0a → Tm (Γ , A) B (app 0a)
  _∘>_ : Tm Γ (Π> A B) 0a
    → Tm (Γ ,0 0A) (Π> B C) 0b
    → Tm Γ (Π> A (C [ < app 0a > ])) (lam (app 0b [ < app 0a > ]))
  
  pair : Tm Γ A 0a → Tm Γ (B [ < 0a > ]) 0b → Tm Γ (Σ A B) (pair 0a 0b)
  fst : Tm Γ (Σ A B) 0a → Tm Γ A (fst 0a)
  snd : Tm Γ (Σ A B) 0b → Tm Γ (B [ < fst 0b > ]) (snd 0b)
  
  pairD : Tm Γ A 0a → Tm Γ (B [ < 0a > ]) 0b → Tm Γ (ΣD A B) (pair 0a 0b)
  fstD : Tm Γ (ΣD A B) 0a → Tm Γ A (fst 0a)
  sndD : Tm Γ (ΣD A B) 0b → Tm Γ (B [ < fst 0b > ]) (snd 0b)