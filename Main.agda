module Main where

open import Relation.Nullary using (Dec; yes; no)

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
 
data Var : ∀ Γ → Ty Γ → Set
data Nf : ∀ Γ → Ty Γ → Set
data Ne : ∀ Γ → Ty Γ → Set

⌜_⌝var : Var Γ A → Tm Γ A
⌜_⌝ne : Ne Γ A → Tm Γ A
⌜_⌝nf : Nf Γ A → Tm Γ A
  
-- Types without η rules
data Ty¬η : ∀ Γ → Ty Γ → Set where
  U¬η : Ty¬η Γ U
  El¬η : ∀ t → Ty¬η Γ (El t)

data Nf where
  lam : Nf (Γ , A) B → Nf Γ (Π A B)
  
  -- Anything with η rules should be η-long
  ne : Ne Γ A → Ty¬η Γ A → Nf Γ A
  
data Var where
  vz : Var (Γ , A) (A [ p ])
  vs : Var Γ B → Var (Γ , A) (B [ p ])

data Ne where
  var : Var Γ A → Ne Γ A
  app : Ne Γ (Π A B) → (a : Ne Γ A) → Ne Γ (B [ < ⌜ a ⌝ne > ])
  
⌜ vz ⌝var = q
⌜ vs i ⌝var = (⌜ i ⌝var) [ p ]

⌜ var i ⌝ne = ⌜ i ⌝var
⌜ app f x ⌝ne = ap (⌜ f ⌝ne) [ < ⌜ x ⌝ne > ]

⌜ lam f ⌝nf = lam (⌜ f ⌝nf)
⌜ ne n _ ⌝nf = ⌜ n ⌝ne

variable  
  n n' m m' : Nf _ _
  e e' u u' : Ne _ _

-- Decidable equivalence relation

data _⊢_≈nf_⊢_ : ∀ Γ → {A : Ty Γ} → Nf Γ A → ∀ Γ' → {A' : Ty Γ'} → Nf Γ' A' → Set
data _⊢_≈ne_⊢_ : ∀ Γ → {A : Ty Γ} → Ne Γ A → ∀ Γ' → {A' : Ty Γ'} → Ne Γ' A' → Set

data _⊢_≈nf_⊢_ where
  rfl : Γ ⊢ n ≈nf Γ ⊢ n
  ne≈ : ∀ {e¬η e'¬η} → Γ ⊢ e ≈ne Γ' ⊢ e' → Γ ⊢ ne e e¬η ≈nf Γ' ⊢ ne e' e'¬η
  lam≈ : (Γ , A) ⊢ n ≈nf (Γ' , A') ⊢ n' → Γ ⊢ lam n ≈nf Γ' ⊢ lam n'

data _⊢_≈ne_⊢_ where
  rfl : Γ ⊢ e ≈ne Γ ⊢ e
  app≈ : Γ ⊢ e ≈ne Γ' ⊢ e' → Γ ⊢ u ≈ne Γ' ⊢ u' → Γ ⊢ app e u ≈ne Γ' ⊢ app e' u'

_⊢_≈nf?_⊢_ : ∀ Γ → {A : Ty Γ} → (n : Nf Γ A)
  → ∀ Γ' → {A' : Ty Γ'} → (n' : Nf Γ' A')
  → Dec (Γ ⊢ n ≈nf Γ' ⊢ n')

_⊢_≈ne?_⊢_ : ∀ Γ → {A : Ty Γ} → (n : Ne Γ A)
  → ∀ Γ' → {A' : Ty Γ'} → (n' : Ne Γ' A')
  → Dec (Γ ⊢ n ≈ne Γ' ⊢ n')

Γ ⊢ lam n ≈nf? Γ' ⊢ lam n' with (Γ , _) ⊢ n ≈nf? (Γ' , _) ⊢ n'
... | yes l = yes (lam≈ l)
... | no l = no λ where
  (lam≈ a') → l a'
  rfl → l rfl
Γ ⊢ (ne e e¬η) ≈nf? Γ' ⊢ (ne e' e'¬η) with Γ ⊢ e ≈ne? Γ' ⊢ e'
... | yes l = yes (ne≈ l)
... | no l = no λ where
  (ne≈ a') → l a'
  rfl → l rfl
Γ ⊢ lam n ≈nf? Γ' ⊢ (ne e e¬η) = no λ () 
Γ ⊢ (ne e e¬η) ≈nf? Γ' ⊢ lam n = no λ () 

Γ ⊢ app f x ≈ne? Γ' ⊢ app f' x' with Γ ⊢ f ≈ne? Γ' ⊢ f' | Γ ⊢ x ≈ne? Γ' ⊢ x'
... | yes a | yes b = yes (app≈ a b)
... | no l | _ = no λ where
  (app≈ f'' x'') → l f''
  rfl → l rfl
... | _ | no l = no λ where
  (app≈ f'' x'') → l x''
  rfl → l rfl