module Equivalence where

open import Syntax
open import Normal
open import Relation.Nullary using (Dec; yes; no)

-- Decidable equivalence relation

data _⊢_≈var_⊢_ : ∀ Γ → {A : Ty Γ} → Var Γ A → ∀ Γ' → {A' : Ty Γ'} → Var Γ' A' → Set
data _⊢_≈nf_⊢_ : ∀ Γ → {A : Ty Γ} → Nf Γ A → ∀ Γ' → {A' : Ty Γ'} → Nf Γ' A' → Set
data _⊢_≈ne_⊢_ : ∀ Γ → {A : Ty Γ} → Ne Γ A → ∀ Γ' → {A' : Ty Γ'} → Ne Γ' A' → Set

data _⊢_≈var_⊢_ where
  rfl : Γ ⊢ v ≈var Γ ⊢ v
  vz≈ : (Γ , A) ⊢ vz ≈var (Γ' , A') ⊢ vz
  vs≈ : Γ ⊢ v ≈var Γ' ⊢ v' → (Γ , A) ⊢ vs v ≈var (Γ' , A') ⊢ vs v'

data _⊢_≈nf_⊢_ where
  rfl : Γ ⊢ n ≈nf Γ ⊢ n
  ne≈ : ∀ {e¬η e'¬η} → Γ ⊢ e ≈ne Γ' ⊢ e' → Γ ⊢ ne e e¬η ≈nf Γ' ⊢ ne e' e'¬η
  lam≈ : (Γ , A) ⊢ n ≈nf (Γ' , A') ⊢ n' → Γ ⊢ lam n ≈nf Γ' ⊢ lam n'

data _⊢_≈ne_⊢_ where
  rfl : Γ ⊢ e ≈ne Γ ⊢ e
  var≈ : Γ ⊢ v ≈var Γ' ⊢ v' → Γ ⊢ var v ≈ne Γ' ⊢ var v'
  app≈ : Γ ⊢ e ≈ne Γ' ⊢ e' → Γ ⊢ u ≈ne Γ' ⊢ u' → Γ ⊢ app e u ≈ne Γ' ⊢ app e' u'

_⊢_≈var?_⊢_ : ∀ Γ → {A : Ty Γ} → (n : Var Γ A)
  → ∀ Γ' → {A' : Ty Γ'} → (n' : Var Γ' A')
  → Dec (Γ ⊢ n ≈var Γ' ⊢ n')

_⊢_≈nf?_⊢_ : ∀ Γ → {A : Ty Γ} → (n : Nf Γ A)
  → ∀ Γ' → {A' : Ty Γ'} → (n' : Nf Γ' A')
  → Dec (Γ ⊢ n ≈nf Γ' ⊢ n')

_⊢_≈ne?_⊢_ : ∀ Γ → {A : Ty Γ} → (n : Ne Γ A)
  → ∀ Γ' → {A' : Ty Γ'} → (n' : Ne Γ' A')
  → Dec (Γ ⊢ n ≈ne Γ' ⊢ n')

(Γ , A) ⊢ vz ≈var? (Γ' , A') ⊢ vz = yes vz≈
(Γ , A) ⊢ vs v ≈var? (Γ' , A') ⊢ vs v' with Γ ⊢ v ≈var? Γ' ⊢ v'
... | yes l = yes (vs≈ l)
... | no l = no λ where
  (vs≈ a') → l a'
  rfl → l rfl
(Γ , A) ⊢ vz ≈var? (Γ' , A') ⊢ vs v' = no λ ()
(Γ , A) ⊢ vs v ≈var? (Γ' , A') ⊢ vz = no λ ()

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

Γ ⊢ var v ≈ne? Γ' ⊢ var v' with Γ ⊢ v ≈var? Γ' ⊢ v'
... | yes l = yes (var≈ l)
... | no l = no λ where
  (var≈ v'') → l v''
  rfl → l rfl
Γ ⊢ app f x ≈ne? Γ' ⊢ app f' x' with Γ ⊢ f ≈ne? Γ' ⊢ f' | Γ ⊢ x ≈ne? Γ' ⊢ x'
... | yes a | yes b = yes (app≈ a b)
... | no l | _ = no λ where
  (app≈ f'' x'') → l f''
  rfl → l rfl
... | _ | no l = no λ where
  (app≈ f'' x'') → l x''
  rfl → l rfl
Γ ⊢ var v ≈ne? Γ' ⊢ app f' x' = no λ () 
Γ ⊢ app f' x' ≈ne? Γ' ⊢ var v  = no λ () 