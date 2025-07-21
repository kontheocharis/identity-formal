
postulate
  Con : Set
  Ty : Con → Set

data Nf : ∀ Γ → Ty Γ → Set where

data Ne : ∀ Γ → Ty Γ → Set where
  