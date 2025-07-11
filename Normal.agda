module Normal where

open import Syntax

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