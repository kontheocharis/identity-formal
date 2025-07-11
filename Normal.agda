module Normal where

open import Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

data Var : ∀ Γ → Ty Γ → Set
data Nf : ∀ Γ → Ty Γ → Set
data Ne : ∀ Γ → Ty Γ → Set

variable  
  n n' m m' : Nf _ _
  e e' u u' : Ne _ _
  v v' : Var _ _

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
  

-- Decidable equality

_≡var?_ : (v : Var Γ A) → (v' : Var Γ A) → Dec (v ≡ v')
vz ≡var? vz = yes refl
vs i ≡var? vs i' with i ≡var? i'
... | yes refl = yes refl
... | no i¬≡ = no λ { refl → i¬≡ refl }
vz ≡var? vs i' = no λ ()
vs i ≡var? vz = no λ ()
