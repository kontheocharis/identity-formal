module Normal where

open import Syntax
open import Relation.Binary.PropositionalEquality using (_＝_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

data Var : ∀ Γ → Ty Γ → Set
data 0Var : ∀ Γ → Ty Γ → Set
data Nf : ∀ Γ → Ty Γ → Set
data 0Nf : ∀ Γ → Ty Γ → Set
data Ne : ∀ Γ → Ty Γ → Set
data 0Ne : ∀ Γ → Ty Γ → Set

variable  
  n n' m m' : Nf _ _
  0n 0n' 0m 0m' : 0Nf _ _
  e e' u u' : Ne _ _
  0e 0e' 0u 0u' : 0Ne _ _
  v v' : Var _ _
  0v 0v' : 0Var _ _

⌜_⌝var : Var Γ A → Tm Γ A
⌜_⌝0var : 0Var Γ A → 0Tm Γ A
⌜_⌝ne : Ne Γ A → Tm Γ A
⌜_⌝0ne : 0Ne Γ A → 0Tm Γ A
⌜_⌝nf : Nf Γ A → Tm Γ A
⌜_⌝0nf : 0Nf Γ A → 0Tm Γ A
  
-- Types without η rules
data Ty¬η : ∀ Γ → Ty Γ → Set where
  U¬η : Ty¬η Γ U
  El¬η : ∀ t → Ty¬η Γ (El t)

data Nf where
  lam : Nf (Γ , A) (B [ none ]) → Nf Γ (Π A B)
  lam0 : Nf (Γ ,0 A) B → Nf Γ (Π0 A B)
  
  -- Anything with η rules should be η-long
  ne : Ne Γ A → Ty¬η Γ A → Nf Γ A

data 0Nf where
  lam : 0Nf (Γ , A) (B [ none ]) → 0Nf Γ (Π A B)
  lam0 : 0Nf (Γ ,0 A) B → 0Nf Γ (Π0 A B)
  
  -- Anything with η rules should be η-long
  ne : 0Ne Γ A → Ty¬η Γ A → 0Nf Γ A
  
data Var where
  vz : Var (Γ , A) (A [ p ])
  vs : Var Γ B → Var (Γ , A) (B [ p ])
  
data 0Var where
  vz : 0Var (Γ ,0 A) (A [ p0 ])
  vs : 0Var Γ B → 0Var (Γ ,0 A) (B [ p0 ])

data Ne where
  var : Var Γ A → Ne Γ A
  app : Ne Γ (Π A B) → (a : Ne Γ A) → Ne Γ (B [ < π' (⌜ a ⌝ne) >0 ])
  app0 : Ne Γ (Π0 A B) → (a : 0Ne Γ A) → Ne Γ (B [ < ⌜ a ⌝0ne >0 ])

data 0Ne where
  var : 0Var Γ A → 0Ne Γ A
  app : 0Ne Γ (Π A B) → (a : 0Ne Γ A) → 0Ne Γ (B [ < ⌜ a ⌝0ne >0 ])
  app0 : 0Ne Γ (Π0 A B) → (a : 0Ne Γ A) → 0Ne Γ (B [ < ⌜ a ⌝0ne >0 ])
  
⌜ vz ⌝var = q
⌜ vs i ⌝var = (⌜ i ⌝var) [ p ]

⌜ vz ⌝0var = q0
⌜ vs i ⌝0var = (⌜ i ⌝0var) [ p0 ]

⌜ var i ⌝ne = ⌜ i ⌝var
⌜ app f x ⌝ne = app (⌜ f ⌝ne) (⌜ x ⌝ne)
⌜ app0 f x ⌝ne = app0 (⌜ f ⌝ne) (⌜ x ⌝0ne)

⌜ var i ⌝0ne = ⌜ i ⌝0var
⌜ app f x ⌝0ne = app (⌜ f ⌝0ne) (⌜ x ⌝0ne)
⌜ app0 f x ⌝0ne = app0 (⌜ f ⌝0ne) (⌜ x ⌝0ne)

⌜ lam f ⌝nf = lam (⌜ f ⌝nf)
⌜ lam0 f ⌝nf = lam0 (⌜ f ⌝nf)
⌜ ne n _ ⌝nf = ⌜ n ⌝ne

⌜ lam f ⌝0nf = lam (⌜ f ⌝0nf)
⌜ lam0 f ⌝0nf = lam0 (⌜ f ⌝0nf)
⌜ ne n _ ⌝0nf = ⌜ n ⌝0ne
  

-- Decidable equality

_＝var?_ : (v : Var Γ A) → (v' : Var Γ A) → Dec (v ＝ v')
vz ＝var? vz = yes refl
vs i ＝var? vs i' with i ＝var? i'
... | yes refl = yes refl
... | no i¬＝ = no λ { refl → i¬＝ refl }
vz ＝var? vs i' = no λ ()
vs i ＝var? vz = no λ ()
 