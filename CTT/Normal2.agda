module CTT.Normal2 where

open import Data.Bool
open import Relation.Binary.PropositionalEquality

data CCon : Set where
  ∙ : CCon
  _▷ : CCon → CCon

data Kind : Set where
  Ne Nf : Kind

data CNorm : Kind → (CΓ : CCon) → Set
data CVar : (CΓ : CCon) → Set

CNe = CNorm Ne
CNf = CNorm Nf
  
variable
  CΓ CΔ : CCon
  x x' y y' z z' : CNorm _ _
  v v' : CVar _
  k k' : Kind

data _≈_ : CNorm k CΓ → CNorm k CΓ → Set

coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
coe refl a = a

infix 4 _≡[_]_
_≡[_]_ : ∀ {i} {A B : Set i} → A → A ≡ B → B → Set i
x ≡[ p ] y = coe p x ≡ y

data CVar where
  vz : CVar (CΓ ▷)
  vs : CVar CΓ → CVar (CΓ ▷)

_[p] : CNorm k CΓ → CNorm k (CΓ ▷)

data CNorm where
  ne : CNe CΓ → CNf CΓ
  
  -- Intro
  nlam : CNf (CΓ ▷) → CNf CΓ
  nzero : CNf CΓ
  nsucc : CNf CΓ → CNf CΓ

  -- Elim
  napp : CNe CΓ → CNf CΓ → CNe CΓ
  nvar : CVar CΓ → CNe CΓ
  nelim : CNe CΓ → CNf CΓ → CNf (CΓ ▷ ▷) → CNe CΓ
  
(ne x) [p] = ne (x [p])
(nlam x) [p] = nlam (x [p])
nzero {CΓ} [p] = nzero {CΓ ▷}
(nsucc x) [p] = nsucc (x [p])
(napp x y) [p] = napp (x [p]) (y [p])
(nvar v) [p] = nvar (vs v)
(nelim x x' y) [p] = nelim (x [p]) (x' [p]) (y [p])

data _≈_ where
  -- Equivalence rel
  rfl : x ≈ x
  
  -- Congruence
  ne≈ : x ≈ y → ne x ≈ ne y

  nlam≈ : x ≈ y → nlam x ≈ nlam y
  nsucc≈ : x ≈ y → nsucc x ≈ nsucc y

  napp≈ : x ≈ x' → y ≈ y' → napp x y ≈ napp x' y'
  nelim≈ : x ≈ x' → y ≈ y' → z ≈ z' → nelim x y z ≈ nelim x' y' z'

  -- Eta rules
  n-Πη : nlam (ne (napp (x [p]) (ne (nvar vz)))) ≈ ne x
  n-elimη : nelim x nzero (nsucc (ne (nvar (vs vz)))) ≈ x

data ⊥ : Set where

data Dec (X : Set) : Set where
  yes : X → Dec X
  no : (X → ⊥) → Dec X
  
symm : x ≈ y → y ≈ x 
symm {x = ne x} {y = ne .x} rfl = rfl
symm {x = ne x} {y = ne x₁} (ne≈ p) = ne≈ (symm p)
symm {x = ne x} {y = nlam x₁} ()
symm {x = ne x} {y = nzero} ()
symm {x = ne x} {y = nsucc x₁} ()
symm {x = nlam .(ne (napp (x [p]) (ne (nvar vz))))} {y = ne x} n-Πη = {!   !}
symm {x = nlam x} {y = nlam .x} rfl = {!   !}
symm {x = nlam x} {y = nlam x₁} (nlam≈ p) = {!   !}
symm {x = nlam x} {y = nzero} ()
symm {x = nlam x} {y = nsucc x₁} ()
symm {x = nzero} {y = ne x} ()
symm {x = nzero} {y = nlam x} ()
symm {x = nzero} {y = nzero} rfl = {!   !}
symm {x = nzero} {y = nsucc x} ()
symm {x = nsucc x} {y = ne x₁} ()
symm {x = nsucc x} {y = nlam x₁} ()
symm {x = nsucc x} {y = nzero} ()
symm {x = nsucc x} {y = nsucc .x} rfl = {!   !}
symm {x = nsucc x} {y = nsucc x₁} (nsucc≈ p) = {!   !}
symm {x = napp x x₁} {y = napp .x .x₁} rfl = {!   !}
symm {x = napp x x₁} {y = napp x₂ x₃} (napp≈ p p₁) = {!   !}
symm {x = napp x x₁} {y = nvar x₂} ()
symm {x = napp x x₁} {y = nelim x₂ x₃ x₄} ()
symm {x = nvar x} {y = napp x₁ x₂} ()
symm {x = nvar x} {y = nvar .x} rfl = {!   !}
symm {x = nvar x} {y = nelim x₁ x₂ x₃} ()
symm {x = nelim .(napp x x₁) .nzero .(nsucc (ne (nvar (vs vz))))} {y = napp x x₁} n-elimη = {!   !}
symm {x = nelim .(nvar x) .nzero .(nsucc (ne (nvar (vs vz))))} {y = nvar x} n-elimη = {!   !}
symm {x = nelim x x₁ x₂} {y = nelim .x .x₁ .x₂} rfl = {!   !}
symm {x = nelim x x₁ x₂} {y = nelim x₃ x₄ x₅} (nelim≈ p p₁ p₂) = {!   !}
symm {x = nelim .(nelim x x₁ x₂) .nzero .(nsucc (ne (nvar (vs vz))))} {y = nelim x x₁ x₂} n-elimη = {!   !}

trs : x ≈ y → y ≈ z → x ≈ z

_≡?_ : (a b : CVar CΓ) → Dec (a ≡ b)
vz ≡? vz = yes refl
(vs i) ≡? (vs i') with i ≡? i'
... | yes refl = yes refl
... | no ¬p = no λ where
  refl → ¬p refl
vz ≡? (vs _) = no λ ()
(vs _) ≡? vz = no λ ()

_≈?_ : (a : CNorm k CΓ) → (b : CNorm k CΓ) → Dec (a ≈ b)
ne x ≈? ne x₁ with x ≈? x₁
... | yes p = yes (ne≈ p)
... | no ¬p = no λ where
  rfl → ¬p rfl
  (ne≈ a) → ¬p a
ne x ≈? nlam x₁ = no λ ()
ne x ≈? nzero = no λ ()
ne x ≈? nsucc x₁ = no λ ()
nlam x ≈? ne x₁ with (x ≈? ne (napp (x₁ [p]) (ne (nvar vz))))
... | yes p = yes (trs (nlam≈ p) n-Πη)
... | no ¬p = no λ where
  n-Πη → ¬p rfl
nlam x ≈? nlam x₁ with x ≈? x₁
... | yes p = yes (nlam≈ p)
... | no ¬p = no λ where
  rfl → ¬p rfl
  (nlam≈ a) → ¬p a
nlam x ≈? nzero = no λ ()
nlam x ≈? nsucc x₁ = no λ ()
nzero ≈? ne x = no λ ()
nzero ≈? nlam x = no λ ()
nzero ≈? nzero = yes rfl
nzero ≈? nsucc x = no λ ()
nsucc x ≈? ne x₁ = no λ ()
nsucc x ≈? nlam x₁ = no λ ()
nsucc x ≈? nzero = no λ ()
nsucc x ≈? nsucc x₁ with x ≈? x₁
... | yes p = yes (nsucc≈ p)
... | no ¬p = no λ where
  rfl → ¬p rfl
  (nsucc≈ a) → ¬p a
napp x x₁ ≈? napp x₂ x₃ with x ≈? x₂ with x₁ ≈? x₃
... | yes p | yes q = yes (napp≈ p q)
... | _ | no ¬q = no λ where
  rfl → ¬q rfl
  (napp≈ a a₁) → ¬q a₁
... | no ¬p | _ = no λ where
  rfl → ¬p rfl
  (napp≈ a a₁) → ¬p a
napp x x₁ ≈? nvar x₂ = no λ ()
napp x x₁ ≈? nelim x₂ x₃ x₄ = no λ ()
nvar x ≈? napp x₁ x₂ = no λ ()
nvar x ≈? nvar x₁ with x ≡? x₁
... | yes refl = yes rfl
... | no ¬p = no λ where
  rfl → ¬p refl
nvar x ≈? nelim x₁ x₂ x₃ = no λ ()
nelim x x₁ x₂ ≈? x₃
  with x₃
  with x ≈? x₃
  with x₁ ≈? nzero
  with x₂ ≈? nsucc (ne (nvar (vs vz)))
nelim x x₁ x₂ ≈? x₃ | _ | yes p | yes q | yes r = yes (trs (nelim≈ p q r) n-elimη)
nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | no ¬p | q | r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
...   | no ¬p' | _ | _ = no λ { rfl → ¬p' rfl
                              ; (nelim≈ a a₁ a₂) → ¬p' a
                              ; n-elimη → ¬p rfl } 
...   | _ | no ¬q' | _ = no λ { rfl → ¬q' rfl
                              ; (nelim≈ a a₁ a₂) → ¬q' a₁
                              ; n-elimη → ¬p rfl } 
...   | _ | _ | no ¬r' = no λ { rfl → ¬r' rfl
                              ; (nelim≈ a a₁ a₂) → ¬r' a₂
                              ; n-elimη → ¬p rfl } 
nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | p | no ¬q | r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
...   | no ¬p' | _ | _ = no λ { rfl → ¬p' rfl
                              ; (nelim≈ a a₁ a₂) → ¬p' a
                              ; n-elimη → ¬q rfl } 
...   | _ | no ¬q' | _ = no λ { rfl → ¬q' rfl
                              ; (nelim≈ a a₁ a₂) → ¬q' a₁
                              ; n-elimη → ¬q rfl } 
...   | _ | _ | no ¬r' = no λ { rfl → ¬r' rfl
                              ; (nelim≈ a a₁ a₂) → ¬r' a₂
                              ; n-elimη → ¬q rfl } 
nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | p | q | no ¬r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
...   | no ¬p' | _ | _ = no λ { rfl → ¬p' rfl
                              ; (nelim≈ a a₁ a₂) → ¬p' a
                              ; n-elimη → ¬r rfl } 
...   | _ | no ¬q' | _ = no λ { rfl → ¬q' rfl
                              ; (nelim≈ a a₁ a₂) → ¬q' a₁
                              ; n-elimη → ¬r rfl } 
...   | _ | _ | no ¬r' = no λ { rfl → ¬r' rfl
                              ; (nelim≈ a a₁ a₂) → ¬r' a₂
                              ; n-elimη → ¬r rfl } 
(nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | no ¬p | q | r = no λ { n-elimη → ¬p rfl }
(nelim x x₁ x₂ ≈? x₃) | nvar x₄ | no ¬p | q | r = no λ { n-elimη → ¬p rfl }
(nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | p | no ¬q | r = no λ { n-elimη → ¬q rfl }
(nelim x x₁ x₂ ≈? x₃) | nvar x₄ | p | no ¬q | r = no λ { n-elimη → ¬q rfl }
(nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | p | q | no ¬r = no λ { n-elimη → ¬r rfl }
(nelim x x₁ x₂ ≈? x₃) | nvar x₄ | p | q | no ¬r = no λ { n-elimη → ¬r rfl }