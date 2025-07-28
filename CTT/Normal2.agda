{-# OPTIONS --cubical #-}
module CTT.Normal2 where

open import Data.Bool
open import Cubical.Core.Primitives
open import Cubical.Core.Glue

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
  Cne Cne' : CNorm Ne _
  Cnf Cnf' : CNorm Nf _
  Cv Cv' : CVar _
  k k' : Kind

coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
coe p a = transp (λ i → p i) i0 a

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

  -- Eta rules
  n-Πη : nlam (ne (napp (Cne [p]) (ne (nvar vz)))) ≡ ne Cne
  n-elimη : nelim Cne nzero (nsucc (ne (nvar (vs vz)))) ≡ Cne
  

-- data _≈[_]CNf_ : CNf CΓ → CNf CΓ → Set where
--   n-η : ∀ {f} → nlam (ne (napp (np {Ca = Ca} f) (ne (nvar vz)))) ≈[ Cη ]CNf ne f
  
-- record _≡Nf_ (a : CNf CΓ Ca) (b : CNf CΓ Cb) : Set where
--   constructor _over_
--   field
--     p : Ca ≡ Cb
--     np : a ≡[ congruence (CNf CΓ) p ] b
  
-- record _≡Ne_ (a : CNe CΓ Ca) (b : CNe CΓ Cb) : Set where
--   constructor _over_
--   field
--     p : Ca ≡ Cb
--     np : a ≡[ congruence (CNe CΓ) p ] b
    
-- {-# INJECTIVE lam #-}

-- _＝Nf?_ : (a : CNf CΓ Ca) → (b : CNf CΓ Cb) → Dec (a ≡Nf b)
-- nlam a ＝Nf? nlam b with a ＝Nf? b
-- ... | yes (refl over refl) = yes (refl over refl)
-- ... | no ¬p = no λ { (p' over p) → ¬p {!   !} }
-- nlam a ＝Nf? ne x = {!   !}
-- ne x ＝Nf? nlam b = {!   !}
-- ne x ＝Nf? ne x₁ = {!   !}

-- _＝Ne?_ : (a : CNe CΓ Ca) → (b : CNe CΓ Cb) → Dec (a ≡Ne b) 