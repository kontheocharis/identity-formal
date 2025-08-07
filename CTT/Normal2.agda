module CTT.Normal2 where

open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

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
  CΓ CΓ' CΔ : CCon
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


data CNorm where
  ne : CNe CΓ → CNf CΓ
  
  -- Intro
  nlam : CNf (CΓ ▷) → CNf CΓ
  -- nzero : CNf CΓ
  -- nsucc : CNf CΓ → CNf CΓ

  -- Elim
  napp : CNe CΓ → CNf CΓ → CNe CΓ
  nvar : CVar CΓ → CNe CΓ
  -- nelim : CNe CΓ → CNf CΓ → CNf (CΓ ▷ ▷) → CNe CΓ
  
data Thin : CCon → CCon → Set where
  ε : Thin ∙ ∙
  _⁺ : Thin CΓ CΔ → Thin (CΓ ▷) (CΔ ▷)
  _∘p : Thin CΓ CΔ → Thin (CΓ ▷) CΔ

variable
  σ σ' : Thin _ _
  
thin : CVar CΓ → Thin CΔ CΓ → CVar CΔ
thin v (t ∘p) = vs (thin v t)
thin vz (t ⁺) = vz
thin (vs v) (t ⁺) = vs (thin v t)
  
_[_] : CNorm k CΔ → Thin CΓ CΔ → CNorm k CΓ
(ne x) [ σ ] = ne (x [ σ ])
-- nzero [ σ ] = nzero
-- (nsucc x) [ σ ] = nsucc (x [ σ ])
(napp x y) [ σ ] = napp (x [ σ ]) (y [ σ ])
(nvar v) [ σ ] = nvar (thin v σ)
nlam x [ σ ] = nlam (x [ σ ⁺ ])
-- nelim x x₁ x₂ [ σ ] = nelim (x [ σ ]) (x₁ [ σ ]) (x₂ [ (σ ⁺) ⁺ ]) 

id : Thin CΓ CΓ
id {CΓ = ∙} = ε
id {CΓ = CΓ ▷} = id ⁺

p : Thin (CΓ ▷) CΓ
p = id ∘p

thinid : ∀ {v : CVar CΓ} → thin v id ≡ v
thinid {CΓ = CΓ ▷} {v = vz} = refl
thinid {CΓ = CΓ ▷} {v = vs v} = cong vs thinid

thinp≡vs : ∀ {v : CVar CΓ} → thin v p ≡ vs v
thinp≡vs {CΓ = CΓ ▷} {v = vz} = refl
thinp≡vs {CΓ = CΓ ▷} {v = vs v} = cong vs thinp≡vs

Lift : (n : ℕ) → CCon → CCon
Lift zero CΓ = CΓ
Lift (suc n) CΓ = (Lift n CΓ) ▷

lift : (n : ℕ) → Thin CΓ CΔ → Thin (Lift n CΓ) (Lift n CΔ)
lift zero σ = σ
lift (suc n) σ = (lift n σ) ⁺

thin-[thin-lift]-lift-p≡thin-lift-∘p : ∀ {n : ℕ} {CΓ CΔ} {σ : Thin CΓ CΔ} {v : CVar (Lift n CΔ)}
  → thin (thin v (lift n σ)) (lift n p) ≡ thin v (lift n (σ ∘p))
thin-[thin-lift]-lift-p≡thin-lift-∘p {zero} {σ = σ} {v = v} rewrite thinid {v = thin v σ} = refl
thin-[thin-lift]-lift-p≡thin-lift-∘p {suc n} {v = vz} = refl
thin-[thin-lift]-lift-p≡thin-lift-∘p {suc n} {v = vs v} = cong vs thin-[thin-lift]-lift-p≡thin-lift-∘p

[lift][liftp]≡[lift∘p] : ∀ {n : ℕ} {CΓ CΔ} {σ : Thin CΓ CΔ} {z : CNorm k (Lift n CΔ)}
  → z [ lift n σ ] [ lift n p ] ≡ z [ lift n (σ ∘p) ]
[lift][liftp]≡[lift∘p] {z = ne x} = cong ne [lift][liftp]≡[lift∘p]
[lift][liftp]≡[lift∘p] {z = nlam x} = cong nlam [lift][liftp]≡[lift∘p]
[lift][liftp]≡[lift∘p] {z = napp x x₁} = cong₂ napp [lift][liftp]≡[lift∘p] [lift][liftp]≡[lift∘p]
[lift][liftp]≡[lift∘p] {z = nvar x} = cong nvar thin-[thin-lift]-lift-p≡thin-lift-∘p

thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p : ∀ {n : ℕ} {CΓ CΔ} {σ : Thin CΓ CΔ} {v : CVar (Lift n CΔ)}
  → thin (thin v (lift n p)) (lift n (σ ⁺)) ≡ thin (thin v (lift n σ)) (lift n p)
thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {zero} {σ = σ} {v = v}
  rewrite thinid {v = v}
  rewrite thinid {v = thin v σ}
    = refl
thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {suc n} {v = vz} = refl
thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {suc n} {v = vs v} = cong vs thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p

[liftp][lift⁺]≡[lift][liftp] : ∀ {n : ℕ} {CΓ CΔ} {σ : Thin CΓ CΔ} {z : CNorm k (Lift n CΔ)}
  → (z [ lift n p ]) [ lift n (σ ⁺) ] ≡ (z [ lift n σ ]) [ lift n p ]
[liftp][lift⁺]≡[lift][liftp] {z = ne x} = cong ne [liftp][lift⁺]≡[lift][liftp]
[liftp][lift⁺]≡[lift][liftp] {z = nlam x} = cong nlam [liftp][lift⁺]≡[lift][liftp]
[liftp][lift⁺]≡[lift][liftp] {z = napp x x₁} = cong₂ napp [liftp][lift⁺]≡[lift][liftp] [liftp][lift⁺]≡[lift][liftp]
[liftp][lift⁺]≡[lift][liftp] {z = nvar x} = cong nvar thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p

[][p]≡[∘p] : ∀ {σ : Thin CΓ CΔ} → z [ σ ] [ p ] ≡ z [ σ ∘p ]
[][p]≡[∘p] = [lift][liftp]≡[lift∘p]

[p][⁺]≡[][p] : ∀ {σ : Thin CΓ CΔ} → (z [ p ]) [ σ ⁺ ] ≡ (z [ σ ]) [ p ]
[p][⁺]≡[][p] = [liftp][lift⁺]≡[lift][liftp]

data _≈_ where
  -- Congruence
  ne≈ : x ≈ y → ne x ≈ ne y

  nlam≈ : x ≈ y → nlam x ≈ nlam y
  -- nzero≈ : nzero {CΓ = CΓ} ≈ nzero
  -- nsucc≈ : x ≈ y → nsucc x ≈ nsucc y

  napp≈ : x ≈ x' → y ≈ y' → napp x y ≈ napp x' y'
  nvar≈ : v ≡ v' → nvar v ≈ nvar v'
  -- nelim≈ : x ≈ x' → y ≈ y' → z ≈ z' → nelim x y z ≈ nelim x' y' z'

  -- Eta rules
  n-Πη : z ≈ (x [ p ]) → y ≈ ne (napp z (ne (nvar vz))) → nlam y ≈ ne x
  n-Πη-sym : (x [ p ]) ≈ z → ne (napp z (ne (nvar vz))) ≈ y → ne x ≈ nlam y
  -- n-elimη : y ≈ x → z ≈ nzero → z' ≈ nsucc (ne (nvar (vs vz))) → nelim y z z' ≈ x
  -- n-elimη-sym : x ≈ y → nzero ≈ z → nsucc (ne (nvar (vs vz))) ≈ z' → x ≈ nelim y z z'


data ⊥ : Set where

data Dec (X : Set) : Set where
  yes : X → Dec X
  no : (X → ⊥) → Dec X
  
rfl : x ≈ x
rfl {x = ne x} = ne≈ rfl
rfl {x = nlam x} = nlam≈ rfl
-- rfl {x = nzero} = nzero≈
-- rfl {x = nsucc x} = nsucc≈ rfl
rfl {x = napp x x₁} = napp≈ rfl rfl
rfl {x = nvar x} = nvar≈ refl
-- rfl {x = nelim x x₁ x₂} = nelim≈ rfl rfl rfl
  
trivial : z ≡ y → z ≈ y
trivial refl = rfl
  
trs-trivial : z ≈ x → x ≡ y → z ≈ y
trs-trivial q refl = q
  
trivial-trs : z ≡ x → x ≈ y → z ≈ y
trivial-trs refl q = q

symm : x ≈ y → y ≈ x 
symm (ne≈ p) = ne≈ (symm p)
symm (nlam≈ p) = nlam≈ (symm p)
-- symm nzero≈ = nzero≈
-- symm (nsucc≈ p) = nsucc≈ (symm p)
symm (napp≈ p p₁) = napp≈ (symm p) (symm p₁)
symm (nvar≈ x) = nvar≈ (sym x)
-- symm (nelim≈ p p₁ p₂) = nelim≈ (symm p) (symm p₁) (symm p₂)
symm (n-Πη a b) = n-Πη-sym (symm a) (symm b)
symm (n-Πη-sym a b) = n-Πη (symm a) (symm b)
-- symm (n-elimη a b c) = n-elimη-sym (symm a) (symm b) (symm c)
-- symm (n-elimη-sym a b c) = n-elimη (symm a) (symm b) (symm c)

_[_]≈ : x ≈ y → (σ : Thin CΓ CΔ) → (x [ σ ]) ≈ (y [ σ ])
ne≈ p [ σ ]≈ = ne≈ (p [ σ ]≈)
nlam≈ p [ σ ]≈ = nlam≈ (p [ σ ⁺ ]≈)
-- nzero≈ [ σ ]≈ = nzero≈
-- nsucc≈ p [ σ ]≈ = nsucc≈ (p [ σ ]≈)
napp≈ p p₁ [ σ ]≈ = napp≈ (p [ σ ]≈) (p₁ [ σ ]≈)
nvar≈ refl [ σ ]≈ = nvar≈ refl
-- nelim≈ p p₁ p₂ [ σ ]≈ = nelim≈ (p [ σ ]≈) (p₁ [ σ ]≈) (p₂ [ (σ ⁺) ⁺ ]≈)
n-Πη a b [ σ ]≈ = n-Πη (trs-trivial (a [ σ ⁺ ]≈) [p][⁺]≡[][p]) (b [ σ ⁺ ]≈)
n-Πη-sym a b [ σ ]≈ = n-Πη-sym (trivial-trs (sym [p][⁺]≡[][p]) (a [ σ ⁺ ]≈)) (b [ σ ⁺ ]≈)

_[]≈' : ∀ {σ : Thin CΓ CΔ} → (x [ σ ]) ≈ (y [ σ ]) → x ≈ y

trs : x ≈ y → y ≈ z → x ≈ z
trs (ne≈ p₁) (ne≈ q) = ne≈ (trs p₁ q)
trs (ne≈ p₁) (n-Πη-sym x q) = n-Πη-sym (trs (p₁ [ p ]≈) x) q
trs (nlam≈ p₁) (nlam≈ q) = nlam≈ (trs p₁ q)
trs (nlam≈ p₁) (n-Πη y q) = n-Πη y (trs p₁ q)
-- trs nzero≈ nzero≈ = nzero≈
-- trs (nsucc≈ p₁) (nsucc≈ q) = nsucc≈ (trs p₁ q)
trs (napp≈ p₁ p₂) (napp≈ q q₁) = napp≈ (trs p₁ q) (trs p₂ q₁)
-- trs (napp≈ p₁ p₂) (n-elimη-sym q r s) = n-elimη-sym (trs (napp≈ p₁ p₂) q) r s
trs (nvar≈ refl) (nvar≈ refl) = nvar≈ refl
-- trs (nvar≈ x) (n-elimη-sym q r s) = n-elimη-sym (trs (nvar≈ x) q) r s
-- trs (nelim≈ p₁ p₂ p₃) (nelim≈ q q₁ q₂) = nelim≈ (trs p₁ q) (trs p₂ q₁) (trs p₃ q₂)
-- trs (nelim≈ p₁ p₂ p₃) (n-elimη q r s) = n-elimη (trs p₁ q) (trs p₂ r) (trs p₃ s)
-- trs (nelim≈ p₁ p₂ p₃) (n-elimη-sym q r s) = n-elimη-sym (trs (nelim≈ p₁ p₂ p₃) q) r s
trs (n-Πη x q) (ne≈ p₁) = n-Πη (trs x (p₁ [ p ]≈)) q
trs (n-Πη x p₁) (n-Πη-sym y q) = nlam≈ (trs p₁ (trs (ne≈ (napp≈ (trs x y) (ne≈ (nvar≈ refl)))) q))
trs (n-Πη-sym x p₁) (nlam≈ q) = n-Πη-sym x (trs p₁ q)
trs (n-Πη-sym x p₁) (n-Πη y q) = ne≈ ({!   !})
-- trs (n-elimη p₁ p₂ p₃) (napp≈ q q₁) = n-elimη (trs p₁ (napp≈ q q₁)) p₂ p₃
-- trs (n-elimη p₁ p₂ p₃) (nvar≈ x) = n-elimη (trs p₁ (nvar≈ x)) p₂ p₃
-- trs (n-elimη p₁ p₂ p₃) (nelim≈ q q₁ q₂) = n-elimη (trs p₁ (nelim≈ q q₁ q₂)) p₂ p₃
-- trs (n-elimη p₁ p₂ p₃) (n-elimη q q₁ q₂) = n-elimη (trs p₁ (n-elimη q q₁ q₂)) p₂ p₃
-- trs (n-elimη p₁ p₂ p₃) (n-elimη-sym q q₁ q₂) = n-elimη (trs p₁ (n-elimη-sym q q₁ q₂)) p₂ p₃
-- trs (n-elimη-sym p₁ p₂ p₃) (nelim≈ q q₁ q₂) = n-elimη-sym (trs p₁ q) (trs p₂ q₁) (trs p₃ q₂)
-- trs (n-elimη-sym p₁ p₂ p₃) (n-elimη q q₁ q₂) = trs p₁ q
-- trs (n-elimη-sym p₁ p₂ p₃) (n-elimη-sym q q₁ q₂) = n-elimη-sym (trs (n-elimη-sym p₁ p₂ p₃) q) q₁ q₂

-- n-Πη-sym a b [ σ ]≈ = n-Πη-sym {!   !} {!   !}
-- n-elimη a b c [ σ ]≈ = {! n-elimη ?  !}
-- n-elimη-sym a b c [ σ ]≈ = {!  n-elimη  ?  !}

-- trs (ne≈ p) (ne≈ q) = ne≈ (trs p q)
-- trs (ne≈ p) n-Πη-sym = trs n-Πη-sym (nlam≈ (ne≈ (napp≈ (p [p]≈) (ne≈ (nvar≈ refl)))))
-- trs (nlam≈ p) (nlam≈ q) = nlam≈ (trs p q)
-- trs (nlam≈ p) n-Πη = {!   !}
-- trs nzero≈ nzero≈ = nzero≈
-- trs (nsucc≈ p) (nsucc≈ q) = nsucc≈ (trs p q)
-- trs (napp≈ p p₁) (napp≈ q q₁) = napp≈ (trs p q) (trs p₁ q₁)
-- trs (napp≈ p p₁) n-elimη-sym = {!   !}
-- trs (nelim≈ p p₁ p₂) (nelim≈ q q₁ q₂) = nelim≈ (trs p q) (trs p₁ q₁) (trs p₂ q₂)
-- trs (nelim≈ p p₁ p₂) n-elimη = {!   !}
-- trs (nelim≈ p p₁ p₂) n-elimη-sym = {!   !}
-- trs n-Πη (ne≈ q) = {!   !}
-- trs n-Πη n-Πη-sym = {!   !}
-- trs (nvar≈ x) (nvar≈ x₁) = {!   !}
-- trs (nvar≈ x) n-elimη-sym = {!   !}
-- trs n-Πη-sym (nlam≈ q) = {!   !}
-- trs n-Πη-sym n-Πη = {!   !}
-- trs n-elimη (napp≈ q q₁) = {!   !}
-- trs n-elimη (nvar≈ x) = {!   !}
-- trs n-elimη (nelim≈ q q₁ q₂) = {!   !}
-- trs n-elimη n-elimη = {!   !}
-- trs n-elimη n-elimη-sym = {!   !}
-- trs n-elimη-sym (nelim≈ q q₁ q₂) = {!   !}
-- trs n-elimη-sym n-elimη = {!   !}
-- trs n-elimη-sym n-elimη-sym = {!   !}

-- _≡?_ : (a b : CVar CΓ) → Dec (a ≡ b)
-- vz ≡? vz = yes refl
-- (vs i) ≡? (vs i') with i ≡? i'
-- ... | yes refl = yes refl
-- ... | no ¬p = no λ where
--   refl → ¬p refl
-- vz ≡? (vs _) = no λ ()
-- (vs _) ≡? vz = no λ ()

-- _≈?_ : (a : CNorm k CΓ) → (b : CNorm k CΓ) → Dec (a ≈ b)
-- ne x ≈? ne x₁ with x ≈? x₁
-- ... | yes p = yes (ne≈ p)
-- ... | no ¬p = no λ where
--   (ne≈ a) → ¬p a
-- ne x₁ ≈? nlam x with (ne (napp (x₁ [p]) (ne (nvar vz))) ≈? x)
-- ... | yes p = yes (trs n-Πη-sym (nlam≈ p))
-- ... | no ¬p = no λ where
--   n-Πη-sym → ¬p rfl
-- ne x ≈? nzero = no λ ()
-- ne x ≈? nsucc x₁ = no λ ()
-- nlam x ≈? ne x₁ with (x ≈? ne (napp (x₁ [p]) (ne (nvar vz))))
-- ... | yes p = yes (trs (nlam≈ p) n-Πη)
-- ... | no ¬p = no λ where
--   n-Πη → ¬p rfl
-- nlam x ≈? nlam x₁ with x ≈? x₁
-- ... | yes p = yes (nlam≈ p)
-- ... | no ¬p = no λ where
--   (nlam≈ a) → ¬p a
-- nlam x ≈? nzero = no λ ()
-- nlam x ≈? nsucc x₁ = no λ ()
-- nzero ≈? ne x = no λ ()
-- nzero ≈? nlam x = no λ ()
-- nzero ≈? nzero = yes rfl
-- nzero ≈? nsucc x = no λ ()
-- nsucc x ≈? ne x₁ = no λ ()
-- nsucc x ≈? nlam x₁ = no λ ()
-- nsucc x ≈? nzero = no λ ()
-- nsucc x ≈? nsucc x₁ with x ≈? x₁
-- ... | yes p = yes (nsucc≈ p)
-- ... | no ¬p = no λ where
--   (nsucc≈ a) → ¬p a
-- napp x x₁ ≈? napp x₂ x₃ with x ≈? x₂ with x₁ ≈? x₃
-- ... | yes p | yes q = yes (napp≈ p q)
-- ... | _ | no ¬q = no λ where
--   (napp≈ a a₁) → ¬q a₁
-- ... | no ¬p | _ = no λ where
--   (napp≈ a a₁) → ¬p a
-- napp x x₁ ≈? nvar x₂ = no λ ()
-- nvar x ≈? napp x₁ x₂ = no λ ()
-- nvar x ≈? nvar x₁ with x ≡? x₁
-- ... | yes refl = yes (nvar≈ refl)
-- ... | no ¬p = no λ { (nvar≈ x) → ¬p x }
-- -- napp x x₁ ≈? nelim x₂ x₃ x₄ = no λ ()
-- -- nvar x ≈? nelim x₁ x₂ x₃ = no λ ()
-- nelim x x₁ x₂ ≈? x₃
--   with x₃
--   with x ≈? x₃
--   with x₁ ≈? nzero
--   with x₂ ≈? nsucc (ne (nvar (vs vz)))
-- nelim x x₁ x₂ ≈? x₃ | _ | yes p | yes q | yes r = yes (trs (nelim≈ p q r) n-elimη)
-- nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | no ¬p | q | r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
-- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη → ¬p rfl ; n-elimη-sym → ¬p ({!   !}) } 
-- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη → ¬p rfl ; n-elimη-sym → ¬p ({!   !}) } 
-- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη → ¬p rfl ; n-elimη-sym → ¬p ({!   !}) } 
-- nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | p | no ¬q | r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
-- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη → ¬q rfl  ; n-elimη-sym → ¬q ({!   !}) } 
-- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη → ¬q rfl ; n-elimη-sym → ¬q ({!   !}) } 
-- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη → ¬q rfl ; n-elimη-sym → ¬q ({!   !}) } 
-- nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | p | q | no ¬r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
-- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη → ¬r rfl  ; n-elimη-sym → ¬r ({!   !}) } 
-- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη → ¬r rfl ; n-elimη-sym → ¬r ({!   !}) } 
-- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη → ¬r rfl ; n-elimη-sym → ¬r ({!   !}) } 
-- (nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | no ¬p | q | r = no λ { n-elimη → ¬p rfl }
-- (nelim x x₁ x₂ ≈? x₃) | nvar x₄ | no ¬p | q | r = no λ { n-elimη → ¬p rfl }
-- (nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | p | no ¬q | r = no λ { n-elimη → ¬q rfl }
-- (nelim x x₁ x₂ ≈? x₃) | nvar x₄ | p | no ¬q | r = no λ { n-elimη → ¬q rfl }
-- (nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | p | q | no ¬r = no λ { n-elimη → ¬r rfl }
-- (nelim x x₁ x₂ ≈? x₃) | nvar x₄ | p | q | no ¬r = no λ { n-elimη → ¬r rfl }
-- x₃ ≈? nelim x x₁ x₂ 
--   with x₃
--   with x₃ ≈? x 
--   with nzero ≈? x₁
--   with nsucc (ne (nvar (vs vz))) ≈? x₂
-- x₃ ≈? nelim x x₁ x₂ | _ | yes p | yes q | yes r = yes (trs n-elimη-sym (nelim≈ p q r))
-- x₃ ≈? nelim x x₁ x₂ | nelim x' x₁' x₂' | no ¬p | q | r with (x' ≈? x) with (x₁' ≈? x₁) with (x₂' ≈? x₂)
-- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη-sym → ¬p rfl  ; n-elimη → ¬p ({!   !}) } 
-- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη-sym → ¬p rfl ; n-elimη → ¬p ({!   !}) } 
-- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη-sym → ¬p rfl ; n-elimη → ¬p ({!   !}) } 
-- x₃ ≈? nelim x x₁ x₂ | nelim x' x₁' x₂' | p | no ¬q | r with (x' ≈? x) with (x₁' ≈? x₁) with (x₂' ≈? x₂)
-- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη-sym → ¬q rfl  ; n-elimη → ¬q ({!   !}) }   
-- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη-sym → ¬q rfl ; n-elimη → ¬q ({!   !}) }   
-- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη-sym → ¬q rfl ; n-elimη → ¬q ({!   !}) }   
-- x₃ ≈? nelim x x₁ x₂ | nelim x' x₁' x₂' | p | q | no ¬r with (x' ≈? x) with (x₁' ≈? x₁) with (x₂' ≈? x₂)
-- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη-sym → ¬r rfl  ; n-elimη → ¬r ({!   !}) } 
-- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη-sym → ¬r rfl ; n-elimη → ¬r ({!   !}) } 
-- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη-sym → ¬r rfl ; n-elimη → ¬r ({!   !}) } 
-- (x₃ ≈? nelim x x₁ x₂) | napp x₄ x₅ | no ¬p | q | r = no λ { n-elimη-sym → ¬p rfl }
-- (x₃ ≈? nelim x x₁ x₂) | nvar x₄ | no ¬p | q | r = no λ { n-elimη-sym → ¬p rfl }
-- (x₃ ≈? nelim x x₁ x₂) | napp x₄ x₅ | p | no ¬q | r = no λ { n-elimη-sym → ¬q rfl }
-- (x₃ ≈? nelim x x₁ x₂) | nvar x₄ | p | no ¬q | r = no λ { n-elimη-sym → ¬q rfl }
-- (x₃ ≈? nelim x x₁ x₂) | napp x₄ x₅ | p | q | no ¬r = no λ { n-elimη-sym → ¬r rfl }
-- (x₃ ≈? nelim x x₁ x₂) | nvar x₄ | p | q | no ¬r = no λ { n-elimη-sym → ¬r rfl } 