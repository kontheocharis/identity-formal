module CTT.Normal2 where

open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

data Con : Set where
  ∙ : Con
  _▷ : Con → Con

data Kind : Set where
  NeK NfK : Kind

data Skel : Kind → Set
data Norm : (k : Kind) → (Γ : Con) → Skel k → Set
data Var : (Γ : Con) → Set

Ne = Norm NeK
Nf = Norm NfK
  
  
variable
  Γ Γ' Δ : Con
  a a' b b' c c' : Skel _
  x x' y y' z z' : Norm _ _ _
  v v' : Var _
  k k' : Kind

data _~_ : Skel k → Skel k → Set
data _≈[_]_ : Norm k Γ a → a ~ b → Norm k Γ b → Set

coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
coe refl a = a

infix 4 _≡[_]_
_≡[_]_ : ∀ {i} {A B : Set i} → A → A ≡ B → B → Set i
x ≡[ p ] y = coe p x ≡ y

data Var where
  vz : Var (Γ ▷)
  vs : Var Γ → Var (Γ ▷)

data Skel where
  ne : Skel NeK → Skel NfK
  nlam : Skel NfK → Skel NfK
  napp : Skel NeK → Skel NfK → Skel NeK
  nvar : Skel NeK

data _~_ where
  ne~ : a ~ a' → ne a ~ ne a'
  nlam~ : a ~ a' → nlam a ~ nlam a'
  napp~ : a ~ a' → b ~ b' →  napp a b ~ napp a' b'
  nvar~ : nvar ~ nvar

  n-Πη : c ~ a → b ~ ne (napp c (ne nvar)) → nlam b ~ ne a
  n-Πη-sym : a ~ c → ne (napp c (ne nvar)) ~ b → ne a ~ nlam b

data Norm where
  ne : Ne Γ a → Nf Γ (ne a)
  
  -- Intro
  nlam : Nf (Γ ▷) a → Nf Γ (nlam a)
  -- nzero : Nf Γ
  -- nsucc : Nf Γ → Nf Γ

  -- Elim
  napp : Ne Γ a → Nf Γ b → Ne Γ (napp a b)
  nvar : Var Γ → Ne Γ nvar
  -- nelim : Ne Γ → Nf Γ → Nf (Γ ▷ ▷) → Ne Γ
  
data Thin : Con → Con → Set where
  ε : Thin ∙ ∙
  _⁺ : Thin Γ Δ → Thin (Γ ▷) (Δ ▷)
  _∘p : Thin Γ Δ → Thin (Γ ▷) Δ

variable
  σ σ' σ'' : Thin _ _
  
thin : Var Γ → Thin Δ Γ → Var Δ
thin v (t ∘p) = vs (thin v t)
thin vz (t ⁺) = vz
thin (vs v) (t ⁺) = vs (thin v t)
  
_[_] : Norm k Δ a → Thin Γ Δ → Norm k Γ a
(ne x) [ σ ] = ne (x [ σ ])
-- nzero [ σ ] = nzero
-- (nsucc x) [ σ ] = nsucc (x [ σ ])
(napp x y) [ σ ] = napp (x [ σ ]) (y [ σ ])
(nvar v) [ σ ] = nvar (thin v σ)
nlam x [ σ ] = nlam (x [ σ ⁺ ])
-- nelim x x₁ x₂ [ σ ] = nelim (x [ σ ]) (x₁ [ σ ]) (x₂ [ (σ ⁺) ⁺ ]) 

id : Thin Γ Γ
id {Γ = ∙} = ε
id {Γ = Γ ▷} = id ⁺

p : Thin (Γ ▷) Γ
p = id ∘p

thinid : ∀ {v : Var Γ} → thin v id ≡ v
thinid {Γ = Γ ▷} {v = vz} = refl
thinid {Γ = Γ ▷} {v = vs v} = cong vs thinid

thinp≡vs : ∀ {v : Var Γ} → thin v p ≡ vs v
thinp≡vs {Γ = Γ ▷} {v = vz} = refl
thinp≡vs {Γ = Γ ▷} {v = vs v} = cong vs thinp≡vs

Lift : (n : ℕ) → Con → Con
Lift zero Γ = Γ
Lift (suc n) Γ = (Lift n Γ) ▷

lift : (n : ℕ) → Thin Γ Δ → Thin (Lift n Γ) (Lift n Δ)
lift zero σ = σ
lift (suc n) σ = (lift n σ) ⁺

thin-[thin-lift]-lift-p≡thin-lift-∘p : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {v : Var (Lift n Δ)}
  → thin (thin v (lift n σ)) (lift n p) ≡ thin v (lift n (σ ∘p))
thin-[thin-lift]-lift-p≡thin-lift-∘p {zero} {σ = σ} {v = v} rewrite thinid {v = thin v σ} = refl
thin-[thin-lift]-lift-p≡thin-lift-∘p {suc n} {v = vz} = refl
thin-[thin-lift]-lift-p≡thin-lift-∘p {suc n} {v = vs v} = cong vs thin-[thin-lift]-lift-p≡thin-lift-∘p

[lift][liftp]≡[lift∘p] : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {z : Norm k (Lift n Δ) a}
  → z [ lift n σ ] [ lift n p ] ≡ z [ lift n (σ ∘p) ]
[lift][liftp]≡[lift∘p] {z = ne x} = cong ne [lift][liftp]≡[lift∘p]
[lift][liftp]≡[lift∘p] {z = nlam x} = cong nlam [lift][liftp]≡[lift∘p]
[lift][liftp]≡[lift∘p] {z = napp x x₁} = cong₂ napp [lift][liftp]≡[lift∘p] [lift][liftp]≡[lift∘p]
[lift][liftp]≡[lift∘p] {z = nvar x} = cong nvar thin-[thin-lift]-lift-p≡thin-lift-∘p

thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {v : Var (Lift n Δ)}
  → thin (thin v (lift n p)) (lift n (σ ⁺)) ≡ thin (thin v (lift n σ)) (lift n p)
thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {zero} {σ = σ} {v = v}
  rewrite thinid {v = v}
  rewrite thinid {v = thin v σ}
    = refl
thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {suc n} {v = vz} = refl
thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {suc n} {v = vs v} = cong vs thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p

[liftp][lift⁺]≡[lift][liftp] : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {z : Norm k (Lift n Δ) a}
  → (z [ lift n p ]) [ lift n (σ ⁺) ] ≡ (z [ lift n σ ]) [ lift n p ]
[liftp][lift⁺]≡[lift][liftp] {z = ne x} = cong ne [liftp][lift⁺]≡[lift][liftp]
[liftp][lift⁺]≡[lift][liftp] {z = nlam x} = cong nlam [liftp][lift⁺]≡[lift][liftp]
[liftp][lift⁺]≡[lift][liftp] {z = napp x x₁} = cong₂ napp [liftp][lift⁺]≡[lift][liftp] [liftp][lift⁺]≡[lift][liftp]
[liftp][lift⁺]≡[lift][liftp] {z = nvar x} = cong nvar thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p

[][p]≡[∘p] : ∀ {σ : Thin Γ Δ} → z [ σ ] [ p ] ≡ z [ σ ∘p ]
[][p]≡[∘p] = [lift][liftp]≡[lift∘p]

[p][⁺]≡[][p] : ∀ {σ : Thin Γ Δ} → (z [ p ]) [ σ ⁺ ] ≡ (z [ σ ]) [ p ]
[p][⁺]≡[][p] = [liftp][lift⁺]≡[lift][liftp]

[id] : z [ id ] ≡ z
[id] {z = ne x} = cong ne [id]
[id] {z = nlam x} = cong nlam [id]
[id] {z = napp x x₁} = cong₂ napp [id] [id]
[id] {z = nvar x} = cong nvar (thinid)

variable
  i j : _ ~ _

data _≈[_]_ where
  -- Congruence
  ne≈ : x ≈[ i ] y → ne x ≈[ ne~ i ] ne y 

  nlam≈ : x ≈[ i ] y → nlam x ≈[ nlam~ i ] nlam y
  -- nzero≈ : nzero {Γ = Γ} ≈ nzero
  -- nsucc≈ : x ≈ y → nsucc x ≈ nsucc y

  napp≈ : x ≈[ i ] x' → y ≈[ j ] y' → napp x y ≈[ napp~ i j ] napp x' y'
  nvar≈ : v ≡ v' → nvar v ≈[ nvar~ ] nvar v'
  -- nelim≈ : x ≈ x' → y ≈ y' → z ≈ z' → nelim x y z ≈ nelim x' y' z'

  -- Eta rules
  n-Πη : z ≈[ i ] (x [ p ]) → y ≈[ j ] ne (napp z (ne (nvar vz))) → nlam y ≈[ n-Πη i j ] ne x
  n-Πη-sym : (x [ p ]) ≈[ i ] z → ne (napp z (ne (nvar vz))) ≈[ j ] y → ne x ≈[ n-Πη-sym i j ] nlam y
  -- n-elimη : y ≈ x → z ≈ nzero → z' ≈ nsucc (ne (nvar (vs vz))) → nelim y z z' ≈ x
  -- n-elimη-sym : x ≈ y → nzero ≈ z → nsucc (ne (nvar (vs vz))) ≈ z' → x ≈ nelim y z z'

variable
  f g h : _ ≈[ _ ] _

data ⊥ : Set where

data Dec (X : Set) : Set where
  yes : X → Dec X
  no : (X → ⊥) → Dec X
  
rfl~ : a ~ a
rfl~ {a = ne a} = ne~ rfl~
rfl~ {a = nlam a} = nlam~ rfl~
rfl~ {a = napp a a₁} = napp~ rfl~ rfl~
rfl~ {a = nvar} = nvar~

rfl : x ≈[ rfl~ ] x
rfl {x = ne x} = ne≈ rfl
rfl {x = nlam x} = nlam≈ rfl
-- rfl {x = nzero} = nzero≈
-- rfl {x = nsucc x} = nsucc≈ rfl
rfl {x = napp x x₁} = napp≈ rfl rfl
rfl {x = nvar x} = nvar≈ refl
-- rfl {x = nelim x x₁ x₂} = nelim≈ rfl rfl rfl
  
-- trivial : z ≡ y → z ≈[ rfl~ ] y
-- trivial refl = rfl
  
-- trs-trivial : z ≈[ i ] x → x ≡ y → z ≈[ i ] y
-- trs-trivial q refl = q
  
-- trivial-trs : z ≡ x → x ≈[ i ] y → z ≈[ i ] y
-- trivial-trs refl q = q

-- symm~ : a ~ b → b ~ a
-- symm~ (ne~ p₁) = ne~ (symm~ p₁)
-- symm~ (nlam~ p₁) = nlam~ (symm~ p₁)
-- symm~ (napp~ p₁ p₂) = napp~ (symm~ p₁) (symm~ p₂)
-- symm~ nvar~ = nvar~
-- symm~ (n-Πη p₁ p₂) = n-Πη-sym (symm~ p₁) (symm~ p₂)
-- symm~ (n-Πη-sym p₁ p₂) = n-Πη (symm~ p₁) (symm~ p₂)

-- symm : x ≈[ i ] y → y ≈[ symm~ i ] x 
-- symm (ne≈ p) = ne≈ (symm p)
-- symm (nlam≈ p) = nlam≈ (symm p)
-- -- symm nzero≈ = nzero≈
-- -- symm (nsucc≈ p) = nsucc≈ (symm p)
-- symm (napp≈ p p₁) = napp≈ (symm p) (symm p₁)
-- symm (nvar≈ x) = nvar≈ (sym x)
-- -- symm (nelim≈ p p₁ p₂) = nelim≈ (symm p) (symm p₁) (symm p₂)
-- symm (n-Πη a b) = n-Πη-sym (symm a) (symm b)
-- symm (n-Πη-sym a b) = n-Πη (symm a) (symm b)
-- -- symm (n-elimη a b c) = n-elimη-sym (symm a) (symm b) (symm c)
-- -- symm (n-elimη-sym a b c) = n-elimη (symm a) (symm b) (symm c)

-- _[_]≈ : x ≈[ i ] y → (σ : Thin Γ Δ) → (x [ σ ]) ≈[ i ] (y [ σ ])
-- ne≈ p [ σ ]≈ = ne≈ (p [ σ ]≈)
-- nlam≈ p [ σ ]≈ = nlam≈ (p [ σ ⁺ ]≈)
-- -- nzero≈ [ σ ]≈ = nzero≈
-- -- nsucc≈ p [ σ ]≈ = nsucc≈ (p [ σ ]≈)
-- napp≈ p p₁ [ σ ]≈ = napp≈ (p [ σ ]≈) (p₁ [ σ ]≈)
-- nvar≈ refl [ σ ]≈ = nvar≈ refl
-- -- nelim≈ p p₁ p₂ [ σ ]≈ = nelim≈ (p [ σ ]≈) (p₁ [ σ ]≈) (p₂ [ (σ ⁺) ⁺ ]≈)
-- n-Πη a b [ σ ]≈ = n-Πη (trs-trivial (a [ σ ⁺ ]≈) [p][⁺]≡[][p]) (b [ σ ⁺ ]≈)
-- n-Πη-sym a b [ σ ]≈ = n-Πη-sym (trivial-trs (sym [p][⁺]≡[][p]) (a [ σ ⁺ ]≈)) (b [ σ ⁺ ]≈)

-- vs-inj : vs v ≡ vs v' → v ≡ v'
-- vs-inj refl = refl

-- thin≡ : ∀ {Δ} {v} {σ : Thin Γ Δ} {v'} → thin v σ ≡ thin v' σ → v ≡ v'
-- thin≡ {v = vz} {v' = vz} p = refl
-- thin≡ {Γ = Γ ▷} {Δ = Δ ▷} {v = vz} {σ ∘p} {v' = vs v'} p = thin≡ (vs-inj p)
-- thin≡ {Γ = Γ ▷} {Δ = Δ ▷} {v = vs v} {σ ∘p} {v' = vz} p = thin≡ (vs-inj p)
-- thin≡ {v = vs v} {σ = σ ⁺} {v' = vs v'} p = cong vs (thin≡ (vs-inj p))
-- thin≡ {v = vs v} {σ = σ ∘p} {v' = vs v'} p = thin≡ (vs-inj p)

-- -- data ~-eqns : (n : ℕ) → Skel → Skel → Set where
-- --   done : ~-eqns zero a a
-- --   cont : ∀ {n} → ~-eqns n a b → b ~ c → ~-eqns (suc n) a c
  
-- -- trsN~ : (n : ℕ) → ~-eqns n a b → a ~ b

-- -- trs~ p q = trsN~ (suc (suc zero)) (cont (cont done p) q)

-- -- trsN~ zero done = rfl~
-- -- trsN~ (suc n) (cont p₁ (ne~ x)) with trsN~ n p₁
-- -- ... | ne~ r = ne~ (trs~ r x)
-- -- ... | n-Πη r r₁ = n-Πη x (trs~ r₁ (ne~ (napp~ r (ne~ nvar~))))
-- -- trsN~ (suc n) (cont p₁ (nlam~ x)) with trsN~ n p₁
-- -- ... | nlam~ r = nlam~ (trs~ r x)
-- -- ... | n-Πη-sym r r₁ = n-Πη-sym r (trs~ r₁ x)
-- -- trsN~ (suc n) (cont p₁ (napp~ x x₁)) with trsN~ n p₁
-- -- ... | napp~ r r₁ = napp~ (trs~ r x) (trs~ r₁ x₁)
-- -- trsN~ (suc n) (cont p₁ nvar~) with trsN~ n p₁
-- -- ... | nvar~ = nvar~
-- -- trsN~ (suc n) (cont p₁ (n-Πη x x₁)) with trsN~ n p₁
-- -- ... | nlam~ r = {!   !}
-- -- ... | n-Πη-sym r r₁ = {!   !}
-- -- trsN~ (suc n) (cont p₁ (n-Πη-sym x x₁)) with trsN~ n p₁
-- -- ... | ne~ r = {!   !}
-- -- ... | n-Πη r r₁ = {!   !}

-- -- trsNe~ : ∀ {a b c : Skel NeK} → a ~ b → b ~ c → a ~ c
-- -- trsNe~ (napp~ p₁ p₂) (napp~ q q₁) = napp~ (trsNe~ p₁ q) (trsNf~ p₂ q₁)
-- -- trsNe~ nvar~ nvar~ = nvar~

-- -- trsNf~ (ne~ p₁) (ne~ q) = ne~ (trsNe~ p₁ q)
-- -- trsNf~ (ne~ p₁) (n-Πη-sym q q₁) = n-Πη-sym p₁ (trsNf~ (ne~ (napp~ q (ne~ nvar~))) q₁)
-- -- trsNf~ (nlam~ p₁) (nlam~ q) = {!   !}
-- -- trsNf~ (nlam~ p₁) (n-Πη q q₁) = {!   !}
-- -- trsNf~ (n-Πη p₁ p₂) (ne~ q) = {!   !}
-- -- trsNf~ (n-Πη p₁ p₂) (n-Πη-sym q q₁) = {!   !}
-- -- trsNf~ (n-Πη-sym p₁ p₂) (nlam~ q) = {!   !}
-- -- trsNf~ (n-Πη-sym p₁ p₂) (n-Πη q q₁) = {!   !}

trs~ : a ~ b → b ~ c → a ~ c
trs~ (ne~ p₁) (ne~ q) = ne~ (trs~ p₁ q)
trs~ (ne~ p₁) (n-Πη-sym q q₁) = n-Πη-sym (trs~ p₁ q) q₁
trs~ (nlam~ p₁) (nlam~ q) = nlam~ (trs~ p₁ q)
trs~ (nlam~ p₁) (n-Πη q q₁) = n-Πη q (trs~ p₁ q₁)
trs~ (napp~ p₁ p₂) (napp~ q q₁) = napp~ (trs~ p₁ q) (trs~ p₂ q₁)
trs~ nvar~ nvar~ = nvar~
trs~ (n-Πη p₁ p₂) (ne~ q) = n-Πη (trs~ p₁ q) p₂
trs~ (n-Πη p₁ p₂) (n-Πη-sym q q₁) = nlam~ ({!   !})
trs~ (n-Πη-sym p₁ p₂) (nlam~ q) = n-Πη-sym p₁ (trs~ p₂ q)
trs~ (n-Πη-sym p₁ p₂) (n-Πη q q₁) = {!   !}


-- trs~ (ne~ p₁) (ne~ q) = ne~ (trs~ p₁ q)
-- trs~ (ne~ p₁) (n-Πη-sym q q₁) = n-Πη-sym (trs~ p₁ q) q₁
-- trs~ (nlam~ p₁) (nlam~ q) = nlam~ (trs~ p₁ q)
-- trs~ (nlam~ p₁) (n-Πη q q₁) = n-Πη q (trs~ p₁ q₁)
-- trs~ (napp~ p₁ p₂) (napp~ q q₁) = napp~ (trs~ p₁ q) (trs~ p₂ q₁)
-- trs~ nvar~ nvar~ = nvar~
-- trs~ (n-Πη p₁ p₂) (ne~ q) = n-Πη (trs~ p₁ q) p₂
-- trs~ (n-Πη p₁ p₂) (n-Πη-sym q q₁) with trs~ p₁ q 
-- ... | napp~ r r₁ = nlam~ (trs~ p₂ ({!   !}))
-- ... | nvar~ = nlam~ (trs~ p₂ q₁)
-- trs~ (n-Πη-sym p₁ p₂) (nlam~ q) = n-Πη-sym p₁ (trs~ p₂ q)
-- trs~ (n-Πη-sym p₁ p₂) (n-Πη q q₁) = {!   !}
-- -- ... | ne~ (napp~ r r₁) = ne~ (trs~ (trs~ p₁ r) q)

-- -- trs : x ≈[ i ] y → y ≈[ j ] z → x ≈[ trs~ i j ] z
-- -- trs (ne≈ p₁) (ne≈ q) = ne≈ (trs p₁ q)
-- -- trs (ne≈ p₁) (n-Πη-sym q q₁) = n-Πη-sym (trs (p₁ [ p ]≈) q) q₁
-- -- trs (nlam≈ p₁) (nlam≈ q) = nlam≈ (trs p₁ q)
-- -- trs (nlam≈ p₁) (n-Πη q q₁) = n-Πη q (trs p₁ q₁)
-- -- trs (napp≈ p₁ p₂) (napp≈ q q₁) = napp≈ (trs p₁ q) (trs p₂ q₁)
-- -- trs (nvar≈ x) (nvar≈ x₁) = nvar≈ (trans x x₁)
-- -- trs (n-Πη p₁ p₂) (ne≈ q) = n-Πη (trs p₁ (q [ p ]≈)) p₂
-- -- trs (n-Πη p₁ p₂) (n-Πη-sym q q₁) = nlam≈ (trs (trs p₂ (ne≈ (napp≈ (trs p₁ q) (ne≈ (nvar≈ refl))))) q₁)
-- -- trs (n-Πη-sym p₁ p₂) (nlam≈ q) = n-Πη-sym p₁ (trs p₂ q)
-- -- trs (n-Πη-sym p₁ p₂) (n-Πη q q₁) = ne≈ {!   !}

-- -- -- _[]≈' : ∀ {σ : Thin Γ Δ} → (x [ σ ]) ≈ (y [ σ ]) → x ≈ y
-- -- -- _[]≈' {x = ne x} {y = ne x₁} (ne≈ t) = ne≈ (t []≈')
-- -- -- _[]≈' {x = ne x} {y = nlam x₁} (n-Πη-sym t t₁) =
-- -- --   n-Πη-sym ({!   !}) ({!  t₁ []≈' !})
-- -- -- _[]≈' {x = nlam x} {y = ne x₁} (n-Πη t t₁) = {!   !}
-- -- -- _[]≈' {x = nlam x} {y = nlam x₁} (nlam≈ t) = nlam≈ (t []≈')
-- -- -- _[]≈' {x = napp x x₁} {y = napp x₂ x₃} (napp≈ t t₁) = napp≈ (t []≈') (t₁ []≈')
-- -- -- _[]≈' {x = napp x x₁} {y = nvar x₂} ()
-- -- -- _[]≈' {x = nvar x} {y = napp x₁ x₂} ()
-- -- -- _[]≈' {x = nvar x} {y = nvar x₁} (nvar≈ x₂) = nvar≈ (thin≡ x₂)

-- -- -- _[∘p]≈ : (x [ σ ]) ≈ (x' [ σ' ]) → x [ σ ∘p ] ≈ 

-- -- -- data _[_]≈R : x ≈ y → (σ : Thin Γ Δ) → Set where
-- -- --   ne≈R : 
-- -- --   nlam≈ p [ σ ]≈ = nlam≈ (p [ σ ⁺ ]≈)
-- -- --   -- nzero≈ [ σ ]≈ = nzero≈
-- -- --   -- nsucc≈ p [ σ ]≈ = nsucc≈ (p [ σ ]≈)
-- -- --   napp≈ p p₁ [ σ ]≈ = napp≈ (p [ σ ]≈) (p₁ [ σ ]≈)
-- -- --   nvar≈ refl [ σ ]≈ = nvar≈ refl
-- -- --   -- nelim≈ p p₁ p₂ [ σ ]≈ = nelim≈ (p [ σ ]≈) (p₁ [ σ ]≈) (p₂ [ (σ ⁺) ⁺ ]≈)
-- -- --   n-Πη a b [ σ ]≈ = n-Πη (trs-trivial (a [ σ ⁺ ]≈) [p][⁺]≡[][p]) (b [ σ ⁺ ]≈)
-- -- --   n-Πη-sym a b [ σ ]≈ = n-Πη-sym (trivial-trs (sym [p][⁺]≡[][p]) (a [ σ ⁺ ]≈)) (b [ σ ⁺ ]≈)

-- -- data _≈'_ : (x : Norm k Γ) → (y : Norm k Γ) → Set

-- -- variable
-- --     q r : _ ≈ _
-- --     q' r' : _ ≈' _

-- -- data _≈'_ where
-- --   rfl' : x ≈' x
-- --   symm' : x ≈' y → y ≈' x

-- --   -- Congruence
-- --   ne≈ : x ≈' y → ne x ≈' ne y

-- --   nlam≈ : x ≈' y → nlam x ≈' nlam y
-- --   -- nzero≈[ ? ] : nzero {Γ = Γ} ≈[ ? ] nzero
-- --   -- nsucc≈[ ? ] : x ≈[ ? ] y → nsucc x ≈[ ? ] nsucc y

-- --   napp≈ : x ≈' x' → y ≈' y' → napp x y ≈' napp x' y'
-- --   nvar≈ : (p : v ≡ v') → nvar v ≈' nvar v'
-- --   -- nelim≈[ ? ] : x ≈[ ? ] x' → y ≈[ ? ] y' → z ≈[ ? ] z' → nelim x y z ≈[ ? ] nelim x' y' z'

-- --   -- Eta rules
-- --   n-Πη : z ≈' (x [ p ]) → y ≈' ne (napp z (ne (nvar vz))) → nlam y ≈' ne x
-- --   n-Πη-sym : (x [ p ]) ≈' z → ne (napp z (ne (nvar vz))) ≈' y → ne x ≈' nlam y
  
-- --   _[_]≈' : x ≈' y → (σ : Thin Γ Δ) → x' ≈' (x [ σ ]) → y' ≈' (y [ σ ]) → x' ≈' y'
-- --   -- n-elimη : y ≈[ ? ] x → z ≈[ ? ] nzero → z' ≈[ ? ] nsucc (ne (nvar (vs vz))) → nelim y z z' ≈[ ? ] x
-- --   -- n-elimη-sym : x ≈[ ? ] y → nzero ≈[ ? ] z → nsucc (ne (nvar (vs vz))) ≈[ ? ] z' → x ≈[ ? ] nelim y z z'
  
-- -- -- proj : x ≈' y → x ≈ y
-- -- -- proj rfl' = rfl
-- -- -- proj (symm' q) = symm (proj q)
-- -- -- proj (ne≈ q) = ne≈ (proj q)
-- -- -- proj (nlam≈ q) = nlam≈ (proj q)
-- -- -- proj (napp≈ q q₁) = napp≈ (proj q) (proj q₁)
-- -- -- proj (nvar≈ p₁) = nvar≈ p₁
-- -- -- proj (n-Πη q q₁) = n-Πη (proj q) (proj q₁)
-- -- -- proj (n-Πη-sym q q₁) = n-Πη-sym (proj q) (proj q₁)
-- -- -- proj ((q [ σ ]≈') q₁ q₂) = {!  ? [ ? ]≈ !}

-- -- view : x ≈ y → x ≈' y
-- -- view (ne≈ m) = ne≈ (view m)
-- -- view (nlam≈ m) = nlam≈ (view m)
-- -- view (napp≈ m m₁) = napp≈ (view m) (view m₁)
-- -- view (nvar≈ x) = nvar≈ x
-- -- view (n-Πη m m₁) = n-Πη (view m) (view m₁)
-- -- view (n-Πη-sym m m₁) = n-Πη-sym (view m) (view m₁)
  
-- -- rfl' : x ≈' x
-- -- rfl' {x = ne x} = ne≈ rfl'
-- -- rfl' {x = nlam x} = nlam≈ rfl'
-- -- rfl' {x = napp x x₁} = napp≈ rfl' rfl'
-- -- rfl' {x = nvar x} = nvar≈ refl

-- -- sym' : x ≈' y → y ≈' x


-- -- trs' : x ≈' y → y ≈' z → x ≈' z
-- -- trs' (ne≈ p₁) (ne≈ q) = ne≈ (trs' p₁ q)
-- -- trs' (ne≈ p₁) (n-Πη-sym q x) = n-Πη-sym (trs' ((p₁ [ p ]≈') rfl' rfl') q) x
-- -- trs' (ne≈ p₁) ((ne≈ q [ σ ]≈') r₁ r₂) = {!   !}
-- -- trs' (ne≈ p₁) ((nlam≈ q [ σ ]≈') r₁ r₂) = {!   !}
-- -- trs' (ne≈ p₁) ((n-Πη q q₁ [ σ ]≈') r₁ r₂) = {!   !}
-- -- trs' (ne≈ p₁) ((n-Πη-sym q q₁ [ σ ]≈') r₁ r₂) = {!   !}
-- -- trs' (ne≈ p₁) (((q [ σ₁ ]≈') q₁ q₂ [ σ ]≈') r₁ r₂) = {!   !}
-- -- trs' (nlam≈ p₁) (nlam≈ q) = nlam≈ (trs' p₁ q)
-- -- trs' (nlam≈ p₁) (n-Πη q x) = n-Πη q (trs' p₁ x)
-- -- trs' (nlam≈ p₁) ((q [ σ ]≈') x x₁) = {!   !}
-- -- trs' (napp≈ p₁ p₂) (napp≈ q q₁) = napp≈ (trs' p₁ q) (trs' p₂ q₁)
-- -- trs' (napp≈ p₁ p₂) ((q [ σ ]≈') x x₁) = {!   !}
-- -- trs' (nvar≈ p₁) (nvar≈ p₂) = nvar≈ (trans p₁ p₂)
-- -- trs' (nvar≈ p₁) ((q [ σ ]≈') x x₁) = {! !}
-- -- trs' (n-Πη p₁ x) (ne≈ q) = n-Πη ((q [ p ]≈') {!   !} {!   !}) x
-- -- trs' (n-Πη p₁ x) (n-Πη-sym q x₁) = {!   !}
-- -- trs' (n-Πη p₁ x) ((q [ σ ]≈') x₁ x₂) = {!   !}
-- -- trs' (n-Πη-sym p₁ x) (nlam≈ q) = {!   !}
-- -- trs' (n-Πη-sym p₁ x) (n-Πη q x₁) = {!   !}
-- -- trs' (n-Πη-sym p₁ x) ((q [ σ ]≈') x₁ x₂) = {!   !}
-- -- trs' ((p₁ [ σ ]≈') x x₁) (ne≈ q) = {!   !}
-- -- trs' ((p₁ [ σ ]≈') x x₁) (nlam≈ q) = {!   !}
-- -- trs' ((p₁ [ σ ]≈') x x₁) (napp≈ q q₁) = {!   !}
-- -- trs' ((p₁ [ σ ]≈') x x₁) (nvar≈ p₂) = {!   !}
-- -- trs' ((p₁ [ σ ]≈') x x₁) (n-Πη q x₂) = {!   !}
-- -- trs' ((p₁ [ σ ]≈') x x₁) (n-Πη-sym q x₂) = {!   !}
-- -- trs' ((p₁ [ σ ]≈') x x₁) ((q [ σ₁ ]≈') x₂ x₃) = {!   !}


-- -- trs {r = ne≈ r} {q = ne≈ q} ar aq = ne≈ (trs (view r) (view q))
-- -- trs {r = n-Πη r r₁} {q = ne≈ q} ar aq = {!   !}
-- -- trs {r = nlam≈ r} {q = nlam≈ q} ar aq = {!   !}
-- -- trs {r = n-Πη-sym r r₁} {q = nlam≈ q} ar aq = {!   !}
-- -- trs {r = napp≈ r r₁} {q = napp≈ q q₁} ar aq = {!   !}
-- -- trs {r = nvar≈ x} {q = nvar≈ x₁} ar aq = {!   !}
-- -- trs {r = nlam≈ r} {q = n-Πη q q₁} ar aq = {!   !}
-- -- trs {r = n-Πη-sym r r₁} {q = n-Πη q q₁} ar aq = {!   !}
-- -- trs {r = ne≈ r} {q = n-Πη-sym q q₁} ar aq = {!   !}
-- -- trs {r = n-Πη r r₁} {q = n-Πη-sym q q₁} ar aq = {!   !}

-- -- trs (ne≈ p₁) (ne≈ q) = ne≈ (trs p₁ q)
-- -- trs (ne≈ p₁) (n-Πη-sym x q) = n-Πη-sym ({!   !}) q
-- -- trs (nlam≈ p₁) (nlam≈ q) = nlam≈ (trs p₁ q)
-- -- trs (nlam≈ p₁) (n-Πη y q) = n-Πη y (trs p₁ q)
-- -- -- trs nzero≈ nzero≈ = nzero≈
-- -- -- trs (nsucc≈ p₁) (nsucc≈ q) = nsucc≈ (trs p₁ q)
-- -- trs (napp≈ p₁ p₂) (napp≈ q q₁) = napp≈ (trs p₁ q) (trs p₂ q₁)
-- -- -- trs (napp≈ p₁ p₂) (n-elimη-sym q r s) = n-elimη-sym (trs (napp≈ p₁ p₂) q) r s
-- -- trs (nvar≈ refl) (nvar≈ refl) = nvar≈ refl
-- -- -- trs (nvar≈ x) (n-elimη-sym q r s) = n-elimη-sym (trs (nvar≈ x) q) r s
-- -- -- trs (nelim≈ p₁ p₂ p₃) (nelim≈ q q₁ q₂) = nelim≈ (trs p₁ q) (trs p₂ q₁) (trs p₃ q₂)
-- -- -- trs (nelim≈ p₁ p₂ p₃) (n-elimη q r s) = n-elimη (trs p₁ q) (trs p₂ r) (trs p₃ s)
-- -- -- trs (nelim≈ p₁ p₂ p₃) (n-elimη-sym q r s) = n-elimη-sym (trs (nelim≈ p₁ p₂ p₃) q) r s
-- -- trs (n-Πη x q) (ne≈ p₁) = n-Πη (trs x ({!   !})) q
-- -- trs (n-Πη x p₁) (n-Πη-sym y q) = nlam≈ (trs p₁ (trs (ne≈ (napp≈ (trs x y) (ne≈ (nvar≈ refl)))) q))
-- -- trs (n-Πη-sym x p₁) (nlam≈ q) = n-Πη-sym x (trs p₁ q)
-- -- trs (n-Πη-sym x p₁) (n-Πη y q) = ne≈ ({!   !})
-- -- trs (n-elimη p₁ p₂ p₃) (napp≈ q q₁) = n-elimη (trs p₁ (napp≈ q q₁)) p₂ p₃
-- -- trs (n-elimη p₁ p₂ p₃) (nvar≈ x) = n-elimη (trs p₁ (nvar≈ x)) p₂ p₃
-- -- trs (n-elimη p₁ p₂ p₃) (nelim≈ q q₁ q₂) = n-elimη (trs p₁ (nelim≈ q q₁ q₂)) p₂ p₃
-- -- trs (n-elimη p₁ p₂ p₃) (n-elimη q q₁ q₂) = n-elimη (trs p₁ (n-elimη q q₁ q₂)) p₂ p₃
-- -- trs (n-elimη p₁ p₂ p₃) (n-elimη-sym q q₁ q₂) = n-elimη (trs p₁ (n-elimη-sym q q₁ q₂)) p₂ p₃
-- -- trs (n-elimη-sym p₁ p₂ p₃) (nelim≈ q q₁ q₂) = n-elimη-sym (trs p₁ q) (trs p₂ q₁) (trs p₃ q₂)
-- -- trs (n-elimη-sym p₁ p₂ p₃) (n-elimη q q₁ q₂) = trs p₁ q
-- -- trs (n-elimη-sym p₁ p₂ p₃) (n-elimη-sym q q₁ q₂) = n-elimη-sym (trs (n-elimη-sym p₁ p₂ p₃) q) q₁ q₂

-- -- n-Πη-sym a b [ σ ]≈ = n-Πη-sym {!   !} {!   !}
-- -- n-elimη a b c [ σ ]≈ = {! n-elimη ?  !}
-- -- n-elimη-sym a b c [ σ ]≈ = {!  n-elimη  ?  !}

-- -- trs (ne≈ p) (ne≈ q) = ne≈ (trs p q)
-- -- trs (ne≈ p) n-Πη-sym = trs n-Πη-sym (nlam≈ (ne≈ (napp≈ (p [p]≈) (ne≈ (nvar≈ refl)))))
-- -- trs (nlam≈ p) (nlam≈ q) = nlam≈ (trs p q)
-- -- trs (nlam≈ p) n-Πη = {!   !}
-- -- trs nzero≈ nzero≈ = nzero≈
-- -- trs (nsucc≈ p) (nsucc≈ q) = nsucc≈ (trs p q)
-- -- trs (napp≈ p p₁) (napp≈ q q₁) = napp≈ (trs p q) (trs p₁ q₁)
-- -- trs (napp≈ p p₁) n-elimη-sym = {!   !}
-- -- trs (nelim≈ p p₁ p₂) (nelim≈ q q₁ q₂) = nelim≈ (trs p q) (trs p₁ q₁) (trs p₂ q₂)
-- -- trs (nelim≈ p p₁ p₂) n-elimη = {!   !}
-- -- trs (nelim≈ p p₁ p₂) n-elimη-sym = {!   !}
-- -- trs n-Πη (ne≈ q) = {!   !}
-- -- trs n-Πη n-Πη-sym = {!   !}
-- -- trs (nvar≈ x) (nvar≈ x₁) = {!   !}
-- -- trs (nvar≈ x) n-elimη-sym = {!   !}
-- -- trs n-Πη-sym (nlam≈ q) = {!   !}
-- -- trs n-Πη-sym n-Πη = {!   !}
-- -- trs n-elimη (napp≈ q q₁) = {!   !}
-- -- trs n-elimη (nvar≈ x) = {!   !}
-- -- trs n-elimη (nelim≈ q q₁ q₂) = {!   !}
-- -- trs n-elimη n-elimη = {!   !}
-- -- trs n-elimη n-elimη-sym = {!   !}
-- -- trs n-elimη-sym (nelim≈ q q₁ q₂) = {!   !}
-- -- trs n-elimη-sym n-elimη = {!   !}
-- -- trs n-elimη-sym n-elimη-sym = {!   !}

-- -- _≡?_ : (a b : Var Γ) → Dec (a ≡ b)
-- -- vz ≡? vz = yes refl
-- -- (vs i) ≡? (vs i') with i ≡? i'
-- -- ... | yes refl = yes refl
-- -- ... | no ¬p = no λ where
-- --   refl → ¬p refl
-- -- vz ≡? (vs _) = no λ ()
-- -- (vs _) ≡? vz = no λ ()

-- -- _≈?_ : (a : Norm k Γ) → (b : Norm k Γ) → Dec (a ≈ b)
-- -- ne x ≈? ne x₁ with x ≈? x₁
-- -- ... | yes p = yes (ne≈ p)
-- -- ... | no ¬p = no λ where
-- --   (ne≈ a) → ¬p a
-- -- ne x₁ ≈? nlam x with (ne (napp (x₁ [p]) (ne (nvar vz))) ≈? x)
-- -- ... | yes p = yes (trs n-Πη-sym (nlam≈ p))
-- -- ... | no ¬p = no λ where
-- --   n-Πη-sym → ¬p rfl
-- -- ne x ≈? nzero = no λ ()
-- -- ne x ≈? nsucc x₁ = no λ ()
-- -- nlam x ≈? ne x₁ with (x ≈? ne (napp (x₁ [p]) (ne (nvar vz))))
-- -- ... | yes p = yes (trs (nlam≈ p) n-Πη)
-- -- ... | no ¬p = no λ where
-- --   n-Πη → ¬p rfl
-- -- nlam x ≈? nlam x₁ with x ≈? x₁
-- -- ... | yes p = yes (nlam≈ p)
-- -- ... | no ¬p = no λ where
-- --   (nlam≈ a) → ¬p a
-- -- nlam x ≈? nzero = no λ ()
-- -- nlam x ≈? nsucc x₁ = no λ ()
-- -- nzero ≈? ne x = no λ ()
-- -- nzero ≈? nlam x = no λ ()
-- -- nzero ≈? nzero = yes rfl
-- -- nzero ≈? nsucc x = no λ ()
-- -- nsucc x ≈? ne x₁ = no λ ()
-- -- nsucc x ≈? nlam x₁ = no λ ()
-- -- nsucc x ≈? nzero = no λ ()
-- -- nsucc x ≈? nsucc x₁ with x ≈? x₁
-- -- ... | yes p = yes (nsucc≈ p)
-- -- ... | no ¬p = no λ where
-- --   (nsucc≈ a) → ¬p a
-- -- napp x x₁ ≈? napp x₂ x₃ with x ≈? x₂ with x₁ ≈? x₃
-- -- ... | yes p | yes q = yes (napp≈ p q)
-- -- ... | _ | no ¬q = no λ where
-- --   (napp≈ a a₁) → ¬q a₁
-- -- ... | no ¬p | _ = no λ where
-- --   (napp≈ a a₁) → ¬p a
-- -- napp x x₁ ≈? nvar x₂ = no λ ()
-- -- nvar x ≈? napp x₁ x₂ = no λ ()
-- -- nvar x ≈? nvar x₁ with x ≡? x₁
-- -- ... | yes refl = yes (nvar≈ refl)
-- -- ... | no ¬p = no λ { (nvar≈ x) → ¬p x }
-- -- -- napp x x₁ ≈? nelim x₂ x₃ x₄ = no λ ()
-- -- -- nvar x ≈? nelim x₁ x₂ x₃ = no λ ()
-- -- nelim x x₁ x₂ ≈? x₃
-- --   with x₃
-- --   with x ≈? x₃
-- --   with x₁ ≈? nzero
-- --   with x₂ ≈? nsucc (ne (nvar (vs vz)))
-- -- nelim x x₁ x₂ ≈? x₃ | _ | yes p | yes q | yes r = yes (trs (nelim≈ p q r) n-elimη)
-- -- nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | no ¬p | q | r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
-- -- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- -- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη → ¬p rfl ; n-elimη-sym → ¬p ({!   !}) } 
-- -- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη → ¬p rfl ; n-elimη-sym → ¬p ({!   !}) } 
-- -- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη → ¬p rfl ; n-elimη-sym → ¬p ({!   !}) } 
-- -- nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | p | no ¬q | r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
-- -- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- -- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη → ¬q rfl  ; n-elimη-sym → ¬q ({!   !}) } 
-- -- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη → ¬q rfl ; n-elimη-sym → ¬q ({!   !}) } 
-- -- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη → ¬q rfl ; n-elimη-sym → ¬q ({!   !}) } 
-- -- nelim x x₁ x₂ ≈? x₃ | nelim x' x₁' x₂' | p | q | no ¬r with (x ≈? x') with (x₁ ≈? x₁') with (x₂ ≈? x₂')
-- -- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- -- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη → ¬r rfl  ; n-elimη-sym → ¬r ({!   !}) } 
-- -- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη → ¬r rfl ; n-elimη-sym → ¬r ({!   !}) } 
-- -- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη → ¬r rfl ; n-elimη-sym → ¬r ({!   !}) } 
-- -- (nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | no ¬p | q | r = no λ { n-elimη → ¬p rfl }
-- -- (nelim x x₁ x₂ ≈? x₃) | nvar x₄ | no ¬p | q | r = no λ { n-elimη → ¬p rfl }
-- -- (nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | p | no ¬q | r = no λ { n-elimη → ¬q rfl }
-- -- (nelim x x₁ x₂ ≈? x₃) | nvar x₄ | p | no ¬q | r = no λ { n-elimη → ¬q rfl }
-- -- (nelim x x₁ x₂ ≈? x₃) | napp x₄ x₅ | p | q | no ¬r = no λ { n-elimη → ¬r rfl }
-- -- (nelim x x₁ x₂ ≈? x₃) | nvar x₄ | p | q | no ¬r = no λ { n-elimη → ¬r rfl }
-- -- x₃ ≈? nelim x x₁ x₂ 
-- --   with x₃
-- --   with x₃ ≈? x 
-- --   with nzero ≈? x₁
-- --   with nsucc (ne (nvar (vs vz))) ≈? x₂
-- -- x₃ ≈? nelim x x₁ x₂ | _ | yes p | yes q | yes r = yes (trs n-elimη-sym (nelim≈ p q r))
-- -- x₃ ≈? nelim x x₁ x₂ | nelim x' x₁' x₂' | no ¬p | q | r with (x' ≈? x) with (x₁' ≈? x₁) with (x₂' ≈? x₂)
-- -- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- -- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη-sym → ¬p rfl  ; n-elimη → ¬p ({!   !}) } 
-- -- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη-sym → ¬p rfl ; n-elimη → ¬p ({!   !}) } 
-- -- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη-sym → ¬p rfl ; n-elimη → ¬p ({!   !}) } 
-- -- x₃ ≈? nelim x x₁ x₂ | nelim x' x₁' x₂' | p | no ¬q | r with (x' ≈? x) with (x₁' ≈? x₁) with (x₂' ≈? x₂)
-- -- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- -- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη-sym → ¬q rfl  ; n-elimη → ¬q ({!   !}) }   
-- -- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη-sym → ¬q rfl ; n-elimη → ¬q ({!   !}) }   
-- -- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη-sym → ¬q rfl ; n-elimη → ¬q ({!   !}) }   
-- -- x₃ ≈? nelim x x₁ x₂ | nelim x' x₁' x₂' | p | q | no ¬r with (x' ≈? x) with (x₁' ≈? x₁) with (x₂' ≈? x₂)
-- -- ...   | yes p' | yes q' | yes r' = yes (nelim≈ p' q' r')
-- -- ...   | no ¬p' | _ | _ = no λ { (nelim≈ a a₁ a₂) → ¬p' a ; n-elimη-sym → ¬r rfl  ; n-elimη → ¬r ({!   !}) } 
-- -- ...   | _ | no ¬q' | _ = no λ { (nelim≈ a a₁ a₂) → ¬q' a₁ ; n-elimη-sym → ¬r rfl ; n-elimη → ¬r ({!   !}) } 
-- -- ...   | _ | _ | no ¬r' = no λ { (nelim≈ a a₁ a₂) → ¬r' a₂ ; n-elimη-sym → ¬r rfl ; n-elimη → ¬r ({!   !}) } 
-- -- (x₃ ≈? nelim x x₁ x₂) | napp x₄ x₅ | no ¬p | q | r = no λ { n-elimη-sym → ¬p rfl }
-- -- (x₃ ≈? nelim x x₁ x₂) | nvar x₄ | no ¬p | q | r = no λ { n-elimη-sym → ¬p rfl }
-- -- (x₃ ≈? nelim x x₁ x₂) | napp x₄ x₅ | p | no ¬q | r = no λ { n-elimη-sym → ¬q rfl }
-- -- (x₃ ≈? nelim x x₁ x₂) | nvar x₄ | p | no ¬q | r = no λ { n-elimη-sym → ¬q rfl }
-- -- (x₃ ≈? nelim x x₁ x₂) | napp x₄ x₅ | p | q | no ¬r = no λ { n-elimη-sym → ¬r rfl }
-- -- (x₃ ≈? nelim x x₁ x₂) | nvar x₄ | p | q | no ¬r = no λ { n-elimη-sym → ¬r rfl }   