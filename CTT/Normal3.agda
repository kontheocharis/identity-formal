{-# OPTIONS --cubical #-}
module CTT.Normal3 where

open import Data.Bool
open import Data.Nat
open import Data.Empty
open import Cubical.Foundations.Prelude hiding (Sub; _,_)
  renaming (_∙_ to trans)

coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
-- coe refl a = a

infix 4 _≡[_]_
_≡[_]_ : ∀ {i} {A B : Set i} → A → A ≡ B → B → Set i
_≡[_]_ {i} {A} {B} a p b = PathP (λ i → p i) a b
  
  -- η-body-lam₁ : (t : Nf-β ((Γ ▷) ▷) t₁) → Body-βη (Γ ▷) ?


data Con : Set where
  ∙ : Con
  _▷ : Con → Con

variable
  Γ Γ' Δ : Con

data Tm : Con → Set
data Var : (Γ : Con) → Set

-- β
data Nf-β : ∀ Γ → Tm Γ → Set
data Subj-β : ∀ Γ {t : Tm Γ} → Nf-β Γ t → Set

-- βη
data Nf-βη : ∀ Γ → Tm Γ → Set
data Body-βη : ∀ Γ {t : Tm Γ} → Nf-βη Γ t → Set
data Subj-βη : ∀ Γ {t : Tm Γ} → Nf-βη Γ t → Set
data Not-η : ∀ Γ {t : Tm Γ} {nt : Nf-βη Γ t} → Subj-βη Γ nt → ∀ {u : Tm Γ} → Nf-βη Γ u → Set

data Sub : Con → Con → Set
data Thin : ∀ Γ Δ → Sub Γ Δ → Set
data _∈_ : Var Γ → Tm Γ → Set
  
variable
  t u w : Tm _

  nbt : Nf-β _ t
  nbu : Nf-β _ u
  nbw : Nf-β _ w
  sb sb' : Subj-β _ _ 

  nt : Nf-βη _ t
  nu : Nf-βη _ u
  nw : Nf-βη _ w
  s s' : Subj-βη _ _ 
  b b' : Body-βη _ _

  v v' : Var _

  ρ ρ' ρ'' : Thin _ _ _
  σ σ' σ'' : Sub _ _
  
_[_] : Tm Δ → Sub Γ Δ → Tm Γ

id : Sub Γ Γ

term : Sub Γ ∙

p : Sub (Γ ▷) Γ

_,_ : Sub Γ Δ → Tm Γ → Sub Γ (Δ ▷)

data Var where
  vz : Var (Γ ▷)
  vs : Var Γ → Var (Γ ▷)

data Tm where
  lam : Tm (Γ ▷) → Tm Γ
  app : Tm Γ → Tm Γ → Tm Γ
  var : Var Γ → Tm Γ
  
  β : app (lam t) u ≡ (t [ id , u ])
  η : lam (app (t [ p ]) (var vz)) ≡ t

pᵀ : Thin (Γ ▷) Γ p
_[_]n : Nf-β Δ t → Thin Γ Δ σ → Nf-β Γ (t [ σ ])
_[_]s : Subj-β Δ nbt → (ρ : Thin Γ Δ σ) → Subj-β Γ (nbt [ ρ ]n)
-- p : Thin (Γ ▷) Γ
  
-- β normal forms

data Nf-β where
  nvar : (v : Var Γ) → Nf-β Γ (var v)
  nlam : Nf-β (Γ ▷) t → Nf-β Γ (lam t)
  napp : Subj-β Γ nbt → Nf-β Γ u → Nf-β Γ (app t u)
  nη : nlam (napp {nbt = nbt [ pᵀ ]n} (sb [ pᵀ ]s) (nvar vz)) ≡[ cong (Nf-β _) η ] nbt

data Subj-β where
  svar : (v : Var Γ) → Subj-β Γ (nvar v)
  sapp : (s : Subj-β Γ nbt) → (nu : Nf-β Γ u) → Subj-β Γ {app t u} (napp s nu)
  
-- βη normal forms

data Nf-βη where
  nvar : (v : Var Γ) → Nf-βη Γ (var v)
  nlam : Body-βη (Γ ▷) nt → Nf-βη Γ (lam t)
  napp : Subj-βη Γ nt → Nf-βη Γ u → Nf-βη Γ (app t u)
  
data Body-βη where
  bvar : (v : Var Γ) → Body-βη Γ (nvar v)
  blam : (b : Body-βη (Γ ▷) nt) → Body-βη Γ {lam t} (nlam b)
  bapp : (s : Subj-βη Γ nt) → (nu : Nf-βη Γ u) → Not-η Γ s nu → Body-βη Γ {app t u} (napp s nu)

data Subj-βη where
  svar : (v : Var Γ) → Subj-βη Γ (nvar v)
  sapp : (s : Subj-βη Γ nt) → (nu : Nf-βη Γ u) → Subj-βη Γ {app t u} (napp s nu)
  
data Not-η where
  vs-var-not-η : Not-η (Γ ▷) s (nvar (vs v))
  lam-not-η : Not-η Γ s {lam t} (nlam b)
  app-not-η : Not-η Γ s {app t u} (napp s nu)
  fn-uses-vz-not-η : vz ∈ t → Not-η (Γ ▷) {t} s (nvar vz)

data _∈_ where
  ∈-var : v ≡ v' → v ∈ (var v')
  ∈-app-left : v ∈ t → v ∈ (app t u)
  ∈-app-right : v ∈ u → v ∈ (app t u)
  ∈-lam : vs v ∈ u → v ∈ (lam u)
  
-- data Thin where
--   ε : Thin ∙ ∙ term
--   _⁺ : Thin Γ Δ σ → Thin (Γ ▷) (Δ ▷) ({!   !} σ)
--   _∘p : Thin Γ Δ σ → Thin (Γ ▷) Δ ({!   !} σ)

-- data Dec (X : Set) : Set where
--   yes : X → Dec X
--   no : (X → ⊥) → Dec X
  
-- data _＋_ (A : Set) (B : Set) : Set where
--   inl : A → A ＋ B
--   inr : B → A ＋ B
  
-- η-reduce : Nf-β Γ t → Nf-βη Γ t
-- η-lam : Nf-β (Γ ▷) t → Nf-βη Γ (lam t)
-- η-subj : Subj-β Γ {t} nbt → Subj-βη Γ {t} (η-reduce nbt)
-- η-lam-body-app : (s : Subj-β (Γ ▷) {t} nbt) (nu : Nf-β (Γ ▷) u)
--   → Body-βη (Γ ▷) {app t u} (napp (η-subj s) (η-reduce nu))
-- η-body-lam : (nt : Nf-β ((Γ ▷) ▷) t) → Body-βη (Γ ▷) (η-lam nt)

-- _≡?_ : (v : Var Γ) → (v' : Var Γ) → Dec (v ≡ v')
-- vz ≡? vz = yes refl
-- -- vz ≡? vs v' = no λ { () }
-- -- vs v ≡? vz =  no λ { () }
-- -- vs v ≡? vs v' with v ≡? v'
-- -- ... | yes refl = yes refl
-- -- ... | no x = no λ { refl → x refl }

-- _∈?_ : (v : Var Γ) → (t : Tm Γ) → Dec (v ∈ t)
-- -- v ∈? lam t with (vs v) ∈? t
-- -- ... | yes x = yes (∈-lam x)
-- -- ... | no x = no λ { (∈-lam z) → x z }
-- -- v ∈? app t t₁ with v ∈? t
-- -- ... | yes x = yes (∈-app-left x)
-- -- ... | no y with v ∈? t₁
-- -- ...   | yes x' = yes (∈-app-right x')
-- -- ...   | no x' = no λ { (∈-app-left z) → y z
-- --                   ; (∈-app-right z) → x' z }
-- -- v ∈? var v' with v ≡? v'
-- -- ... | yes x = yes (∈-var x)
-- -- ... | no x = no λ { (∈-var x') → x x' }
  
-- η-reduce (nvar v) = nvar v
-- η-reduce (nlam x) = η-lam x
-- η-reduce (napp x x₁) = napp (η-subj x) (η-reduce x₁)

-- η-subj (svar v) = svar v
-- η-subj (sapp s nu) = sapp (η-subj s) (η-reduce nu)

-- η-lam (nvar v) = nlam (bvar v)
-- η-lam (nlam t) = nlam (η-body-lam t)
-- η-lam (napp x t) = {!   !}

-- η-lam-body-app {t = t} s (nvar vz) with vz ∈? t
-- ... | yes x = bapp (η-subj s) (nvar vz) (fn-uses-vz-not-η x)
-- ... | no x = {!  bvar ? !}
-- η-lam-body-app s (nvar (vs v₁)) = bapp (η-subj s) (η-reduce (nvar (vs v₁))) vs-var-not-η
-- η-body-app (svar v) (nlam nu) = bapp (η-subj (svar v)) (η-reduce (nlam nu)) {!   !}
-- η-body-app (svar v) (napp x nu) = bapp {!   !} {!   !} {!   !}
-- η-body-app (sapp s nu) (nvar v) = bapp {!   !} {!   !} {!   !}
-- η-body-app (sapp s nu) (nlam nu₁) = bapp {!   !} {!   !} {!   !}
-- η-body-app (sapp s nu) (napp x nu₁) = bapp {!   !} {!   !} {!   !}

-- η-body-lam (nvar v) = blam (bvar v)
-- η-body-lam (nlam nt) = blam (η-body-lam nt)
-- η-body-lam (napp x nt) = {!   !}

-- thin : Var Γ → Thin Δ Γ → Var Δ
-- thin v (t ∘p) = vs (thin v t)
-- thin vz (t ⁺) = vz
-- thin (vs v) (t ⁺) = vs (thin v t)
  
-- (ne x) [ σ ] = ne (x [ σ ])
-- (napp x y) [ σ ] = napp (x [ σ ]) (y [ σ ])
-- (nvar v) [ σ ] = nvar (thin v σ)
-- nlam x [ σ ] = nlam (x [ σ ⁺ ])

-- id : Thin Γ Γ
-- id {Γ = ∙} = ε
-- id {Γ = Γ ▷} = id ⁺

-- p : Thin (Γ ▷) Γ
-- p = id ∘p

-- thinid : ∀ {v : Var Γ} → thin v id ≡ v
-- thinid {Γ = Γ ▷} {v = vz} = refl
-- thinid {Γ = Γ ▷} {v = vs v} = cong vs thinid

-- thinp≡vs : ∀ {v : Var Γ} → thin v p ≡ vs v
-- thinp≡vs {Γ = Γ ▷} {v = vz} = refl
-- thinp≡vs {Γ = Γ ▷} {v = vs v} = cong vs thinp≡vs

-- Lift : (n : ℕ) → Con → Con
-- Lift zero Γ = Γ
-- Lift (suc n) Γ = (Lift n Γ) ▷

-- lift : (n : ℕ) → Thin Γ Δ → Thin (Lift n Γ) (Lift n Δ)
-- lift zero σ = σ
-- lift (suc n) σ = (lift n σ) ⁺

-- thin-[thin-lift]-lift-p≡thin-lift-∘p : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {v : Var (Lift n Δ)}
--   → thin (thin v (lift n σ)) (lift n p) ≡ thin v (lift n (σ ∘p))
-- thin-[thin-lift]-lift-p≡thin-lift-∘p {zero} {σ = σ} {v = v} rewrite thinid {v = thin v σ} = refl
-- thin-[thin-lift]-lift-p≡thin-lift-∘p {suc n} {v = vz} = refl
-- thin-[thin-lift]-lift-p≡thin-lift-∘p {suc n} {v = vs v} = cong vs thin-[thin-lift]-lift-p≡thin-lift-∘p

-- [lift][liftp]≡[lift∘p] : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {z : Norm k (Lift n Δ) a}
--   → z [ lift n σ ] [ lift n p ] ≡ z [ lift n (σ ∘p) ]
-- [lift][liftp]≡[lift∘p] {z = ne x} = cong ne [lift][liftp]≡[lift∘p]
-- [lift][liftp]≡[lift∘p] {z = nlam x} = cong nlam [lift][liftp]≡[lift∘p]
-- [lift][liftp]≡[lift∘p] {z = napp x x₁} = cong₂ napp [lift][liftp]≡[lift∘p] [lift][liftp]≡[lift∘p]
-- [lift][liftp]≡[lift∘p] {z = nvar x} = cong nvar thin-[thin-lift]-lift-p≡thin-lift-∘p

-- thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {v : Var (Lift n Δ)}
--   → thin (thin v (lift n p)) (lift n (σ ⁺)) ≡ thin (thin v (lift n σ)) (lift n p)
-- thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {zero} {σ = σ} {v = v}
--   rewrite thinid {v = v}
--   rewrite thinid {v = thin v σ}
--     = refl
-- thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {suc n} {v = vz} = refl
-- thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p {suc n} {v = vs v} = cong vs thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p

-- [liftp][lift⁺]≡[lift][liftp] : ∀ {n : ℕ} {Γ Δ} {σ : Thin Γ Δ} {z : Norm k (Lift n Δ) a}
--   → (z [ lift n p ]) [ lift n (σ ⁺) ] ≡ (z [ lift n σ ]) [ lift n p ]
-- [liftp][lift⁺]≡[lift][liftp] {z = ne x} = cong ne [liftp][lift⁺]≡[lift][liftp]
-- [liftp][lift⁺]≡[lift][liftp] {z = nlam x} = cong nlam [liftp][lift⁺]≡[lift][liftp]
-- [liftp][lift⁺]≡[lift][liftp] {z = napp x x₁} = cong₂ napp [liftp][lift⁺]≡[lift][liftp] [liftp][lift⁺]≡[lift][liftp]
-- [liftp][lift⁺]≡[lift][liftp] {z = nvar x} = cong nvar thin-[thin-lift-p]-lift-⁺≡thin-[thin-lift]-lift-p

-- [][p]≡[∘p] : ∀ {σ : Thin Γ Δ} → z [ σ ] [ p ] ≡ z [ σ ∘p ]
-- [][p]≡[∘p] = [lift][liftp]≡[lift∘p]

-- [p][⁺]≡[][p] : ∀ {σ : Thin Γ Δ} → (z [ p ]) [ σ ⁺ ] ≡ (z [ σ ]) [ p ]
-- [p][⁺]≡[][p] = [liftp][lift⁺]≡[lift][liftp]

-- [id] : z [ id ] ≡ z
-- [id] {z = ne x} = cong ne [id]
-- [id] {z = nlam x} = cong nlam [id]
-- [id] {z = napp x x₁} = cong₂ napp [id] [id]
-- [id] {z = nvar x} = cong nvar (thinid)