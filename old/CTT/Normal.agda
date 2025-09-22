module CTT.Normal where

open import CTT.Theory renaming (syn to S)
open import Utils
open import Data.Unit
open import Data.Empty
open import Data.Product using (Σ-syntax; proj₁; proj₂) renaming (_,_ to pair)

open ＝-Reasoning

open Model S
open Ind

data CVar : CCon → Set where
  vz : CVar (CΓ ▷)
  vs : CVar CΓ → CVar (CΓ ▷)

data CThin : ∀ CΓ CΔ → CSub CΓ CΔ → Set

data CNf : ∀ CΓ → CTm CΓ → Set
data CNe : ∀ CΓ → CTm CΓ → Set
data Body : ∀ CΓ {t : CTm CΓ} → CNf CΓ t → Set
data Subj : ∀ CΓ {t : CTm CΓ} → CNf CΓ t → Set
data Not-η : ∀ CΓ {Ca : CTm CΓ} {Cna : CNf CΓ Ca} → Subj CΓ Cna → ∀ {Cb : CTm CΓ} → CNf CΓ Cb → Set
data _∈_ : CVar CΓ → ∀ {Ca : CTm CΓ} → CNf CΓ Ca → Set

variable
  Cna : CNf _ Ca
  Cna' : CNf _ Ca'
  Cnb : CNf _ Cb
  Cnea : CNe _ Ca
  Cnea' : CNe _ Ca'
  Cneb : CNe _ Cb
  Cs Cs' : Subj _ _ 
  Cbo Cbo' : Body _ _
  Cv Cv' : CVar _
  Cρ Cρ' Cρ'' : CThin _ _ _
  
⌜_⌝var : CVar CΓ → CTm CΓ
⌜ vz ⌝var = q
⌜ vs v ⌝var = ⌜ v ⌝var [ p ]

app' : CTm CΓ → CTm CΓ → CTm CΓ
app' t u = app t [ id , u ]

data CThin where
  εᵀ : CThin ∙ ∙ ε
  _⁺ᵀ : CThin CΓ CΔ Cσ → CThin (CΓ ▷) (CΔ ▷) (Cσ ⁺)
  _∘p : CThin CΓ CΔ Cσ → CThin (CΓ ▷) CΔ (Cσ ∘ p)

idᵀ : CThin CΓ CΓ id
idᵀ = {!   !}
-- idᵀ {CΓ = (CΓ ▷)} = idᵀ ⁺ᵀ

pᵀ : CThin (CΓ ▷) CΓ p
pᵀ = {!   !}

_∘ᵀ_ : CThin CΓ CΔ Cσ → CThin CΓ' CΓ Cσ' → CThin CΓ' CΔ (Cσ ∘ Cσ')
_∘ᵀ_ = {!   !}


data CNf where
  nvar : (v : CVar CΓ) → CNf CΓ (⌜ v ⌝var)
  nlam : ∀ {Cna : CNf (CΓ ▷) Ca} → Body (CΓ ▷) Cna → CNf CΓ (lam Ca)
  napp : ∀ {Cna : CNf CΓ Ca} → Subj CΓ Cna → (Cnb : CNf CΓ Cb) → CNf CΓ (app' Ca Cb)
  
data Body where
  bvar : (v : CVar CΓ) → Body CΓ (nvar v)
  blam : ∀ {Cna : CNf (CΓ ▷) Ca} → (Cbo : Body (CΓ ▷) Cna) → Body CΓ {lam Ca} (nlam Cbo)
  bapp : ∀ {Cna : CNf CΓ Ca} → (Cs : Subj CΓ Cna) → (Cnb : CNf CΓ Cb) → Not-η CΓ Cs Cnb → Body CΓ {app' Ca Cb} (napp Cs Cnb)

data Subj where
  svar : (v : CVar CΓ) → Subj CΓ (nvar v)
  sapp : ∀ {Cna : CNf CΓ Ca} → (Cs : Subj CΓ Cna) → (Cnb : CNf CΓ Cb) → Subj CΓ {app' Ca Cb} (napp Cs Cnb)
  
data Not-η where
  vs-var-not-η : Not-η (CΓ ▷) Cs (nvar (vs Cv))
  lam-not-η : Not-η CΓ Cs {lam Ca} (nlam Cbo)
  app-not-η : Not-η CΓ Cs {app' Ca Cb} (napp Cs' Cnb)
  fn-uses-vz-not-η : vz ∈ Cna → Not-η (CΓ ▷) {Ca} Cs (nvar vz)

data _∈_ where
  ∈-var : Cv ∈ (nvar Cv)
  ∈-app-left : ∀ {Cs : Subj CΓ Cna} → Cv ∈ Cna → Cv ∈ (napp Cs Cnb)
  ∈-app-right : Cv ∈ Cnb → Cv ∈ (napp Cs Cnb)
  ∈-lam : ∀ {Cbo : Body (CΓ ▷) Cna} → vs Cv ∈ Cna → Cv ∈ (nlam Cbo)
  
▷≠∙ : (CΓ ▷) ＝ ∙ → ⊥
  
thin : CVar CΔ → CThin CΓ CΔ Cσ → CVar CΓ
  
_[_]ᵀNf : CNf CΔ Ca → CThin CΓ CΔ Cσ → CNf CΓ (Ca [ Cσ ])
-- nvar v [ ρ ]ᵀ = {!   !}
-- nlam x [ ρ ]ᵀ = {!   !}
-- napp x t [ ρ ]ᵀ = {!   !}

_[_]ᵀNe : CNe CΔ Ca → CThin CΓ CΔ Cσ → CNe CΓ (Ca [ Cσ ])