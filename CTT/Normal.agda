module CTT.Normal where

open import CTT.Theory renaming (syn to S)
open import Utils

open Model S

data CVar : CCon → Set where
  vz : CVar (CΓ ▷)
  vs : CVar CΓ → CVar (CΓ ▷)

data Nf-βη : ∀ CΓ → CTm CΓ → Set
data Body-βη : ∀ CΓ {t : CTm CΓ} → Nf-βη CΓ t → Set
data Subj-βη : ∀ CΓ {t : CTm CΓ} → Nf-βη CΓ t → Set
data Not-η : ∀ CΓ {Ca : CTm CΓ} {Cna : Nf-βη CΓ Ca} → Subj-βη CΓ Cna → ∀ {Cb : CTm CΓ} → Nf-βη CΓ Cb → Set
data _∈_ : CVar CΓ → ∀ {Ca : CTm CΓ} → Nf-βη CΓ Ca → Set

variable
  Cna : Nf-βη _ Ca
  Cna' : Nf-βη _ Ca'
  Cnb : Nf-βη _ Cb
  Cs Cs' : Subj-βη _ _ 
  Cbo Cbo' : Body-βη _ _
  Cv Cv' : CVar _
  
⌜_⌝var : CVar CΓ → CTm CΓ
⌜ vz ⌝var = q
⌜ vs v ⌝var = ⌜ v ⌝var [ p ]

app' : CTm CΓ → CTm CΓ → CTm CΓ
app' t u = app t [ id , u ]

data Nf-βη where
  nvar : (v : CVar CΓ) → Nf-βη CΓ (⌜ v ⌝var)
  nlam : ∀ {Cna : Nf-βη (CΓ ▷) Ca} → Body-βη (CΓ ▷) Cna → Nf-βη CΓ (lam Ca)
  napp : ∀ {Cna : Nf-βη CΓ Ca} → Subj-βη CΓ Cna → (Cnb : Nf-βη CΓ Cb) → Nf-βη CΓ (app' Ca Cb)
  
data Body-βη where
  bvar : (v : CVar CΓ) → Body-βη CΓ (nvar v)
  blam : ∀ {Cna : Nf-βη (CΓ ▷) Ca} → (Cbo : Body-βη (CΓ ▷) Cna) → Body-βη CΓ {lam Ca} (nlam Cbo)
  bapp : ∀ {Cna : Nf-βη CΓ Ca} → (Cs : Subj-βη CΓ Cna) → (Cnb : Nf-βη CΓ Cb) → Not-η CΓ Cs Cnb → Body-βη CΓ {app' Ca Cb} (napp Cs Cnb)

data Subj-βη where
  svar : (v : CVar CΓ) → Subj-βη CΓ (nvar v)
  sapp : ∀ {Cna : Nf-βη CΓ Ca} → (Cs : Subj-βη CΓ Cna) → (Cnb : Nf-βη CΓ Cb) → Subj-βη CΓ {app' Ca Cb} (napp Cs Cnb)
  
data Not-η where
  vs-var-not-η : Not-η (CΓ ▷) Cs (nvar (vs Cv))
  lam-not-η : Not-η CΓ Cs {lam Ca} (nlam Cbo)
  app-not-η : Not-η CΓ Cs {app' Ca Cb} (napp Cs' Cnb)
  fn-uses-vz-not-η : vz ∈ Cna → Not-η (CΓ ▷) {Ca} Cs (nvar vz)

data _∈_ where
  ∈-var : Cv ∈ (nvar Cv)
  ∈-app-left : ∀ {Cs : Subj-βη CΓ Cna} → Cv ∈ Cna → Cv ∈ (napp Cs Cnb)
  ∈-app-right : Cv ∈ Cnb → Cv ∈ (napp Cs Cnb)
  ∈-lam : ∀ {Cbo : Body-βη (CΓ ▷) Cna} → vs Cv ∈ Cna → Cv ∈ (nlam Cbo)