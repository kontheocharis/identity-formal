module CTT.Normal where

open import CTT.Theory renaming (syn to S)
open import Utils
open import Data.Unit
open import Data.Product using (Σ-syntax; proj₁; proj₂) renaming (_,_ to pair)

open ＝-Reasoning

open Model S
open Ind

data CVar : CCon → Set where
  vz : CVar (CΓ ▷)
  vs : CVar CΓ → CVar (CΓ ▷)

data CThin : ∀ CΓ CΔ → CSub CΓ CΔ → Set

data CNf : ∀ CΓ → CTm CΓ → Set
data Body : ∀ CΓ {t : CTm CΓ} → CNf CΓ t → Set
data Subj : ∀ CΓ {t : CTm CΓ} → CNf CΓ t → Set
data Not-η : ∀ CΓ {Ca : CTm CΓ} {Cna : CNf CΓ Ca} → Subj CΓ Cna → ∀ {Cb : CTm CΓ} → CNf CΓ Cb → Set
data _∈_ : CVar CΓ → ∀ {Ca : CTm CΓ} → CNf CΓ Ca → Set

variable
  Cna : CNf _ Ca
  Cna' : CNf _ Ca'
  Cnb : CNf _ Cb
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
  

module Normalisation where

  open Modelᴰ
  open Sortsᴰ
  open InSortsᴰ
  
  record NCon (CΓ : CCon) : Set1 where
    field
      ⟦_⟧ : CCon → Set

      sub : ⟦_⟧ CΔ → CThin CΓ' CΔ Cσ → ⟦_⟧ CΓ'
      sub-∘ : ∀ γ → sub γ (Cρ ∘ᵀ Cρ') ＝ sub (sub γ Cρ) Cρ'
      sub-id : ∀ γ → sub {CΓ'} γ idᵀ ＝ γ
      
      repr : ⟦_⟧ CΔ  → CSub CΔ CΓ
      repr-[] : ∀ {γ} {Cρ : CThin _ _ Cσ} → repr (sub γ Cρ) ＝ repr γ ∘ Cσ
  open NCon
      
  record NSub (NΓ : NCon CΓ) (NΔ : NCon CΔ) (Cσ : CSub CΓ CΔ) : Set where
    field
      ⟦_⟧ : ⟦ NΓ ⟧ CΓ' → ⟦ NΔ ⟧ CΓ'
      
  
  record NTm (NΓ : NCon CΓ) (Ca : CTm CΓ) : Set where

  record Σ-NTm (NΓ : NCon CΓ) : Set where
    field
      tm : CTm CΓ
      nf : NTm NΓ tm
  open Σ-NTm 
      

  N : Modelᴰ S

  -- Sorts
  N .sᴰ .CConᴰ = NCon
  N .sᴰ .CSubᴰ = NSub
  N .sᴰ .CTmᴰ = NTm

  -- Substitution calc
  ⟦ N .cᴰ .Ctorsᴰ.∙ᴰ ⟧ CΔ = ⊤ 
  N .cᴰ .Ctorsᴰ.∙ᴰ .sub _ _ = tt
  N .cᴰ .Ctorsᴰ.∙ᴰ .sub-∘ γ = refl
  N .cᴰ .Ctorsᴰ.∙ᴰ .sub-id γ = refl
  N .cᴰ .Ctorsᴰ.∙ᴰ .repr γ = ε
  N .cᴰ .Ctorsᴰ.∙ᴰ .repr-[] = sym εη


  -- ⟦ (N .cᴰ Ctorsᴰ.▷ᴰ) NΓ ⟧ CΔ = ?
  ⟦ (N .cᴰ Ctorsᴰ.▷ᴰ) NΓ ⟧ CΔ = Σ[ γ ∈ ⟦ NΓ ⟧ CΔ ] Σ-NTm NΓ
  (N .cᴰ Ctorsᴰ.▷ᴰ) NΓ .sub (pair γ t) ρ = pair (NΓ .sub γ ρ) t
  (N .cᴰ Ctorsᴰ.▷ᴰ) NΓ .sub-∘ {Cρ = Cρ} {Cρ' = Cρ'} (pair γ t) = cong (λ γ' → pair γ' t ) (NΓ .sub-∘ γ)
  (N .cᴰ Ctorsᴰ.▷ᴰ) NΓ .sub-id (pair γ t) = cong (λ γ' → pair γ' t) (NΓ .sub-id γ)
  (N .cᴰ Ctorsᴰ.▷ᴰ) NΓ .repr (pair γ t) = NΓ .repr γ , (t .tm [ NΓ .repr γ ])
  (N .cᴰ Ctorsᴰ.▷ᴰ) NΓ .repr-[] {Cσ = Cσ} {γ = pair γ t} {Cρ = Cρ} = begin
      (NΓ .repr (NΓ .sub γ Cρ) , (t .tm [ NΓ .repr (NΓ .sub γ Cρ) ]))
    ＝⟨ cong (λ σ → (σ , (t .tm [ NΓ .repr (NΓ .sub γ Cρ) ]))) (NΓ .repr-[]) ⟩
      ((NΓ .repr γ ∘ Cσ) , (t .tm [ NΓ .repr (NΓ .sub γ Cρ) ]))
    ＝⟨ cong (λ σ → ((NΓ .repr γ ∘ Cσ) , (t .tm [ σ ]))) (NΓ .repr-[]) ⟩
      ((NΓ .repr γ ∘ Cσ) , (t .tm [ NΓ .repr γ ∘ Cσ ]))
    ＝⟨ cong (λ t' → ((NΓ .repr γ ∘ Cσ) , t')) [∘] ⟩
      ((NΓ .repr γ ∘ Cσ) , ((t .tm [ NΓ .repr γ ]) [ Cσ ]))
    ＝⟨ sym ,∘ ⟩
      ((cᴰ N Ctorsᴰ.▷ᴰ) NΓ .repr (pair γ t) ∘ Cσ)
    ∎

  N .cᴰ .Ctorsᴰ.idᴰ = {!   !}
  N .cᴰ .Ctorsᴰ._∘ᴰ_ = {!   !}
  N .cᴰ .Ctorsᴰ.id∘ᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.∘idᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.∘assocᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.εᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.εηᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.pᴰ = {!   !}
  N .cᴰ .Ctorsᴰ._[_]ᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.qᴰ = {!   !}
  N .cᴰ .Ctorsᴰ._,ᴰ_ = {!   !}
  N .cᴰ .Ctorsᴰ.p∘,ᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.p,qᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.,∘ᴰ = {!   !}

  N .cᴰ .Ctorsᴰ.lamᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.appᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.[id]ᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.[∘]ᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.q[,]ᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.lam[]ᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.Πηᴰ = {!   !}
  N .cᴰ .Ctorsᴰ.Πβᴰ = {!   !}
     