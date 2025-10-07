module Model where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂; subst)

open import Utils


record TT : Set2 where
  field
    -- Logical
    ConL : Set1
    SubL : ConL → ConL → Set
    TyL : ConL → Set1
    TmL : ∀ ΓL → TyL ΓL → Set

    ∙L : ConL
    _▷L_ : (ΓL : ConL) → TyL ΓL → ConL
    
    -- Computational
    ConC : Set
    SubC : ConC → ConC → Set
    TmC : ConC → Set

    ∙C : ConC
    _▷C : ConC → ConC
    _[p*] : ∀ {ΓC} → TmC ∙C → TmC ΓC
    
    -- Total
    Con : ConL → ConC → Set1
    Sub : ∀ {ΓL ΔL ΓC ΔC} → Con ΓL ΓC → Con ΔL ΔC → SubL ΓL ΔL → SubC ΓC ΔC → Set
    Ty : ∀ ΓL → TyL ΓL → Set1
    Tm : ∀ {ΓL ΓC TL} → Con ΓL ΓC → Ty ΓL TL → TmL ΓL TL → TmC ΓC → Set
    
    ∙ : Con ∙L ∙C
    _▷_ : ∀ {ΓL ΓC TL} → Con ΓL ΓC → Ty ΓL TL → Con (ΓL ▷L TL) (ΓC ▷C)
    _▷0_ : ∀ {ΓL ΓC TL} → Con ΓL ΓC → TyL ΓL → Con (ΓL ▷L TL) ΓC
    
    -- Substitution
    _[_]TL : ∀ {ΓL ΔL} → TyL ΔL → SubL ΓL ΔL → TyL ΓL
    _[_]T : ∀ {ΓL ΔL AL} → Ty ΔL AL → (σ : SubL ΓL ΔL) → Ty ΓL (AL [ σ ]TL)
    _[_]L : ∀ {ΓL ΔL AL} → TmL ΔL AL → (σ : SubL ΓL ΔL) → TmL ΓL (AL [ σ ]TL)

    idL : ∀ {ΓL} → SubL ΓL ΓL
    _,L_ : ∀ {ΓL ΔL AL} → (σ : SubL ΓL ΔL) → TmL ΓL (AL [ σ ]TL) → SubL ΓL (ΔL ▷L AL)

  ⟨_⟩L : ∀ {ΓL AL} → TmL ΓL AL → SubL ΓL (ΓL ▷L AL)
  ⟨ t ⟩L = idL ,L (t [ idL ]L)
    
  field
    -- Function types
    ΠL : ∀ {ΓL} → (TL : TyL ΓL) → TyL (ΓL ▷L TL) → TyL ΓL
    lamL : ∀ {ΓL TL UL} → TmL (ΓL ▷L TL) UL → TmL ΓL (ΠL TL UL)
    apL : ∀ {ΓL TL UL} → TmL ΓL (ΠL TL UL) → TmL (ΓL ▷L TL) UL
    βL : ∀ {ΓL TL UL} t → apL {ΓL} {TL} {UL} (lamL t) ≡ t
    ηL : ∀ {ΓL TL UL} t → lamL {ΓL} {TL} {UL} (apL t) ≡ t
    lamC : ∀ {ΓC} → TmC (ΓC ▷C) → TmC ΓC
    appC : ∀ {ΓC} → TmC ΓC → TmC ΓC → TmC ΓC
    Π : ∀ {ΓL TL UL} → Ty ΓL TL → Ty (ΓL ▷L TL) UL → Ty ΓL (ΠL TL UL)
    lam : ∀ {ΓL ΓC TL UL tL tC Γ T U}
      → Tm {ΓL ▷L TL} {ΓC ▷C} {UL} (Γ ▷ T) U tL tC → Tm Γ (Π T U) (lamL tL) (lamC tC)
    app : ∀ {ΓL ΓC TL UL fL fC tL tC Γ T U}
      → Tm {ΓL} {ΓC} {ΠL TL UL} Γ (Π T U) fL fC → Tm Γ T tL tC
      → Tm Γ (U [ ⟨ tL ⟩L ]T) (apL fL [ ⟨ tL ⟩L ]L) (appC fC tC)
    
    -- Specialization types
    Spec : ∀ {ΓL TL} → Ty ΓL TL → (c : TmC ∙C) → Ty ΓL TL
    spec : ∀ {ΓL ΓC TL Γ T aL aC} → Tm {ΓL} {ΓC} {TL} Γ T aL (aC [p*]) → Tm Γ (Spec T aC) aL (aC [p*])
    unspec : ∀ {ΓL ΓC TL Γ T aL aC aC'} → Tm {ΓL} {ΓC} {TL} Γ (Spec T aC) aL aC' → Tm Γ T aL (aC [p*])
    
    -- lam : ∀ {ΓL ΓC TL UL tL tC} {Γ : Con ΓL ΓC} {T : Ty ΓL TL} {U : Ty (ΓL ▷L TL) UL}
    --       → Tm (Γ ▷ T) U → Tm Γ (Π T U) (lamL {ΓL} {TL} {UL} tL) (lamC tC)

