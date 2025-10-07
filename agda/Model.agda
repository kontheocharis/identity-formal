module Model where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂; subst)

open import Utils

record TT-Comp : Set2 where
  field
    -- Computational
    
    -- Sorts
    ConC : Set
    SubC : ConC → ConC → Set
    TmC : ConC → Set
    
    -- Category
    idC : ∀ {ΓC} → SubC ΓC ΓC
    _∘C_ : ∀ {ΓC ΔC ΘC} → (σ : SubC ΔC ΘC) → (τ : SubC ΓC ΔC) → SubC ΓC ΘC
    assocC : ∀ {ΓC ΔC ΘC ΞC} {ρ : SubC ΘC ΞC} {σ : SubC ΔC ΘC} {τ : SubC ΓC ΔC}
      → (ρ ∘C (σ ∘C τ)) ≡ ((ρ ∘C σ) ∘C τ)
    ∘idC : ∀ {ΓC ΔC} {σ : SubC ΓC ΔC} → (idC ∘C σ) ≡ σ
    idC∘ : ∀ {ΓC ΔC} {σ : SubC ΓC ΔC} → (σ ∘C idC) ≡ σ
    
    -- Presheaf action
    _[_]C : ∀ {ΓC ΔC} → TmC ΔC → (σ : SubC ΓC ΔC) → TmC ΓC
    [id]C : ∀ {ΓC} {t : TmC ΓC} → t [ idC ]C ≡ t
    [∘]C : ∀ {ΓC ΔC ΘC} {t : TmC ΘC} {σ : SubC ΔC ΘC} {τ : SubC ΓC ΔC}
      → t [ σ ∘C τ ]C ≡ (t [ σ ]C) [ τ ]C

    -- Terminal object
    ∙C : ConC
    εC : ∀ {ΓC} → SubC ΓC ∙C
    ∃!εC : ∀ {ΓC} σ → εC {ΓC} ≡ σ

    -- Context extension
    _▷C : ConC → ConC
    pC : ∀ {ΓC} → SubC (ΓC ▷C) ΓC
    qC : ∀ {ΓC} → TmC (ΓC ▷C)
    _,C_ : ∀ {ΓC ΔC} → (σ : SubC ΓC ΔC) → TmC ΓC → SubC ΓC (ΔC ▷C)
    ,∘C : ∀ {ΓC ΔC ΘC} {σ : SubC ΓC ΔC} {σ' : SubC ΘC ΓC} {t} → (σ ,C t) ∘C σ' ≡ (σ ∘C σ') ,C (t [ σ' ]C)
    pC,qC : ∀ {ΓC} → (pC {ΓC} ,C qC) ≡ idC
    pC∘, : ∀ {ΓC ΔC} {σ : SubC ΓC ΔC} {t : TmC ΓC} → pC ∘C (σ ,C t) ≡ σ
    qC[,] : ∀ {ΓC ΔC} {σ : SubC ΓC ΔC} {t : TmC ΓC} → qC [ σ ,C t ]C ≡ t
    
  _⁺C : ∀ {ΓC ΔC} → SubC ΓC ΔC → SubC (ΓC ▷C) (ΔC ▷C)
  σ ⁺C = (σ ∘C pC) ,C qC
    
  field

    -- Terms
    
    -- Functions
    lamC : ∀ {ΓC} → TmC (ΓC ▷C) → TmC ΓC
    lamC[] : ∀ {ΓC ΔC t} {σ : SubC ΔC ΓC} → (lamC {ΓC} t) [ σ ]C ≡ lamC (t [ σ ⁺C ]C)

    appC : ∀ {ΓC} → TmC ΓC → TmC ΓC → TmC ΓC
    appC[] : ∀ {ΓC ΔC t u} {σ : SubC ΔC ΓC} → (appC {ΓC} t u) [ σ ]C ≡ appC (t [ σ ]C) (u [ σ ]C)
    
    -- Unit
    unit : ∀ {ΓC} → TmC ΓC
    unit[] : ∀ {ΓC ΔC} {σ : SubC ΔC ΓC} → (unit {ΓC}) [ σ ]C ≡ unit

    -- Natural numbers
    zeroC : ∀ {ΓC} → TmC ΓC
    zeroC[] : ∀ {ΓC ΔC σ} → (zeroC {ΓC}) [ σ ]C ≡ zeroC {ΔC}

    succC : ∀ {ΓC} → TmC ΓC → TmC ΓC
    succC[] : ∀ {ΓC ΔC t} {σ : SubC ΔC ΓC} → (succC {ΓC} t) [ σ ]C ≡ succC (t [ σ ]C)
    
    recC : ∀ {ΓC} → TmC ΓC → TmC (ΓC ▷C ▷C) → TmC ΓC → TmC ΓC
    recC[] : ∀ {ΓC ΔC z s n} {σ : SubC ΔC ΓC}
      → (recC {ΓC} z s n) [ σ ]C ≡ recC (z [ σ ]C) (s [ σ ⁺C ⁺C ]C) (n [ σ ]C)
    

    recC-η1 : ∀ {ΓC n} → recC {ΓC} zeroC (succC qC) n ≡ n
    recC-η2 : ∀ {ΓC n} → recC {ΓC} zeroC (succC (qC [ pC ]C)) n ≡ n
    recC-β-zero : ∀ {ΓC z s} → recC {ΓC} z s zeroC ≡ z
    recC-β-succ : ∀ {ΓC z s n} → recC {ΓC} z s (succC n) ≡ s [ (idC ,C n) ,C recC z s n ]C


record TT-Logic : Set2 where
  field
    -- Logical
    
    -- Sorts
    ConL : Set1
    SubL : ConL → ConL → Set
    TyL : ConL → Set1
    TmL : ∀ ΓL → TyL ΓL → Set
    
    -- Category
    idL : ∀ {ΓL} → SubL ΓL ΓL
    _∘L_ : ∀ {ΓL ΔL ΘL} → (σ : SubL ΔL ΘL) → (τ : SubL ΓL ΔL) → SubL ΓL ΘL
    assocL : ∀ {ΓL ΔL ΘL ΞL} {ρ : SubL ΘL ΞL} {σ : SubL ΔL ΘL} {τ : SubL ΓL ΔL}
      → (ρ ∘L (σ ∘L τ)) ≡ ((ρ ∘L σ) ∘L τ)
    ∘idL : ∀ {ΓL ΔL} {σ : SubL ΓL ΔL} → (idL ∘L σ) ≡ σ
    idL∘ : ∀ {ΓL ΔL} {σ : SubL ΓL ΔL} → (σ ∘L idL) ≡ σ
    
    -- Presheaf actions
    _[_]TL : ∀ {ΓL ΔL} → TyL ΔL → SubL ΓL ΔL → TyL ΓL
    _[_]L : ∀ {ΓL ΔL AL} → TmL ΔL AL → (σ : SubL ΓL ΔL) → TmL ΓL (AL [ σ ]TL)
    [id]TL : ∀ {ΓL} {A : TyL ΓL} → A [ idL ]TL ≡ A
    [id]L : ∀ {ΓL AL} {t : TmL ΓL AL} → t [ idL ]L ≡[ cong (TmL ΓL) [id]TL ] t
    [∘]TL : ∀ {ΓL ΔL ΘL} {A : TyL ΘL} {σ : SubL ΔL ΘL} {τ : SubL ΓL ΔL}
      → A [ σ ∘L τ ]TL ≡ (A [ σ ]TL) [ τ ]TL
    [∘]L : ∀ {ΓL ΔL ΘL AL} {t : TmL ΘL AL} {σ : SubL ΔL ΘL} {τ : SubL ΓL ΔL}
      → t [ σ ∘L τ ]L ≡[ cong (TmL ΓL) [∘]TL ] (t [ σ ]L) [ τ ]L
  
  coeL : ∀ {ΓL AL BL} → AL ≡ BL → TmL ΓL AL → TmL ΓL BL
  coeL p t = subst (TmL _) p t
      
  field
      
    -- Terminal object
    ∙L : ConL
    εL : ∀ {ΓL} → SubL ΓL ∙L
    ∃!εL : ∀ {ΓL} σ → εL {ΓL} ≡ σ
    
    -- Context extension
    _▷L_ : (ΓL : ConL) → TyL ΓL → ConL
    pL : ∀ {ΓL AL} → SubL (ΓL ▷L AL) ΓL
    qL : ∀ {ΓL AL} → TmL (ΓL ▷L AL) (AL [ pL ]TL)
    _,L_ : ∀ {ΓL ΔL AL} → (σ : SubL ΓL ΔL) → TmL ΓL (AL [ σ ]TL) → SubL ΓL (ΔL ▷L AL)
    ,L∘ : ∀ {ΓL ΔL ΘL} {AL : TyL ΔL} {σ : SubL ΓL ΔL} {σ' : SubL ΘL ΓL} {t : TmL ΓL (AL [ σ ]TL)}
      → (σ ,L t) ∘L σ' ≡ (σ ∘L σ') ,L coeL (sym [∘]TL) (t [ σ' ]L)
    pL,qL : ∀ {ΓL AL} → (pL {ΓL} {AL} ,L qL) ≡ idL
    pL∘, : ∀ {ΓL ΔL AL} {σ : SubL ΓL ΔL} {t : TmL ΓL (AL [ σ ]TL)}
      → pL ∘L (σ ,L t) ≡ σ
    qL[,] : ∀ {ΓL ΔL AL} {σ : SubL ΓL ΔL} {t : TmL ΓL (AL [ σ ]TL)}
      → qL [ σ ,L t ]L ≡[ cong (TmL ΓL) (trans (sym [∘]TL) (cong (AL [_]TL) pL∘,)) ] t


  ⟨_⟩L : ∀ {ΓL AL} → TmL ΓL AL → SubL ΓL (ΓL ▷L AL)
  ⟨ t ⟩L = idL ,L (t [ idL ]L)
    
  _⁺L : ∀ {ΓL ΔL A} → (σ : SubL ΓL ΔL) → SubL (ΓL ▷L (A [ σ ]TL)) (ΔL ▷L A)
  σ ⁺L = (σ ∘L pL) ,L subst (TmL _) (sym [∘]TL) qL
  
  field
    -- Terms

    -- Functions
    ΠL : ∀ {ΓL} → (TL : TyL ΓL) → TyL (ΓL ▷L TL) → TyL ΓL
    ΠL[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} {T : TyL ΓL} {U : TyL (ΓL ▷L T)}
      → (ΠL T U) [ σ ]TL ≡ ΠL (T [ σ ]TL) (U [ σ ⁺L ]TL)

    lamL : ∀ {ΓL TL UL} → TmL (ΓL ▷L TL) UL → TmL ΓL (ΠL TL UL)
    lamL[] : ∀ {ΓL ΔL T U t} {σ : SubL ΔL ΓL}
      → (lamL {ΓL} {T} {U} t) [ σ ]L ≡[ cong (TmL _) ΠL[] ] lamL (t [ σ ⁺L ]L)
    apL : ∀ {ΓL TL UL} → TmL ΓL (ΠL TL UL) → TmL (ΓL ▷L TL) UL
    βL : ∀ {ΓL TL UL} t → apL {ΓL} {TL} {UL} (lamL t) ≡ t
    ηL : ∀ {ΓL TL UL} t → lamL {ΓL} {TL} {UL} (apL t) ≡ t
    
    -- Universe
    UL : ∀ {ΓL} → TyL ΓL
    UL[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} → UL [ σ ]TL ≡ UL
    
    ElL : ∀ {ΓL} → TmL ΓL UL → TyL ΓL
    ElL[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} {a : TmL ΓL UL}
      → (ElL a) [ σ ]TL ≡ ElL (subst (TmL _) UL[] (a [ σ ]L))
      
    -- Natural numbers
    NatL : ∀ {ΓL} → TyL ΓL
    NatL[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} → NatL [ σ ]TL ≡ NatL
    zeroL : ∀ {ΓL} → TmL ΓL NatL
    zeroL[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} → (zeroL {ΓL}) [ σ ]L ≡[ cong (TmL _) NatL[] ] zeroL
    succL : ∀ {ΓL} → TmL ΓL NatL → TmL ΓL NatL
    succL[] : ∀ {ΓL ΔL t} {σ : SubL ΔL ΓL}
      → (succL {ΓL} t) [ σ ]L ≡[ cong (TmL _) NatL[] ] succL (coeL NatL[] (t [ σ ]L))


    -- We should really have the proper eliminator but we don't do it here
    -- because the substitution calculus gets out of hand.
    recL : ∀ {ΓL} → (P : TyL ΓL)
      → TmL ΓL P
      → TmL ((ΓL ▷L NatL) ▷L (P [ pL ]TL)) (P [ pL ∘L pL ]TL)
      → (n : TmL ΓL NatL)
      → TmL ΓL P
    recL[] : ∀ {ΓL ΔL P z s n} {σ : SubL ΔL ΓL}
      → (recL {ΓL} P z s n) [ σ ]L
        ≡
        recL {ΔL} (P [ σ ]TL) (z [ σ ]L)
        (let m = s [ {!   !} ,L {!   !} ]L in {!  m !})
        (coeL NatL[] (n [ σ ]L))
          


-- record TT : Set2 where
--   field
--     comp : TT-Comp
--     logic : TT-Logic

--   open TT-Comp comp public
--   open TT-Logic logic public
    
--   field
--     -- Total
--     Con : ConL → ConC → Set1
--     Sub : ∀ {ΓL ΔL ΓC ΔC} → Con ΓL ΓC → Con ΔL ΔC → SubL ΓL ΔL → SubC ΓC ΔC → Set
--     Ty : ∀ ΓL → TyL ΓL → Set1
--     Tm : ∀ {ΓL ΓC TL} → Con ΓL ΓC → Ty ΓL TL → TmL ΓL TL → TmC ΓC → Set
    
--     ∙ : Con ∙L ∙C
--     _▷_ : ∀ {ΓL ΓC TL} → Con ΓL ΓC → Ty ΓL TL → Con (ΓL ▷L TL) (ΓC ▷C)
--     _▷0_ : ∀ {ΓL ΓC TL} → Con ΓL ΓC → TyL ΓL → Con (ΓL ▷L TL) ΓC
    
--     _[_]T : ∀ {ΓL ΔL AL} → Ty ΔL AL → (σ : SubL ΓL ΔL) → Ty ΓL (AL [ σ ]TL)
    
--   field
--     Π : ∀ {ΓL TL UL} → Ty ΓL TL → Ty (ΓL ▷L TL) UL → Ty ΓL (ΠL TL UL)
--     lam : ∀ {ΓL ΓC TL UL tL tC Γ T U}
--       → Tm {ΓL ▷L TL} {ΓC ▷C} {UL} (Γ ▷ T) U tL tC → Tm Γ (Π T U) (lamL tL) (lamC tC)
--     app : ∀ {ΓL ΓC TL UL fL fC tL tC Γ T U}
--       → Tm {ΓL} {ΓC} {ΠL TL UL} Γ (Π T U) fL fC → Tm Γ T tL tC
--       → Tm Γ (U [ ⟨ tL ⟩L ]T) (apL fL [ ⟨ tL ⟩L ]L) (appC fC tC)
    
--     -- Specialization types
--     Spec : ∀ {ΓL TL} → Ty ΓL TL → (c : TmC ∙C) → Ty ΓL TL
--     spec : ∀ {ΓL ΓC TL Γ T aL aC} → Tm {ΓL} {ΓC} {TL} Γ T aL (aC [ εC ]C) → Tm Γ (Spec T aC) aL (aC [ εC ]C)
--     unspec : ∀ {ΓL ΓC TL Γ T aL aC aC'} → Tm {ΓL} {ΓC} {TL} Γ (Spec T aC) aL aC' → Tm Γ T aL (aC [ εC ]C)
    
    -- lam : ∀ {ΓL ΓC TL UL tL tC} {Γ : Con ΓL ΓC} {T : Ty ΓL TL} {U : Ty (ΓL ▷L TL) UL}
    --       → Tm (Γ ▷ T) U → Tm Γ (Π T U) (lamL {ΓL} {TL} {UL} tL) (lamC tC)

