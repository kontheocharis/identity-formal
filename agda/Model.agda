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

  ⟨_⟩C : ∀ {ΓC} → TmC ΓC → SubC ΓC (ΓC ▷C)
  ⟨ t ⟩C = idC ,C t
    
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
    
    recC : ∀ {ΓC} → TmC ΓC → TmC (ΓC ▷C) → TmC ΓC → TmC ΓC
    recC[] : ∀ {ΓC ΔC z s n} {σ : SubC ΔC ΓC}
      → (recC {ΓC} z s n) [ σ ]C ≡ recC (z [ σ ]C) (s [ σ ⁺C ]C) (n [ σ ]C)
    

    recC-η1 : ∀ {ΓC n} → recC {ΓC} zeroC (succC qC) n ≡ n
    recC-β-zero : ∀ {ΓC z s} → recC {ΓC} z s zeroC ≡ z
    recC-β-succ : ∀ {ΓC z s n} → recC {ΓC} z s (succC n) ≡ s [ ⟨ recC z s n ⟩C ]C

record TT-Logic : Set2 where
  field
    comp : TT-Comp
  open TT-Comp comp public

  field
    -- Logical
    
    -- Sorts
    ConL : Set1
    SubL : ConL → ConL → Set
    Ty : ConL → Set1
    TmL : ∀ ΓL → Ty ΓL → Set
    
    -- Category
    idL : ∀ {ΓL} → SubL ΓL ΓL
    _∘L_ : ∀ {ΓL ΔL ΘL} → (σ : SubL ΔL ΘL) → (τ : SubL ΓL ΔL) → SubL ΓL ΘL
    assocL : ∀ {ΓL ΔL ΘL ΞL} {ρ : SubL ΘL ΞL} {σ : SubL ΔL ΘL} {τ : SubL ΓL ΔL}
      → (ρ ∘L (σ ∘L τ)) ≡ ((ρ ∘L σ) ∘L τ)
    ∘idL : ∀ {ΓL ΔL} {σ : SubL ΓL ΔL} → (idL ∘L σ) ≡ σ
    idL∘ : ∀ {ΓL ΔL} {σ : SubL ΓL ΔL} → (σ ∘L idL) ≡ σ
    
    -- Presheaf actions
    _[_]T : ∀ {ΓL ΔL} → Ty ΔL → SubL ΓL ΔL → Ty ΓL
    _[_]L : ∀ {ΓL ΔL AL} → TmL ΔL AL → (σ : SubL ΓL ΔL) → TmL ΓL (AL [ σ ]T)
    [id]T : ∀ {ΓL} {A : Ty ΓL} → A [ idL ]T ≡ A
    [id]L : ∀ {ΓL AL} {t : TmL ΓL AL} → t [ idL ]L ≡[ cong (TmL ΓL) [id]T ] t
    [∘]T : ∀ {ΓL ΔL ΘL} {A : Ty ΘL} {σ : SubL ΔL ΘL} {τ : SubL ΓL ΔL}
      → A [ σ ∘L τ ]T ≡ (A [ σ ]T) [ τ ]T
    [∘]L : ∀ {ΓL ΔL ΘL AL} {t : TmL ΘL AL} {σ : SubL ΔL ΘL} {τ : SubL ΓL ΔL}
      → t [ σ ∘L τ ]L ≡[ cong (TmL ΓL) [∘]T ] (t [ σ ]L) [ τ ]L
  
  coeL : ∀ {ΓL AL BL} → AL ≡ BL → TmL ΓL AL → TmL ΓL BL
  coeL p t = subst (TmL _) p t
      
  field
      
    -- Terminal object
    ∙L : ConL
    εL : ∀ {ΓL} → SubL ΓL ∙L
    ∃!εL : ∀ {ΓL} σ → εL {ΓL} ≡ σ
    
    -- Context extension
    _▷L_ : (ΓL : ConL) → Ty ΓL → ConL
    pL : ∀ {ΓL AL} → SubL (ΓL ▷L AL) ΓL
    qL : ∀ {ΓL AL} → TmL (ΓL ▷L AL) (AL [ pL ]T)
    _,L_ : ∀ {ΓL ΔL AL} → (σ : SubL ΓL ΔL) → TmL ΓL (AL [ σ ]T) → SubL ΓL (ΔL ▷L AL)
    ,L∘ : ∀ {ΓL ΔL ΘL} {AL : Ty ΔL} {σ : SubL ΓL ΔL} {σ' : SubL ΘL ΓL} {t : TmL ΓL (AL [ σ ]T)}
      → (σ ,L t) ∘L σ' ≡ (σ ∘L σ') ,L coeL (sym [∘]T) (t [ σ' ]L)
    pL,qL : ∀ {ΓL AL} → (pL {ΓL} {AL} ,L qL) ≡ idL
    pL∘, : ∀ {ΓL ΔL AL} {σ : SubL ΓL ΔL} {t : TmL ΓL (AL [ σ ]T)}
      → pL ∘L (σ ,L t) ≡ σ
    qL[,] : ∀ {ΓL ΔL AL} {σ : SubL ΓL ΔL} {t : TmL ΓL (AL [ σ ]T)}
      → qL [ σ ,L t ]L ≡[ cong (TmL ΓL) (trans (sym [∘]T) (cong (AL [_]T) pL∘,)) ] t


  ⟨_⟩L : ∀ {ΓL AL} → TmL ΓL AL → SubL ΓL (ΓL ▷L AL)
  ⟨ t ⟩L = idL ,L (t [ idL ]L)
    
  _⁺L : ∀ {ΓL ΔL A} → (σ : SubL ΓL ΔL) → SubL (ΓL ▷L (A [ σ ]T)) (ΔL ▷L A)
  σ ⁺L = (σ ∘L pL) ,L subst (TmL _) (sym [∘]T) qL
  
  [pL][σ⁺]≡[σ][pL] : ∀ {ΓL ΔL AL BL} {σ : SubL ΓL ΔL} → (AL [ pL {ΔL} {BL} ]T) [ σ ⁺L ]T ≡ (AL [ σ ]T) [ pL ]T
  [pL][σ⁺]≡[σ][pL] {AL = AL} = trans (sym [∘]T) (trans (cong (AL [_]T) pL∘,) ([∘]T))
  
  field
    -- Terms

    -- Functions
    Π : ∀ {ΓL} → (TL : Ty ΓL) → Ty (ΓL ▷L TL) → Ty ΓL
    Π[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} {T : Ty ΓL} {U : Ty (ΓL ▷L T)}
      → (Π T U) [ σ ]T ≡ Π (T [ σ ]T) (U [ σ ⁺L ]T)

    lamL : ∀ {ΓL TL UL} → TmL (ΓL ▷L TL) UL → TmL ΓL (Π TL UL)
    lamL[] : ∀ {ΓL ΔL T U t} {σ : SubL ΔL ΓL}
      → (lamL {ΓL} {T} {U} t) [ σ ]L ≡[ cong (TmL _) Π[] ] lamL (t [ σ ⁺L ]L)
    apL : ∀ {ΓL TL UL} → TmL ΓL (Π TL UL) → TmL (ΓL ▷L TL) UL
    βL : ∀ {ΓL TL UL} t → apL {ΓL} {TL} {UL} (lamL t) ≡ t
    ηL : ∀ {ΓL TL UL} t → lamL {ΓL} {TL} {UL} (apL t) ≡ t
    
    -- Universe
    U : ∀ {ΓL} → Ty ΓL
    U[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} → U [ σ ]T ≡ U
    
    El : ∀ {ΓL} → TmL ΓL U → Ty ΓL
    El[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} {a : TmL ΓL U}
      → (El a) [ σ ]T ≡ El (subst (TmL _) U[] (a [ σ ]L))
      
    -- Natural numbers
    Nat : ∀ {ΓL} → Ty ΓL
    Nat[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} → Nat [ σ ]T ≡ Nat
    zeroL : ∀ {ΓL} → TmL ΓL Nat
    zeroL[] : ∀ {ΓL ΔL} {σ : SubL ΔL ΓL} → (zeroL {ΓL}) [ σ ]L ≡[ cong (TmL _) Nat[] ] zeroL
    succL : ∀ {ΓL} → TmL ΓL Nat → TmL ΓL Nat
    succL[] : ∀ {ΓL ΔL t} {σ : SubL ΔL ΓL}
      → (succL {ΓL} t) [ σ ]L ≡[ cong (TmL _) Nat[] ] succL (coeL Nat[] (t [ σ ]L))


    -- We should really have the proper eliminator but we don't do it here
    -- because the substitution calculus gets out of hand.
    recL : ∀ {ΓL} → (P : Ty ΓL)
      → TmL ΓL P
      → TmL (ΓL ▷L P) (P [ pL ]T)
      → (n : TmL ΓL Nat)
      → TmL ΓL P
    recL[] : ∀ {ΓL ΔL P z s n} {σ : SubL ΔL ΓL}
      → (recL {ΓL} P z s n) [ σ ]L
        ≡
        recL {ΔL} (P [ σ ]T) (z [ σ ]L)
        (coeL [pL][σ⁺]≡[σ][pL] (s [ σ ⁺L ]L))
        (coeL Nat[] (n [ σ ]L))
    
    -- Specialization types
    Spec : ∀ {ΓL} → Ty ΓL → (c : TmC ∙C) → Ty ΓL
    specL : ∀ {ΓL TL c} → TmL ΓL TL → TmL ΓL (Spec TL c)
    unspecL : ∀ {ΓL TL c} → TmL ΓL (Spec TL c) → TmL ΓL TL
    specL-unspecL : ∀ {ΓL TL c} {t : TmL ΓL TL} → unspecL {c = c} (specL t) ≡ t
    unspecL-specL : ∀ {ΓL TL c} {t : TmL ΓL (Spec TL c)} → specL (unspecL t) ≡ t


record TT : Set2 where
  field
    logic : TT-Logic

  open TT-Logic logic public
    
  field
    -- Total
    
    -- Sorts

    -- No need to encode substitutions here, we don't actually use them for
    -- anything.
    Con : ConL → ConC → Set1
    Tm : ∀ {ΓL ΓC} → Con ΓL ΓC → (TL : Ty ΓL) → TmL ΓL TL → TmC ΓC → Set
    
    -- Context
    ∙ : Con ∙L ∙C
    _▷_ : ∀ {ΓL ΓC} → Con ΓL ΓC → (TL : Ty ΓL) → Con (ΓL ▷L TL) (ΓC ▷C)
    _▷0_ : ∀ {ΓL ΓC} → Con ΓL ΓC → (TL : Ty ΓL) → Con (ΓL ▷L TL) ΓC
    
    -- Terms
    
    -- Variables
    q : ∀ {ΓL ΓC AL Γ} → Tm {ΓL ▷L AL} {ΓC ▷C} (Γ ▷ AL) (AL [ pL ]T) qL qC
    _[p] : ∀ {ΓL ΓC AL Γ aL aC}
      → Tm Γ AL aL aC → Tm {ΓL ▷L AL} {ΓC ▷C} (Γ ▷ AL) (AL [ pL ]T) (aL [ pL ]L) (aC [ pC ]C)

    -- Functions
    lam : ∀ {ΓL ΓC TL UL tL tC Γ}
      → Tm {ΓL ▷L TL} {ΓC ▷C} (Γ ▷ TL) UL tL tC → Tm Γ (Π TL UL) (lamL tL) (lamC tC)
    app : ∀ {ΓL ΓC TL UL fL fC tL tC Γ}
      → Tm {ΓL} {ΓC} Γ (Π TL UL) fL fC → Tm Γ TL tL tC
      → Tm Γ (UL [ ⟨ tL ⟩L ]T) (apL fL [ ⟨ tL ⟩L ]L) (appC fC tC)
      
    -- Natural numbers
    zero : ∀ {ΓL ΓC Γ} → Tm {ΓL} {ΓC} Γ Nat zeroL zeroC
    succ : ∀ {ΓL ΓC Γ nL nC} → Tm {ΓL} {ΓC} Γ Nat nL nC → Tm {ΓL} {ΓC} Γ Nat (succL nL) (succC nC)
    rec : ∀ {ΓL ΓC P zL zC sL sC nL nC Γ}
      → Tm {ΓL} {ΓC} Γ Nat nL nC
      → Tm {ΓL} {ΓC} Γ P zL zC
      → Tm {ΓL ▷L P} {ΓC ▷C} (Γ ▷ P) (P [ pL ]T) sL sC
      → Tm {ΓL} {ΓC} Γ P (recL P zL sL nL) (recC zC sC nC) 

    -- Specialisations
    spec : ∀ {ΓL ΓC Γ T aL aC} → Tm {ΓL} {ΓC} Γ T aL (aC [ εC ]C) → Tm Γ (Spec T aC) (specL aL) (aC [ εC ]C)
    unspec : ∀ {ΓL ΓC Γ T aC aL aC'} → Tm {ΓL} {ΓC} Γ (Spec T aC) aL aC' → Tm Γ T (unspecL aL) (aC [ εC ]C)


