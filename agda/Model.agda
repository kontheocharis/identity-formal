module Model where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; dcong₂; trans; sym)
open import Level using (Level; _⊔_; suc)

open import Utils

data Mode : Set where
  z : Mode
  ω : Mode
  
_*_ : Mode → Mode → Mode
z * j = z
j * z = z
ω * ω = ω

variable
  i j : Mode

data _≤_ : Mode → Mode → Set where
  z≤_ : (j : Mode) → z ≤ j
  ω≤ω : ω ≤ ω
  
reflex : ∀ {m} → m ≤ m
reflex {z} = z≤ z
reflex {ω} = ω≤ω
  
variable
  prf : _ ≤ _

-- OpTT sorts
record OpTT-sorts : Set (suc (ℓ ⊔ ℓ')) where
  field
    Con : Set ℓ
    Sub : Con → Con → Set ℓ'
    Ty : Con → Set ℓ
    Tm  : Mode → ∀ Γ → Ty Γ → Set ℓ'
    Ex : Con → Set ℓ'
    $ : Con → Set ℓ
    
module _ (sorts : OpTT-sorts {ℓ} {ℓ'}) where
  open OpTT-sorts sorts

  variable
    Γ Δ Θ : Con
    ρ σ τ : Sub _ _
    A' A B : Ty _
    t u v : Tm _ _ _
    e f g : Ex _
    μ ν : $ _

  -- OpTT substitution calculus
  record OpTT-subst : Set (suc (ℓ ⊔ ℓ')) where
    field
      -- Category
      id : Sub Γ Γ
      _∘_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
      assoc : (ρ ∘ (σ ∘ τ)) ≡ ((ρ ∘ σ) ∘ τ)
      ∘id : (id ∘ σ) ≡ σ
      id∘ : (σ ∘ id) ≡ σ
      
      -- Types presheaf
      _[_] : Ty Θ → Sub Γ Θ → Ty Γ
      [id] : A [ id ] ≡ A
      [∘] : A [ σ ∘ τ ] ≡ (A [ σ ]) [ τ ]
      
      -- Terms presheaf
      _[_]Tm : Tm i Θ A → (σ : Sub Γ Θ) → Tm i Γ (A [ σ ])
      [id]Tm : t [ id ]Tm ≡[ cong (Tm _ _) [id] ] t
      [∘]Tm : t [ σ ∘ τ ]Tm ≡[ cong (Tm _ _) [∘] ] (t [ σ ]Tm) [ τ ]Tm
      
      -- Expressions presheaf
      _[_]Ex : Ex Θ → (σ : Sub Γ Θ) → Ex Γ
      [id]Ex : e [ id ]Ex ≡ e
      [∘]Ex : e [ σ ∘ τ ]Ex ≡ (e [ σ ]Ex) [ τ ]Ex
      
      -- $ presheaf
      _[_]$ : $ Θ → (σ : Sub Γ Θ) → $ Γ
      [id]$ : μ [ id ]$ ≡ μ
      [∘]$ : μ [ σ ∘ τ ]$ ≡ (μ [ σ ]$) [ τ ]$
      
      -- $ is a proposition
      $-prop : μ ≡ ν
      
      -- Terminal object
      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε ≡ σ

      -- Natural transformation of terms (should be derivable in the syntax)
      0×_ : Tm i Γ A → Tm z Γ A
      0×0 : 0× t ≡ t
      0×[] : (0× t) [ σ ]Tm ≡ 0× (t [ σ ]Tm)

      -- Context extension of terms
      _▷[_]_ : (Γ : Con) → Mode → Ty Γ → Con
      p : Sub (Γ ▷[ i ] A) Γ
      q : j ≤ i → Tm j (Γ ▷[ i ] A) (A [ p ])
      _,_ : (σ : Sub Γ Δ) → Tm i Γ (A [ σ ]) → Sub Γ (Δ ▷[ i ] A)
      ,∘ : (σ , t) ∘ τ ≡ (σ ∘ τ) , coe (cong (Tm _ _) (sym [∘]))(t [ τ ]Tm)
      p,q : p {Γ} {i} {A} , q reflex ≡ id
      p∘, : p ∘ (σ , t) ≡ σ
      qω[,] : q {A = A} ω≤ω [ σ , t ]Tm ≡[ cong (Tm _ _) (trans (sym [∘]) (cong (A [_]) p∘,)) ] t
      qz[,] : q {A = A} (z≤ i) [ σ , t ]Tm ≡[ cong (Tm _ _) (trans (sym [∘]) (cong (A [_]) p∘,)) ] (0× t)
      
      -- Context extension of expressions
      _▷Λ : Con → Con
      pΛ : Sub (Γ ▷Λ) Γ
      qΛ : Ex (Γ ▷Λ)
      _,Λ_ : (σ : Sub Γ Δ) → Ex Γ → Sub Γ (Δ ▷Λ)
      ,∘Λ : (σ ,Λ e) ∘ τ ≡ (σ ∘ τ) ,Λ (e [ τ ]Ex)
      pΛ,qΛ : pΛ {Γ} ,Λ qΛ ≡ id
      pΛ∘,Λ : pΛ ∘ (σ ,Λ e) ≡ σ
      qΛ[,] : qΛ [ σ ,Λ e ]Ex ≡ e
      
      -- Context extension of $
      _▷$ : Con → Con
      p$ : Sub (Γ ▷$) Γ
      q$ : $ (Γ ▷$)
      _,$_ : (σ : Sub Γ Δ) → $ Γ → Sub Γ (Δ ▷$)
      ,∘$ : (σ ,$ μ) ∘ τ ≡ (σ ∘ τ) ,$ (μ [ τ ]$)
      p$,q$ : p$ {Γ} ,$ q$ ≡ id
      p$∘,$ : p$ ∘ (σ ,$ μ) ≡ σ
      q$[,] : q$ [ σ ,$ μ ]$ ≡ μ
      
      -- Conversion between terms and expressions
      ∣_∣ : Tm ω (Γ ▷$) A → Ex Γ
      ⟨_⟩[_] : Ex Γ → (A : Ty (Γ ▷$)) → Tm ω (Γ ▷$) A
      ∣⟨⟩∣ : ∣ ⟨ e ⟩[ A ] ∣ ≡ e
      ⟨∣∣⟩ : ⟨ ∣ t ∣ ⟩[ A ] ≡ t
      ∅ : Tm z (Γ ▷$) A
      ∅-sing : ∅ ≡ t
      
    _⁺Λ : Sub Γ Δ → Sub (Γ ▷Λ) (Δ ▷Λ)
    ρ ⁺Λ = (ρ ∘ pΛ) ,Λ qΛ

    _⁺ : (ρ : Sub Γ Δ) → Sub (Γ ▷[ j ] (A [ ρ ])) (Δ ▷[ j ] A)
    ρ ⁺ = (ρ ∘ p) , coe (cong (Tm _ _) (sym [∘])) (q reflex)
    
    _⁺$ : Sub Γ Δ → Sub (Γ ▷$) (Δ ▷$)
    ρ ⁺$ = (ρ ∘ p$) ,$ q$
    
      
  module _ (subst : OpTT-subst) where
    open OpTT-subst subst public

    -- OpTT structures
    record OpTT-str : Set (suc (ℓ ⊔ ℓ')) where
      field
        -- Expressions
        lamΛ : Ex (Γ ▷Λ) → Ex Γ
        lamΛ[] : (lamΛ e) [ σ ]Ex ≡ lamΛ (e [ σ ⁺Λ ]Ex)

        appΛ : Ex Γ → Ex Γ → Ex Γ
        app[] : (appΛ e f) [ σ ]Ex ≡ appΛ (e [ σ ]Ex) (f [ σ ]Ex)
        
        zeroΛ : Ex Γ
        zero[] : (zeroΛ) [ σ ]Ex ≡ zeroΛ

        succΛ : Ex Γ → Ex Γ
        succ[] : (succΛ e) [ σ ]Ex ≡ succΛ (e [ σ ]Ex)
        
        recΛ : Ex Γ → Ex (Γ ▷Λ ▷Λ) → Ex Γ → Ex Γ
        rec[] : (recΛ e f g) [ σ ]Ex ≡ recΛ (e [ σ ]Ex) (f [ σ ⁺Λ ⁺Λ ]Ex) (g [ σ ]Ex)
        
        -- Terms
        Π : (j : Mode) → Ty Γ → Ty (Γ ▷[ j ] A) → Ty Γ
        Π[] : (Π j A B) [ σ ] ≡ Π j (A [ σ ]) (B [ σ ⁺ ])
        
        lam : Tm i (Γ ▷[ j ] A) B → Tm i Γ (Π j A B)
        lam[] : (lam t) [ σ ]Tm ≡[ cong (Tm _ _) Π[] ] lam (t [ σ ⁺ ]Tm)

        app : Tm i Γ (Π j A B) → Tm i (Γ ▷[ j ] A) B
        
      app' : Tm i Γ (Π j A B) → (a : Tm (i * j) Γ A) → Tm i Γ (B [ id , ({!   !} [ id ]Tm) ])
      app' t u = {!   !}
        
      field
        
        ∣lamω∣ : ∣ lam {i = ω} {j = ω} t ∣ ≡ lamΛ (∣ t [ (pΛ ⁺$) , ⟨ qΛ ⟩[ _ ] ]Tm ∣)
        ∣lamz∣ : ∣ lam {i = ω} {j = z} t ∣ ≡ ∣ t [ id , ∅ ]Tm ∣
        ∣appω∣ : ∣ (app {i = ω} {j = ω} t) [ (p$ ∘ σ) , u ]Tm ∣ ≡ {!   !}

        -- Nat : Ty Γ
        -- Nat[] : (Nat) [ σ ] ≡ Nat
        -- zero : Tm i Γ Nat
        -- zero[] : (zero) [ σ ]Tm ≡[ cong (Tm _ _) Nat[] ] zero
        -- succ : Tm i Γ Nat → Tm i Γ Nat
        -- succ[] : (suc t) [ σ ]Tm ≡[ cong (Tm _ _) Nat[] ] succ (t [ σ ]Tm)

record OpTT : Set (suc (ℓ ⊔ ℓ')) where
  field
    sorts : OpTT-sorts {ℓ} {ℓ'}
  open OpTT-sorts sorts public
  field
    subst : OpTT-subst sorts
  open OpTT-subst subst public
  field
    str : OpTT-str sorts subst
  open OpTT-str str public