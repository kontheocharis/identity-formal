module Model where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; dsubst₂; dcong₂)
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
    Tmz  : ∀ Γ → Ty Γ → Set ℓ'
    Tm  : ∀ Γ A → Tmz Γ A → Set ℓ'
    Ex : Con → Set ℓ'
    $ : Set ℓ
    $∈_ : Con → Set ℓ'
    
module _ (sorts : OpTT-sorts {ℓ} {ℓ'}) where
  open OpTT-sorts sorts

  variable
    Γ Δ Θ : Con
    ρ σ τ : Sub _ _
    A' A B : Ty _
    t u v : Tmz _ _
    t' u' v' : Tm _ _ _
    e f g : Ex _
    μ ν : $
    ξ ϕ : $∈ _

  -- OpTT substitution calculus
  record OpTT-subs : Set (suc (ℓ ⊔ ℓ')) where
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
      _[_]Tmz : Tmz Θ A → (σ : Sub Γ Θ) → Tmz Γ (A [ σ ])
      [id]Tmz : Tmz _ ∣ t [ id ]Tmz ≡[ [id] ] t
      [∘]Tmz : Tmz _ ∣ t [ σ ∘ τ ]Tmz ≡[ [∘] ] (t [ σ ]Tmz) [ τ ]Tmz
      
      -- Relevant terms presheaf
      _[_]Tm : Tm Θ A t → (σ : Sub Γ Θ) → Tm Γ (A [ σ ]) (t [ σ ]Tmz)
      [id]Tm : Tmz _ ∣ t [ id ]Tmz ≡[ [id] ] t
      [∘]Tm : Tmz _ ∣ t [ σ ∘ τ ]Tmz ≡[ [∘] ] (t [ σ ]Tmz) [ τ ]Tmz

      -- Expressions presheaf
      _[_]Ex : Ex Θ → Sub Γ Θ → Ex Γ
      [id]Ex : e [ id ]Ex ≡ e
      [∘]Ex : e [ σ ∘ τ ]Ex ≡ (e [ σ ]Ex) [ τ ]Ex

      -- Expressions presheaf
      _[_]$ : $∈ Θ → Sub Γ Θ → $∈ Γ
      [id]$ : ξ [ id ]$ ≡ ξ
      [∘]$ : ξ [ σ ∘ τ ]$ ≡ (ξ [ σ ]$) [ τ ]$
      
      -- $ is a proposition
      $-prop : μ ≡ ν
      
      -- Terminal object
      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε ≡ σ

      -- Context extension of terms
      _▷[_]_ : (Γ : Con) → Mode → Ty Γ → Con
      p : Sub (Γ ▷[ i ] A) Γ
      q : Tmz (Γ ▷[ i ] A) (A [ p ])
      q' : Tm (Γ ▷[ ω ] A) (A [ p ]) q
      _,[z]_ : (σ : Sub Γ Δ) → Tmz Γ (A [ σ ]) → Sub Γ (Δ ▷[ z ] A)
      _,[ω]_ : (σ : Sub Γ Δ) → ∀ {t} → Tm Γ (A [ σ ]) t → Sub Γ (Δ ▷[ ω ] A)
      ,[z]∘ : (σ ,[z] t) ∘ τ ≡ ((σ ∘ τ) ,[z] subst (Tmz _) (sym [∘]) (t [ τ ]Tmz))
      p,[z]q : p {Γ} {z} {A} ,[z] q ≡ id
      p,[ω]q : p {Γ} {ω} {A} ,[ω] q' ≡ id
      p∘,[z] : p ∘ (σ ,[z] t) ≡ σ
      p∘,[ω] : p ∘ (σ ,[ω] t') ≡ σ
      q[,[z]] : Tmz _ ∣ q [ σ ,[z] t ]Tmz ≡[ (trans (sym [∘]) (cong (A [_]) p∘,[z])) ] t
      q[,[ω]] : Tmz _ ∣ q [ _,[ω]_ σ {t = t} t' ]Tmz ≡[ (trans (sym [∘]) (cong (A [_]) p∘,[ω])) ] t
      q'[,[ω]] : q' [ σ ,[ω] t' ]Tm ≡[ dcong₂ (Tm _) (trans (sym [∘]) (cong (A [_]) p∘,[ω])) q[,[ω]] ] t'
      
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
      q$ : $∈ (Γ ▷$)
      _,$_ : (σ : Sub Γ Δ) → $∈ Γ → Sub Γ (Δ ▷$)
      ,∘$ : (σ ,$ ξ) ∘ τ ≡ (σ ∘ τ) ,$ (ξ [ τ ]$)
      p$,q$ : p$ {Γ} ,$ q$ ≡ id
      p$∘,$ : p$ ∘ (σ ,$ ξ) ≡ σ
      q$[,] : q$ [ σ ,$ ξ ]$ ≡ ξ -- redundant due to prop but whatever
      
      -- Conversion between terms and expressions
      ∣_∣ : Tm (Γ ▷$) A t → Ex Γ
      ∅ : Tmz (Γ ▷$) A
      ∅-sing : ∅ ≡ t
      ⟨_⟩[_] : Ex Γ → ∀ (A : Ty (Γ ▷$)) → Tm (Γ ▷$) A ∅
      ∣⟨⟩∣ : ∣ ⟨ e ⟩[ A ] ∣ ≡ e
      ⟨∣∣⟩ : ⟨ ∣ t' ∣ ⟩[ A ] ≡ t'
    
      
  module _ (subs : OpTT-subs) where
    open OpTT-subs subs public
      
    _⁺Λ : Sub Γ Δ → Sub (Γ ▷Λ) (Δ ▷Λ)
    ρ ⁺Λ = (ρ ∘ pΛ) ,Λ qΛ

    _⁺ : (ρ : Sub Γ Δ) → Sub (Γ ▷[ j ] (A [ ρ ])) (Δ ▷[ j ] A)
    _⁺ {j = z} ρ = (ρ ∘ p) ,[z] coe (cong (Tmz _) (sym [∘])) q
    _⁺ {j = ω} ρ = (ρ ∘ p) ,[ω] coe (dcong₂ (Tm _) (sym [∘]) refl) q'

    _⁺$ : Sub Γ Δ → Sub (Γ ▷$) (Δ ▷$)
    ρ ⁺$ = (ρ ∘ p$) ,$ q$
      
    <_>z : Tmz Γ A → Sub Γ (Γ ▷[ z ] A)
    < t >z = id ,[z] (t [ id ]Tmz)

    <_>ω : Tm Γ A t → Sub Γ (Γ ▷[ ω ] A)
    < t' >ω = id ,[ω] (t' [ id ]Tm)
    
    ↑ : Ty (Γ ▷[ z ] A) → Ty (Γ ▷[ j ] A)
    ↑ {j = z} B = B
    ↑ {j = ω} B = B [ p ,[z] q ]
    
    ↑' : Tmz (Γ ▷[ z ] A) B → Tmz (Γ ▷[ j ] A) (↑ B)
    ↑' {j = z} t = t
    ↑' {j = ω} t = t [ p ,[z] q ]Tmz

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
        Π : (j : Mode) → Ty Γ → Ty (Γ ▷[ z ] A) → Ty Γ
        Π[] : (Π j A B) [ σ ] ≡ Π j (A [ σ ]) (B [ σ ⁺ ])
        lam : Tmz (Γ ▷[ z ] A) B → Tmz Γ (Π j A B)
        lam[] : Tmz _ ∣ (lam {Γ} {A} {B} {j} t) [ σ ]Tmz ≡[ Π[] ] lam (t [ σ ⁺ ]Tmz)
        app : Tmz Γ (Π j A B) → Tmz (Γ ▷[ z ] A) B
        lam-app : app {Γ} {j} (lam t) ≡ t
        app-lam : lam (app t) ≡ t

        lam' : Tm (Γ ▷[ j ] A) (↑ B) (↑' t) → Tm Γ (Π j A B) (lam t)
        app'ω : Tm Γ (Π ω A B) t → Tm Γ A u → Tm Γ (B [ < u >z ]) (app t [ < u >z ]Tmz)
        app'z : Tm Γ (Π z A B) t → (u : Tmz Γ A) → Tm Γ (B [ < u >z ]) (app t [ < u >z ]Tmz)
        
        ∣lam'∣ : ∣ lam' {j = ω} {t = t} t' ∣ ≡ lamΛ (∣ t' [ (pΛ ⁺$) ,[ω] ⟨ qΛ ⟩[ _ ] ]Tm ∣)
        ∣lamz∣ : ∣ lam' {j = z} t' ∣ ≡ ∣ t' [ id ,[z] ∅ ]Tm ∣
        ∣appω∣ : ∣ app'ω t' u' ∣ ≡ appΛ ∣ t' ∣ ∣ u' ∣
        ∣appz∣ : ∣ app'z t' u ∣ ≡ ∣ t' ∣

record OpTT : Set (suc (ℓ ⊔ ℓ')) where
  field
    sorts : OpTT-sorts {ℓ} {ℓ'}
  open OpTT-sorts sorts public
  field
    subs : OpTT-subs sorts
  open OpTT-subs subs public
  field
    str : OpTT-str sorts subs
  open OpTT-str str public