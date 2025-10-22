module Model where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
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
    Subz : Con → Con → Set ℓ'
    Ty : Con → Set ℓ
    Tmz  : ∀ Γ → Ty Γ → Set ℓ'
    Tm  : ∀ Γ A → Tmz Γ A → Set ℓ'
    Sub : ∀ Γ Δ → Subz Γ Δ → Set ℓ'
    Ex : Con → Set ℓ'
    $ : Con → Set ℓ
    
module _ (sorts : OpTT-sorts {ℓ} {ℓ'}) where
  open OpTT-sorts sorts

  variable
    Γ Δ Θ : Con
    ρ σ τ : Subz _ _
    ρ' σ' τ' : Sub _ _ _
    A' A B : Ty _
    t u v : Tmz _ _
    t' u' v' : Tm _ _ _
    e f g : Ex _
    μ ν : $ _

  -- OpTT substitution calculus
  record OpTT-subst : Set (suc (ℓ ⊔ ℓ')) where
    field
      -- Category
      id : Subz Γ Γ
      _∘_ : Subz Δ Θ → Subz Γ Δ → Subz Γ Θ
      assoc : (ρ ∘ (σ ∘ τ)) ≡ ((ρ ∘ σ) ∘ τ)
      ∘id : (id ∘ σ) ≡ σ
      id∘ : (σ ∘ id) ≡ σ

      -- Displayed category
      id' : Sub Γ Γ id
      _∘'_ : Sub Δ Θ τ → Sub Γ Δ σ → Sub Γ Θ (τ ∘ σ)
      assoc' : (ρ' ∘' (σ' ∘' τ')) ≡[ cong (Sub _ _) assoc ] ((ρ' ∘' σ') ∘' τ')
      ∘id' : (id' ∘' σ') ≡[ cong (Sub _ _) ∘id ] σ'
      id∘' : (σ' ∘' id') ≡[ cong (Sub _ _) id∘ ] σ'
      
      -- Types presheaf
      _[_] : Ty Θ → Subz Γ Θ → Ty Γ
      [id] : A [ id ] ≡ A
      [∘] : A [ σ ∘ τ ] ≡ (A [ σ ]) [ τ ]
      
      -- Terms presheaf
      _[_]Tmz : Tmz Θ A → (σ : Subz Γ Θ) → Tmz Γ (A [ σ ])
      [id]Tmz : t [ id ]Tmz ≡[ cong (Tmz _) [id] ] t
      [∘]Tmz : t [ σ ∘ τ ]Tmz ≡[ cong (Tmz _) [∘] ] (t [ σ ]Tmz) [ τ ]Tmz
      
      -- Relevant terms presheaf
      _[_]Tm : Tm Θ A t → Sub Γ Θ σ → Tm Γ (A [ σ ]) (t [ σ ]Tmz)
      [id]Tm : t [ id ]Tmz ≡[ cong (Tmz _) [id] ] t
      [∘]Tm : t [ σ ∘ τ ]Tmz ≡[ cong (Tmz _) [∘] ] (t [ σ ]Tmz) [ τ ]Tmz

      -- Expressions presheaf
      _[_]Ex : Ex Θ → (σ : Subz Γ Θ) → Ex Γ
      [id]Ex : e [ id ]Ex ≡ e
      [∘]Ex : e [ σ ∘ τ ]Ex ≡ (e [ σ ]Ex) [ τ ]Ex
      
      -- $ presheaf
      _[_]$ : $ Θ → (σ : Subz Γ Θ) → $ Γ
      [id]$ : μ [ id ]$ ≡ μ
      [∘]$ : μ [ σ ∘ τ ]$ ≡ (μ [ σ ]$) [ τ ]$
      
      -- $ is a proposition
      $-prop : μ ≡ ν
      
      -- Terminal object
      ∙ : Con
      ε : Subz Γ ∙
      ε' : Sub Γ ∙ ε
      ∃!ε : ε ≡ σ
      ∃!ε' : ε' ≡[ cong (Sub _ _) ∃!ε ] σ'

      -- Context extension of terms
      _▷[_]_ : (Γ : Con) → Mode → Ty Γ → Con
      p : Subz (Γ ▷[ i ] A) Γ
      q : Tmz (Γ ▷[ i ] A) (A [ p ])
      _,[_]_ : (σ : Subz Γ Δ) → (i : Mode) → Tmz Γ (A [ σ ]) → Subz Γ (Δ ▷[ i ] A)
      ,∘ : (σ ,[ i ] t) ∘ τ ≡ ((σ ∘ τ) ,[ i ] subst (Tmz _) (sym [∘]) (t [ τ ]Tmz))
      p,q : p {Γ} {i} {A} ,[ i ] q ≡ id
      p∘, : p ∘ (σ ,[ i ] t) ≡ σ
      q[,] : q [ σ ,[ i ] t ]Tmz ≡[ cong (Tmz _) (trans (sym [∘]) (cong (A [_]) p∘,)) ] t

      -- Context extension of relevant terms 
      p' : Sub (Γ ▷[ i ] A) Γ p
      q' : Tm (Γ ▷[ ω ] A) (A [ p ]) q
      _,[z]'_ : (σ' : Sub Γ Δ σ) → (t : Tmz Γ (A [ σ ])) → Sub Γ (Δ ▷[ z ] A) (σ ,[ z ] t)
      _,[ω]'_ : (σ' : Sub Γ Δ σ) → Tm Γ (A [ σ ]) t → Sub Γ (Δ ▷[ ω ] A) (σ ,[ ω ] t)
      ,[z]∘' : {τ' : Sub Γ Δ τ} → (σ' ,[z]' t) ∘' τ'
                ≡[ cong (Sub _ _) ,∘ ] (σ' ∘' τ') ,[z]' subst (Tmz _) (sym [∘]) (t [ τ ]Tmz)
      ,[ω]∘' : {τ' : Sub Γ Δ τ} → (σ' ,[ω]' t') ∘' τ'
                ≡[ cong (Sub _ _) ,∘ ] (σ' ∘' τ') ,[ω]' subst (λ p → Tm _ _ {!   !}) (sym [∘]Tm) (t' [ τ' ]Tm)

    --   -- Variables for relevant terms
    --   q' : Tm (Γ ▷[ ω ] A) (A [ p ]) q
    --   _[p]' : Tm Γ A t → Tm (Γ ▷[ ω ] A) (A [ p ]) (t [ p ]Tmz)
    --   _[<_>]' : Tm (Γ ▷[ ω ] A) B t → Tm Γ A u → Tm Γ (B [ < u > ]) (t [ < u > ]Tmz)
      
      -- Context extension of expressions
      _▷Λ : Con → Con
      pΛ : Subz (Γ ▷Λ) Γ
      qΛ : Ex (Γ ▷Λ)
      _,Λ_ : (σ : Subz Γ Δ) → Ex Γ → Subz Γ (Δ ▷Λ)
      ,∘Λ : (σ ,Λ e) ∘ τ ≡ (σ ∘ τ) ,Λ (e [ τ ]Ex)
      pΛ,qΛ : pΛ {Γ} ,Λ qΛ ≡ id
      pΛ∘,Λ : pΛ ∘ (σ ,Λ e) ≡ σ
      qΛ[,] : qΛ [ σ ,Λ e ]Ex ≡ e
      
      -- Context extension of $
      _▷$ : Con → Con
      p$ : Subz (Γ ▷$) Γ
      q$ : $ (Γ ▷$)
      _,$_ : (σ : Subz Γ Δ) → $ Γ → Subz Γ (Δ ▷$)
      ,∘$ : (σ ,$ μ) ∘ τ ≡ (σ ∘ τ) ,$ (μ [ τ ]$)
      p$,q$ : p$ {Γ} ,$ q$ ≡ id
      p$∘,$ : p$ ∘ (σ ,$ μ) ≡ σ
      q$[,] : q$ [ σ ,$ μ ]$ ≡ μ
      
      -- Conversion between terms and expressions
      ∣_∣ : Tm (Γ ▷$) A t → Ex Γ
      ⟨_⟩[_][_] : Ex Γ → ∀ (A : Ty (Γ ▷$)) t → Tm (Γ ▷$) A t
      ∣⟨⟩∣ : ∣ ⟨ e ⟩[ A ][ t ] ∣ ≡ e
      ⟨∣∣⟩ : ⟨ ∣ t' ∣ ⟩[ A ][ t ] ≡ t'
      ∅ : Tmz (Γ ▷$) A
      ∅-sing : ∅ ≡ t
      
    _⁺Λ : Subz Γ Δ → Subz (Γ ▷Λ) (Δ ▷Λ)
    ρ ⁺Λ = (ρ ∘ pΛ) ,Λ qΛ

    _⁺ : (ρ : Subz Γ Δ) → Subz (Γ ▷[ j ] (A [ ρ ])) (Δ ▷[ j ] A)
    ρ ⁺ = (ρ ∘ p) ,[ _ ] coe (cong (Tmz _) (sym [∘])) q
    
    _⁺$ : Subz Γ Δ → Subz (Γ ▷$) (Δ ▷$)
    ρ ⁺$ = (ρ ∘ p$) ,$ q$
    
    <_> : Tmz Γ A → Subz Γ (Γ ▷[ j ] A)
    < t > = id ,[ _ ] (t [ id ]Tmz)
    
      
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
        
        lam : Tmz (Γ ▷[ j ] A) B → Tmz Γ (Π j A B)
        lam[] : (lam t) [ σ ]Tmz ≡[ cong (Tmz _) Π[] ] lam (t [ σ ⁺ ]Tmz)

        app : Tmz Γ (Π j A B) → Tmz (Γ ▷[ j ] A) B

        lam' : Tm (Γ ▷[ j ] A) B t → Tm Γ (Π j A B) (lam t)
        app'ω : Tm Γ (Π ω A B) t → Tm Γ A u → Tm Γ (B [ < u > ]) (app t [ < u > ]Tmz)
        app'z : Tm Γ (Π z A B) t → (u : Tmz Γ A) → Tm Γ (B [ < u > ]) (app t [ < u > ]Tmz)
        
        
        -- ∣lam'∣ : ∣ lam' {j = ω} t' ∣ ≡ lamΛ (∣ {! t' [< ? >]' !} ∣)
--         -- ∣lamz∣ : ∣ lam {i = ω} {j = z} t ∣ ≡ ∣ t [ id , ∅ ]Tm ∣
--         -- ∣appω∣ : ∣ (app {i = ω} {j = ω} t) [ (p$ ∘ σ) , u ]Tm ∣ ≡ {!   !}

--         -- Nat : Ty Γ
--         -- Nat[] : (Nat) [ σ ] ≡ Nat
--         -- zero : Tm i Γ Nat
--         -- zero[] : (zero) [ σ ]Tm ≡[ cong (Tm _ _) Nat[] ] zero
--         -- succ : Tm i Γ Nat → Tm i Γ Nat
--         -- succ[] : (suc t) [ σ ]Tm ≡[ cong (Tm _ _) Nat[] ] succ (t [ σ ]Tm)

-- -- record OpTT : Set (suc (ℓ ⊔ ℓ')) where
-- --   field
-- --     sorts : OpTT-sorts {ℓ} {ℓ'}
-- --   open OpTT-sorts sorts public
-- --   field
-- --     subst : OpTT-subst sorts
-- --   open OpTT-subst subst public
-- --   field
-- --     str : OpTT-str sorts subst
-- --   open OpTT-str str public