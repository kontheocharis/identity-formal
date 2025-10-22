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
    Subz : Con → Con → Set ℓ'
    Ty : Con → Set ℓ
    Tmz  : ∀ Γ → Ty Γ → Set ℓ'
    Tm  : ∀ Γ A → Tmz Γ A → Set ℓ'
    Sub : ∀ Γ Δ → Subz Γ Δ → Set ℓ'
    Exz : Con → Set ℓ'
    Ex : ∀ Γ → Exz Γ → Set ℓ'
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
    e f g : Exz _
    e' f' g' : Ex _ _
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
      assoc' : Sub _ _ ∣ (ρ' ∘' (σ' ∘' τ')) ≡[ assoc ] ((ρ' ∘' σ') ∘' τ')
      ∘id' : Sub _ _ ∣ (id' ∘' σ') ≡[ ∘id ] σ'
      id∘' : Sub _ _ ∣ (σ' ∘' id') ≡[ id∘ ] σ'
      
      -- Types presheaf
      _[_] : Ty Θ → Subz Γ Θ → Ty Γ
      [id] : A [ id ] ≡ A
      [∘] : A [ σ ∘ τ ] ≡ (A [ σ ]) [ τ ]
      
      -- Terms presheaf
      _[_]Tmz : Tmz Θ A → (σ : Subz Γ Θ) → Tmz Γ (A [ σ ])
      [id]Tmz : Tmz _ ∣ t [ id ]Tmz ≡[ [id] ] t
      [∘]Tmz : Tmz _ ∣ t [ σ ∘ τ ]Tmz ≡[ [∘] ] (t [ σ ]Tmz) [ τ ]Tmz
      
      -- Relevant terms presheaf
      _[_]Tm : Tm Θ A t → Sub Γ Θ σ → Tm Γ (A [ σ ]) (t [ σ ]Tmz)
      [id]Tm : Tmz _ ∣ t [ id ]Tmz ≡[ [id] ] t
      [∘]Tm : Tmz _ ∣ t [ σ ∘ τ ]Tmz ≡[ [∘] ] (t [ σ ]Tmz) [ τ ]Tmz

      -- Expressions presheaf
      -- _[_]Ex : Ex Θ → Sub Γ Θ σ → Ex Γ
      -- [id]Ex : e [ id' ]Ex ≡ e
      -- [∘]Ex : e [ σ' ∘' τ' ]Ex ≡ (e [ σ' ]Ex) [ τ' ]Ex
      
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
      ∃!ε' : Sub _ _ ∣ ε' ≡[ ∃!ε ] σ'

      -- Context extension of terms
      _▷[_]_ : (Γ : Con) → Mode → Ty Γ → Con
      p : Subz (Γ ▷[ i ] A) Γ
      q : Tmz (Γ ▷[ i ] A) (A [ p ])
      _,[_]_ : (σ : Subz Γ Δ) → (i : Mode) → Tmz Γ (A [ σ ]) → Subz Γ (Δ ▷[ i ] A)
      ,∘ : (σ ,[ i ] t) ∘ τ ≡ ((σ ∘ τ) ,[ i ] subst (Tmz _) (sym [∘]) (t [ τ ]Tmz))
      p,q : p {Γ} {i} {A} ,[ i ] q ≡ id
      p∘, : p ∘ (σ ,[ i ] t) ≡ σ
      q[,] : Tmz _ ∣ q [ σ ,[ i ] t ]Tmz ≡[ (trans (sym [∘]) (cong (A [_]) p∘,)) ] t

      -- Context extension of relevant terms 
      p' : Sub (Γ ▷[ i ] A) Γ p
      q' : Tm (Γ ▷[ ω ] A) (A [ p ]) q
      _,[z]'_ : (σ' : Sub Γ Δ σ) → (t : Tmz Γ (A [ σ ])) → Sub Γ (Δ ▷[ z ] A) (σ ,[ z ] t)
      _,[ω]'_ : (σ' : Sub Γ Δ σ) → Tm Γ (A [ σ ]) t → Sub Γ (Δ ▷[ ω ] A) (σ ,[ ω ] t)
      ,[z]∘' : Sub _ _ ∣ (σ' ,[z]' t) ∘' τ' ≡[ ,∘ ] (σ' ∘' τ') ,[z]' subst (Tmz _) (sym [∘]) (t [ τ ]Tmz)
      ,[ω]∘' : Sub _ _ ∣ (σ' ,[ω]' t') ∘' τ' ≡[ ,∘ ] (σ' ∘' τ') ,[ω]' dsubst₂ (Tm _) (sym [∘]) refl (t' [ τ' ]Tm)
      p',[z]q' : Sub _ _ ∣ p' {Γ} {z} {A} ,[z]' q ≡[ p,q ] id'
      p',[ω]q' : Sub _ _ ∣ p' {Γ} {ω} {A} ,[ω]' q' ≡[ p,q ] id'
      p'∘,[z] : Sub _ _ ∣ p' ∘' (σ' ,[z]' t) ≡[ p∘, ] σ'
      p'∘,[ω] : Sub _ _ ∣ p' ∘' (σ' ,[ω]' t') ≡[ p∘, ] σ'
      q'[,]' : q' [ σ' ,[ω]' t' ]Tm ≡[ dcong₂ (Tm _) (trans (sym [∘]) (cong (A [_]) p∘,)) q[,] ] t'
      
      -- Context extension of expressions
      -- _▷Λ : Con → Con
      -- pΛ : Subz (Γ ▷Λ) Γ
      -- pΛ' : Sub (Γ ▷Λ) Γ pΛ
      -- qΛ : Ex (Γ ▷Λ)
      -- _,Λ_ : (σ : Subz Γ Δ) → Ex Γ → Subz Γ (Δ ▷Λ)
      -- _,Λ'_ : (σ' : Sub Γ Δ σ) → (e : Ex Γ) → Sub Γ (Δ ▷Λ) (σ ,Λ e)
      -- ,∘Λ : (σ ,Λ e) ∘ τ ≡ (σ ∘ τ) ,Λ (e [ τ ]Ex)
      -- ,∘Λ' : Sub _ _ ∣ (σ' ,Λ' e) ∘' τ' ≡[ ,∘Λ ] (σ' ∘' τ') ,Λ' (e [ τ ]Ex)
      -- pΛ,qΛ : pΛ {Γ} ,Λ qΛ ≡ id
      -- pΛ',qΛ' : Sub _ _ ∣ pΛ' {Γ} ,Λ' qΛ ≡[ pΛ,qΛ ] id'
      -- pΛ∘,Λ : pΛ ∘ (σ ,Λ e) ≡ σ
      -- pΛ'∘,Λ' : Sub _ _ ∣ pΛ' ∘' (σ' ,Λ' e) ≡[ pΛ∘,Λ ] σ'
      -- qΛ[,] : qΛ [ σ ,Λ e ]Ex ≡ e
      
      -- Context extension of $
      _▷$ : Con → Con
      p$ : Subz (Γ ▷$) Γ
      p$' : Sub (Γ ▷$) Γ p$
      q$ : $ (Γ ▷$)
      _,$_ : (σ : Subz Γ Δ) → $ Γ → Subz Γ (Δ ▷$)
      _,$'_ : (σ' : Sub Γ Δ σ) → (μ : $ Γ) → Sub Γ (Δ ▷$) (σ ,$ μ)
      ,∘$ : (σ ,$ μ) ∘ τ ≡ (σ ∘ τ) ,$ (μ [ τ ]$)
      ,∘$' : Sub _ _ ∣ (σ' ,$' μ) ∘' τ' ≡[ ,∘$ ] (σ' ∘' τ') ,$' (μ [ τ ]$)
      p$,q$ : p$ {Γ} ,$ q$ ≡ id
      p$',q$' : Sub _ _ ∣ p$' {Γ} ,$' q$ ≡[ p$,q$ ] id'
      p$∘,$ : p$ ∘ (σ ,$ μ) ≡ σ
      p$'∘,$' : Sub _ _ ∣ p$' ∘' (σ' ,$' μ) ≡[ p$∘,$ ] σ'
      q$[,] : q$ [ σ ,$ μ ]$ ≡ μ
      
      -- Conversion between terms and expressions
      -- ∣_∣ : Tm (Γ ▷$) A t → Ex Γ
      -- ⟨_⟩[_][_] : Ex Γ → ∀ (A : Ty (Γ ▷$)) t → Tm (Γ ▷$) A t
      -- ∣⟨⟩∣ : ∣ ⟨ e ⟩[ A ][ t ] ∣ ≡ e
      -- ⟨∣∣⟩ : ⟨ ∣ t' ∣ ⟩[ A ][ t ] ≡ t'
      -- ∅ : Tmz (Γ ▷$) A
      -- ∅-sing : ∅ ≡ t
      
    -- _⁺Λ : Subz Γ Δ → Subz (Γ ▷Λ) (Δ ▷Λ)
    -- ρ ⁺Λ = (ρ ∘ pΛ) ,Λ qΛ

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
        -- lamΛ : Ex (Γ ▷Λ) → Ex Γ
        -- lamΛ[] : (lamΛ e) [ σ ]Ex ≡ lamΛ (e [ σ ⁺Λ ]Ex)

        -- appΛ : Ex Γ → Ex Γ → Ex Γ
        -- app[] : (appΛ e f) [ σ ]Ex ≡ appΛ (e [ σ ]Ex) (f [ σ ]Ex)
        
        -- zeroΛ : Ex Γ
        -- zero[] : (zeroΛ) [ σ ]Ex ≡ zeroΛ

        -- succΛ : Ex Γ → Ex Γ
        -- succ[] : (succΛ e) [ σ ]Ex ≡ succΛ (e [ σ ]Ex)
        
        -- recΛ : Ex Γ → Ex (Γ ▷Λ ▷Λ) → Ex Γ → Ex Γ
        -- rec[] : (recΛ e f g) [ σ ]Ex ≡ recΛ (e [ σ ]Ex) (f [ σ ⁺Λ ⁺Λ ]Ex) (g [ σ ]Ex)
        
        -- Terms
        Π : (j : Mode) → Ty Γ → Ty (Γ ▷[ j ] A) → Ty Γ
        Π[] : (Π j A B) [ σ ] ≡ Π j (A [ σ ]) (B [ σ ⁺ ])
        lam : Tmz (Γ ▷[ j ] A) B → Tmz Γ (Π j A B)
        lam[] : (lam t) [ σ ]Tmz ≡[ cong (Tmz _) Π[] ] lam (t [ σ ⁺ ]Tmz)
        app : Tmz Γ (Π j A B) → Tmz (Γ ▷[ j ] A) B
        lam-app : app (lam t) ≡ t
        app-lam : lam (app t) ≡ t

        lam' : Tm (Γ ▷[ j ] A) B t → Tm Γ (Π j A B) (lam t)
        app'ω : Tm Γ (Π ω A B) t → Tm Γ A u → Tm Γ (B [ < u > ]) (app t [ < u > ]Tmz)
        app'z : Tm Γ (Π z A B) t → (u : Tmz Γ A) → Tm Γ (B [ < u > ]) (app t [ < u > ]Tmz)
        
        
        -- ∣lam'∣ : ∣ lam' {j = ω} t' ∣ ≡ lamΛ (∣ t' [ {!   !} ]Tm ∣)
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