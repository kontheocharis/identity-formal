module Models.Realizability where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc) renaming (zero to f0)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; [_]; []; _∷_; lookup; map; tabulate)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst; sym; cong₂)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Agda.Primitive

open import Model
open import Realizability
open import Utils

module _ {ℓ'} (A : PCA) where
  open Realizability.Relations A public
  open OpTT
  open OpTT-sorts
  open OpTT-subs
  open OpTT-str
  
  -- The gluing category is
  -- id {Set} ↓ Γ {Psh A}
  
  -- Yoneda embeddings
  Psh : Set → Set1
  Psh X = X → Set
  
  isContr : Set ℓ → Set ℓ
  isContr X = Σ[ x ∈ X ] (∀ y → y ≡ x)

  yCon : ℕ → Psh ℕ
  yCon n = λ m → ∣ A [ m ]∣^ n
  
  _⇒_ : Psh ℕ → Psh ℕ → Psh ℕ
  (Γ ⇒ Δ) m = Γ m → Δ m
  
  ∀[_] : Psh ℕ → Set
  ∀[ Γ ] = ∀ {m} → Γ m
  
  Γ[_] : Psh ℕ → Set
  Γ[ Γ ] = Γ 0

  ySub : ∀ {n k} → ∣ A [ n ]∣^ k → ∀[ yCon n ⇒ yCon k ]
  ySub {n} {k} ρ σ = compose ρ σ
  
  ySub-inv : ∀ {n k} → ∀[ yCon n ⇒ yCon k ] → ∣ A [ n ]∣^ k
  ySub-inv {n} {k} f = f identity

  oTm : ℕ → Set
  oTm m = ∣ A [ m ]∣ ^ 1

  yTm : ∀ {n} (ρ : ∣ A [ n ]∣^ 1) → ∀[ yCon n ⇒ oTm ]
  yTm {n} ρ {m} σ = compose ρ σ

  yTm-inv : ∀ {n} → ∀[ yCon n ⇒ oTm ] → ∣ A [ n ]∣^ 1
  yTm-inv {n} f = f identity
  
  is-psh : Psh ℕ → Set
  is-psh Γ = ∀ {n m} (a : ∣ A [ n ]∣^ m) (γ : Γ m) → Γ n
  
  is-natural : ∀ {Γ Δ : Psh ℕ} → is-psh Γ → is-psh Δ → (σ : ∀[ Γ ⇒ Δ ]) → Set
  is-natural {Γ} {Δ} Γ-act Δ-act σ
    = ∀ {n m} (a : ∣ A [ n ]∣^ m) (γ : Γ m) →
      σ (Γ-act a γ) ≡ Δ-act a (σ γ)
        
  oTm-is-psh : is-psh oTm
  oTm-is-psh {n} {m} a x = compose x a
  
  record Conᴿ : Set (lsuc (lsuc ℓ')) where
    field
      syn : Psh ℕ
      syn-act : is-psh syn
      sem : Γ[ syn ] → Set ℓ'
      
  open Conᴿ
  
  -- Conᴿ-eq : {Γ Δ : Conᴿ} → (p : Γ .syn ≡ Δ .syn) → 
  --           (∀ γ → Γ .sem γ ≡ Δ .sem (subst (∣ A [ 0 ]∣^_) p γ)) → Γ ≡ Δ
  -- Conᴿ-eq refl h = cong (λ sem → record { syn = _; sem = sem }) (funext h)
      
  record Subᴿ (Γ Δ : Conᴿ) : Set (lsuc ℓ') where
    field
      syn : ∀[ Γ .syn ⇒ Δ .syn ]
      syn-natural : is-natural (Γ .syn-act) (Δ .syn-act) syn
      sem : ∀ γ → Γ .sem γ → Δ .sem (syn γ)

  open Subᴿ
  
  -- Subᴿ-eq : {Γ Δ : Conᴿ} {σ τ : Subᴿ Γ Δ} → (p : σ .syn ≡ τ .syn) →
  --           (∀ γ γ' → (λ v → Δ .sem (compose v γ)) ∣ σ .sem γ γ' ≡[ p ] τ .sem γ γ') → σ ≡ τ
  -- Subᴿ-eq refl h = cong (λ sem → record { syn = _; sem = sem }) (funext (λ γ → funext (h γ)))

  record Tyᴿ (Γ : Conᴿ) : Set (lsuc (lsuc ℓ')) where
    field
      sem : ∀ γ (γ' : Γ .sem γ) → Γ[ oTm ] → Set ℓ'
      
  open Tyᴿ
  
  -- Tyᴿ-eq : {Γ : Conᴿ} {T U : Tyᴿ Γ} →
  --          (∀ γ γ' a → T .sem γ γ' a ≡ U .sem γ γ' a) → T ≡ U
  -- Tyᴿ-eq h = cong (λ sem → record { sem = sem }) (funext (λ γ → funext (λ γ' → funext (h γ γ'))))

  record Tmzᴿ (Γ : Conᴿ) (T : Tyᴿ Γ) : Set (lsuc ℓ') where
    field
      sem : ∀ γ (γ' : Γ .sem γ) → T .sem γ γ' ([ ⌜ I ⌝ ])

  open Tmzᴿ
  
  -- Tmzᴿ-eq : {Γ : Conᴿ} {T : Tyᴿ Γ} {t u : Tmzᴿ Γ T} →
  --           (∀ γ γ' → t .sem γ γ' ≡ u .sem γ γ') → t ≡ u
  -- Tmzᴿ-eq h = cong (λ sem → record { sem = sem }) (funext (λ γ → funext (h γ)))

  record Tmᴿ (Γ : Conᴿ) (T : Tyᴿ Γ) (t : Tmzᴿ Γ T) : Set (lsuc ℓ') where
    field
      syn : ∀[ Γ .syn ⇒ oTm ]
      syn-natural : is-natural (Γ .syn-act) oTm-is-psh syn
      sem' : ∀ γ (γ' : Γ .sem γ) → T .sem γ γ' (syn γ)

      -- syn : ∣ A [ Γ .syn ]∣^ 1
      -- sem' : ∀ γ γ' → T .sem γ γ' (compose syn γ)
      -- proj : ∀ γ γ' → (T .sem) γ γ' (compose syn γ) → (T .sem) γ γ' ([ ⌜ I ⌝ ])
      
  open Tmᴿ
  
  -- Tmᴿ-eq : {Γ : Conᴿ} {T : Tyᴿ Γ} {t : Tmzᴿ Γ T} {a b : Tmᴿ Γ T t} →
  --          a .syn ≡ b .syn →
  --          (∀ γ γ' → a .sem' γ γ' ≡ b .sem' γ γ') →
  --          (∀ γ γ' x → a .proj γ γ' x ≡ b .proj γ γ' x) → a ≡ b
  -- Tmᴿ-eq refl h₁ h₂ = cong₂ (λ sem' proj → record { syn = _; sem' = sem'; proj = proj })
  --                             (funext (λ γ → funext (h₁ γ)))
  --                             (funext (λ γ → funext (λ γ' → funext (h₂ γ γ'))))
      
  record Exᴿ (Γ : Conᴿ) : Set (lsuc ℓ') where
    field
      syn : ∀[ Γ .syn ⇒ oTm ]
      syn-natural : is-natural (Γ .syn-act) oTm-is-psh syn
      
  open Exᴿ

  record $∈ᴿ_ (Γ : Conᴿ) : Set (lsuc ℓ') where
    field
      iso : (γ : Γ[ Γ .syn ]) → isContr (Γ .sem γ)

  open $∈ᴿ_
  
  -- Exᴿ-eq : {Γ : Conᴿ} {e f : Exᴿ Γ} → e .syn ≡ f .syn → e ≡ f
  -- Exᴿ-eq refl = refl
  
  M-sorts : OpTT-sorts {lsuc (lsuc ℓ')} {lsuc ℓ'}
  M-sorts .Con = Conᴿ
  M-sorts .Sub = Subᴿ
  M-sorts .Ty = Tyᴿ
  M-sorts .Tmz = Tmzᴿ
  M-sorts .Tm = Tmᴿ
  M-sorts .Ex = Exᴿ
  M-sorts .$∈_ = $∈ᴿ_

  M-subs : OpTT-subs M-sorts 
  M-subs .id .syn x = x
  M-subs .id .syn-natural a γ = refl
  M-subs .id .sem γ x = x
  (M-subs ∘ σ) τ .syn x₂ = σ .syn (τ .syn x₂)
  (M-subs ∘ σ) τ .syn-natural a γ = {!   !}
  (M-subs ∘ σ) τ .sem γ z₁ = σ .sem (τ .syn γ) (τ .sem γ z₁)
  -- M-subs .assoc = {!   !}
  -- M-subs .∘id = {!   !}
  -- M-subs .id∘ = {!   !}
  (M-subs [ x ]) x₁ .sem γ' z₁ z₂ = x .sem (x₁ .syn γ') (x₁ .sem γ' z₁) z₂
  -- M-subs .[id] = {!   !}
  -- M-subs .[∘] = {!   !}
  (M-subs [ x ]Tmz) σ .sem γ γ' = x .sem (σ .syn γ) (σ .sem γ γ')
  -- M-subs .[id]Tmz = {!   !}
  -- M-subs .[∘]Tmz = {!   !}
  (M-subs [ x ]Tm) σ .syn x₁ = x .syn (σ .syn x₁)
  (M-subs [ x ]Tm) σ .syn-natural a γ = {!   !}
  (M-subs [ x ]Tm) σ .sem' γ γ' = x .sem' (σ .syn γ) (σ .sem γ γ')
  -- M-subs .[id]Tm = {!   !}
  -- M-subs .[∘]Tm = {!   !}
  (M-subs [ x ]Ex) x₁ .syn z₁ = x .syn (x₁ .syn z₁)
  (M-subs [ x ]Ex) x₁ .syn-natural = {!   !}
  -- M-subs .[id]Ex = {!   !}
  -- M-subs .[∘]Ex = {!   !}
  (M-subs [ record { iso = iso₁ } ]$) x₁ .iso γ
    = let a , b = iso₁ (x₁ .syn γ) in {!  x₁ .sem γ !} , {!   !}
  -- M-subs .[id]$ = {!   !}
  -- M-subs .[∘]$ = {!   !}
  -- M-subs .$-prop = {!   !}
  M-subs .∙ .syn = yCon 0
  M-subs .∙ .syn-act _ _ = []
  M-subs .∙ .sem [] = ⊤
  M-subs .ε .syn x = []
  M-subs .ε .syn-natural a γ = refl
  M-subs .ε .sem γ x = tt
  M-subs .∃!ε = {!   !}
  (M-subs ▷[ Γ ] j) A .syn = {!   !}
  (M-subs ▷[ Γ ] j) A .syn-act = {!   !}
  (M-subs ▷[ Γ ] j) A .sem = {!   !}
  -- M-subs .p = {!   !}
  -- M-subs .q = {!   !}
  -- M-subs .q' = {!   !}
  -- M-subs ._,[z]_ = {!   !}
  -- M-subs ._,[ω]_ = {!   !}
  -- M-subs .,[z]∘ = {!   !}
  -- M-subs .p,[z]q = {!   !}
  -- M-subs .p,[ω]q = {!   !}
  -- M-subs .p∘,[z] = {!   !}
  -- M-subs .p∘,[ω] = {!   !}
  -- M-subs .q[,[z]] = {!   !}
  -- M-subs .q[,[ω]] = {!   !}
  -- M-subs .q'[,[ω]] = {!   !}
  -- M-subs ▷Λ = {!   !}
  -- M-subs .pΛ = {!   !}
  -- M-subs .qΛ = {!   !}
  -- M-subs ._,Λ_ = {!   !}
  -- M-subs .,∘Λ = {!   !}
  -- M-subs .pΛ,qΛ = {!   !}
  -- M-subs .pΛ∘,Λ = {!   !}
  -- M-subs .qΛ[,] = {!   !}
  -- M-subs ▷$ = {!   !}
  -- M-subs .p$ = {!   !}
  -- M-subs .q$ = {!   !}
  -- M-subs ._,$_ = {!   !}
  -- M-subs .,∘$ = {!   !}
  -- M-subs .p$,q$ = {!   !}
  -- M-subs .p$∘,$ = {!   !}
  -- M-subs .q$[,] = {!   !}
  -- ∣ M-subs ∣ = {!   !}
  -- M-subs .∅ = {!   !}
  -- M-subs .∅-sing = {!   !}
  -- M-subs .⟨_⟩[_] = {!   !}
  -- M-subs .∣⟨⟩∣ = {!   !}
  -- M-subs .⟨∣∣⟩ = {!   !}
  
  
  -- M-subs .id .syn = identity
  -- M-subs .id {Γ} .sem γ x = coe (cong (Γ .sem) (sym (id-compose _))) x
  -- (M-subs ∘ σ) σ' .syn = compose (σ .syn) (σ' .syn)
  -- _∘_ M-subs {Θ = Θ} σ σ' .sem γ γ'
  --   = coe (cong (Θ .sem) (sym (compose-assoc (σ .syn) (σ' .syn) γ))) (σ .sem _ (σ' .sem γ γ')) 
  -- M-subs .assoc {ρ = ρ} {σ = σ} {τ = τ}
  --   = Subᴿ-eq (sym (compose-assoc (ρ .syn) (σ .syn) (τ .syn)))
  --     (λ γ γ' → {!  refl !})
  -- M-subs .∘id = {!   !}
  -- M-subs .id∘ = {!   !}
  -- (M-subs [ T ]) σ .sem γ γ' a = T .sem (compose (σ .syn) γ) (σ .sem γ γ') a
  -- M-subs .[id] = Tyᴿ-eq λ γ γ' a → {! ? !}
  -- -- M-subs .[∘] = {!   !}
  -- (M-subs [ x ]Tmz) σ .sem γ γ' = x .sem (compose (σ .syn) γ) (σ .sem γ γ')
  -- -- M-subs .[id]Tmz = {!   !}
  -- -- M-subs .[∘]Tmz = {!   !}
  -- (M-subs [ x ]Tm) σ .syn = compose (x .syn) (σ .syn)
  -- (M-subs [ x ]Tm) σ .sem' γ γ' = subst (λ q → _ .sem _ _ q) ({!  syn (compose-assoc ? ?) !}) (x .sem' (compose (σ .syn) γ) (σ .sem γ γ'))
  -- (M-subs [ x ]Tm) σ .proj = {!   !}
  -- M-subs .[id]Tm = {!   !}
  -- M-subs .[∘]Tm = {!   !}
  -- M-subs ._[_]Ex = {!   !}
  -- M-subs .[id]Ex = {!   !}
  -- M-subs .[∘]Ex = {!   !}
  -- M-subs ._[_]$ = {!   !}
  -- M-subs .[id]$ = {!   !}
  -- M-subs .[∘]$ = {!   !}
  -- M-subs .$-prop = {!   !}
  -- M-subs .∙ .syn = 0
  -- M-subs .∙ .sem [] = ⊤
  -- M-subs .ε .syn = []
  -- M-subs .ε .sem γ γ' = tt
  -- M-subs .∃!ε = {!   !}
  -- M-subs ._▷[_]_ = {!   !}
  -- M-subs .p = {!   !}
  -- M-subs .q = {!   !}
  -- M-subs .q' = {!   !}
  -- M-subs ._,[z]_ = {!   !}
  -- M-subs ._,[ω]_ = {!   !}
  -- M-subs .,[z]∘ = {!   !}
  -- M-subs .p,[z]q = {!   !}
  -- M-subs .p,[ω]q = {!   !}
  -- M-subs .p∘,[z] = {!   !}
  -- M-subs .p∘,[ω] = {!   !}
  -- M-subs .q[,[z]] = {!   !}
  -- M-subs .q[,[ω]] = {!   !}
  -- M-subs .q'[,[ω]] = {!   !}
  -- M-subs ▷Λ = {!   !}
  -- M-subs .pΛ = {!   !}
  -- M-subs .qΛ = {!   !}
  -- M-subs ._,Λ_ = {!   !}
  -- M-subs .,∘Λ = {!   !}
  -- M-subs .pΛ,qΛ = {!   !}
  -- M-subs .pΛ∘,Λ = {!   !}
  -- M-subs .qΛ[,] = {!   !}
  -- M-subs ▷$ = {!   !}
  -- M-subs .p$ = {!   !}
  -- M-subs .q$ = {!   !}
  -- M-subs ._,$_ = {!   !}
  -- M-subs .,∘$ = {!   !}
  -- M-subs .p$,q$ = {!   !}
  -- M-subs .p$∘,$ = {!   !}
  -- M-subs .q$[,] = {!   !}
  -- ∣ M-subs ∣ = {!   !}
  -- M-subs .∅ = {!   !}
  -- M-subs .∅-sing = {!   !}
  -- M-subs .⟨_⟩[_] = {!   !}
  -- M-subs .∣⟨⟩∣ = {!   !}
  -- M-subs .⟨∣∣⟩ = {!   !}

  -- M : OpTT {lsuc (lsuc ℓ')} {lsuc ℓ'}
  -- M .sorts = M-sorts
  -- M .subs = {!   !}
  -- M .str = {!   !}