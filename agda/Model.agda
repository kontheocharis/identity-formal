module Model where

open import Data.Nat hiding (_^_)
open import Data.Fin
open import Data.List
open import Data.Unit
open import Data.Maybe
open import Data.Product hiding (∃)


data ∃ (A : Set) (P : A → Prop) : Prop where
  _,_ : (x : A) → P x → ∃ A P
  
data _AND_ (P Q : Prop) : Prop where
  _,_ : P → Q → P AND Q
  
data _＝_ {A : Set} (x : A) : A → Prop where
  refl : x ＝ x
  
sym : ∀ {A : Set} {x y : A} → x ＝ y → y ＝ x
sym refl = refl

trs : ∀ {A : Set} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
trs refl refl = refl

just-inj : ∀ {A : Set} {x y : A} → just x ＝ just y → x ＝ y
just-inj refl = refl
  
syntax ∃ A (λ x → P) = ∃[ x ∈ A ] P

_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P → Q) AND (Q → P)

record Model : Set2 where
  field
    -- Logical
    ConL : Set1
    SubL : ConL → ConL → Set
    TyL : ConL → Set1
    TmL : ∀ ΓL → TyL ΓL → Set
    
    -- Computational
    ConC : Set
    ∙C : ConC
    SubC : ConC → ConC → Set
    TmC : ConC → Set
    _[p*] : ∀ {ΓC} → TmC ∙C → TmC ΓC
    
    -- Total
    Con : ConL → ConC → Set1
    Sub : ∀ {ΓL ΔL ΓC ΔC} → Con ΓL ΓC → Con ΔL ΔC → SubL ΓL ΔL → SubC ΓC ΔC → Set
    Ty : ∀ ΓL → TyL ΓL → Set1
    Tm : ∀ {ΓL ΓC TL} → Con ΓL ΓC → Ty ΓL TL → TmL ΓL TL → TmC ΓC → Set
    
    -- Specialization types
    Spec : ∀ {ΓL TL} → Ty ΓL TL → TmC ∙C → Ty ΓL TL
    spec : ∀ {ΓL ΓC TL Γ T aL aC} → Tm {ΓL} {ΓC} {TL} Γ T aL (aC [p*]) → Tm Γ (Spec T aC) aL (aC [p*])
    unspec : ∀ {ΓL ΓC TL Γ T aL aC aC'} → Tm {ΓL} {ΓC} {TL} Γ (Spec T aC) aL aC' → Tm Γ T aL (aC [p*])
    
Defined : ∀ {X} → Maybe X → Prop
Defined {X} y = ∃[ x ∈ X ] (y ＝ just x)

record PCA : Set1 where
  field
    ∣_∣ : Set
    app : ∣_∣ → ∣_∣ → Maybe ∣_∣
    S K : ∣_∣
    
  -- @@TODO
  -- field
  --   apps-nothing : ∀ x xs → apps x (nothing ∷ xs) ＝ nothing
  --   apps-cong : ∀ x y xs → apps x xs ＝ nothing → apps x (y ∷ xs) ＝ nothing

  --   K1-def : ∀ x → Defined (apps K (just x ∷ []))
  --   K2-def : ∀ x y → Defined (apps K (just x ∷ just y ∷ []))

  --   S1-def : ∀ x → Defined (apps S (just x ∷ []))
  --   S2-def : ∀ x y → Defined (apps S (just x ∷ just y ∷ []))
  --   S3-def : ∀ x y → Defined (apps S (just x ∷ just y ∷ just z ∷ [])) ⇔ Defined (app x y) (app x z)

  --   K-id : ∀ x y → apps K (x ∷ y ∷ []) ＝ just x

variable
  A : PCA
  m n k : ℕ
  
module PCAWithVars where
  open PCA public

  ∣_∣? : PCA → Set
  ∣ A ∣? = Maybe (∣ A ∣)
      
  data ∣_[_]∣ (A : PCA) : ℕ → Set where
    var : Fin n → ∣ A [ n ]∣
    lit : ∣ A ∣ → ∣ A [ n ]∣
    app-suc : ∣ A [ suc n ]∣ → ∣ A [ suc n ]∣ → ∣ A [ suc n ]∣
    
  eval : ∣ A [ n ]∣ → (Fin n → ∣ A ∣?) → ∣ A ∣?
  eval (var x) σ = σ x
  eval (lit x) σ = just x
  eval {A = A} (app-suc a b) σ with eval a σ | eval b σ
  ... | just f | just x = app A f x
  ... | _ | _ = nothing
  
  ∣_[_]∣^_ : (A : PCA) → ℕ → ℕ → Set
  ∣ A [ k ]∣^ l = Fin l → ∣ A [ k ]∣

  ∣_∣^_ : (A : PCA) → ℕ → Set
  ∣ A ∣^ l = Fin l → ∣ A ∣
  
  wk : (n : ℕ) → ∣ A [ n ]∣ → ∣ A [ suc n ]∣
  wk n (var x) = var (suc x)
  wk n (lit x) = lit x
  wk n (app-suc a b) = app-suc (wk n a) (wk n b)
  
  extract : ∣ A [ zero ]∣ → ∣ A ∣
  extract (lit x) = x

  opn : (n : ℕ) → ∣ A [ zero ]∣ → ∣ A [ n ]∣
  opn zero x = x
  opn (suc n) x = wk n (opn n x)

module PCACombinators (A : PCA) where
  open PCAWithVars
  
  -- @@TODO
  I : ∣ A ∣

  pair : ∣ A ∣ → ∣ A ∣ → ∣ A ∣
  lam : ∣ A [ 1 ]∣ → ∣ A ∣
  ΣA : (∣ A ∣^ n) → ∣ A ∣
  ΠA : (∣ A [ n ]∣) → ∣ A ∣
  
  ΠA-opn : ∀ {n a k} → app A (ΠA (opn n a)) k ＝ just (extract a)
  
  ΠΣA : (∣ A [ m ]∣^ n) → ∣ A ∣

module Realizability (A : PCA) where
  open PCA public
  open PCAWithVars public
  open PCACombinators A public

  RRel : Set → Set1
  RRel X = ∣ A ∣ → X → Prop
  
  _⊩[_]_ : ∀ {X} (a : ∣ A ∣?) (R : RRel X) (x : X) → Prop
  a ⊩[ R ] x = ∃[ a' ∈ (∣ A ∣)] ((a ＝ just a') AND (R a' x))
  
  Total : ∀ {X} → RRel X → Prop
  Total {X} R = (x : X) → ∃[ a ∈ ∣ A ∣ ] (R a x)
  
  _-Cart_ : ∀ {X} → (n : ℕ) → RRel X → Prop
  _-Cart_ {X} n R = (x : X) → (a : ∣ A ∣) → R a x → (∃[ k ∈ ( ∣ A ∣^ n )] (a ＝ ΣA k))
  
  TrackedAt : ∀ {X : Set} {Y : X → Set} (fR : ∣ A ∣) (x : X) (y : Y x)
    (RX : RRel X) (RY : (x : X) → RRel (Y x)) → Prop
  TrackedAt {X} {Y} fR x y RX RY = (a : ∣ A ∣) → RX a x → (app A fR a) ⊩[ RY x ] y
  
  Tracked : ∀ {X : Set} {Y : X → Set} (f : (x : X) → Y x) (fR : ∣ A ∣) (RX : RRel X) (RY : (x : X) → RRel (Y x)) → Prop
  Tracked {X} {Y} f fR RX RY = (x : X) → TrackedAt fR x (f x) RX RY

module RealizabilityModel (A : PCA) where

  open Realizability A

  record Conᴿ (ΓLᴿ : Set) (ΓCᴿ : ℕ) : Set1 where
    field
      ∣_∣ : ΓLᴿ → Set
      _ᴿᴿ : RRel (Σ[ γ ∈ ΓLᴿ ] ∣_∣ γ)
      cart : ΓCᴿ -Cart _ᴿᴿ
      
  open Conᴿ

  record Subᴿ {ΓLᴿ ΓCᴿ ΔLᴿ ΔCᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Δᴿ : Conᴿ ΔLᴿ ΔCᴿ)
    (σLᴿ : ΓLᴿ → ΔLᴿ)
    (σCᴿ : ∣ A [ ΓCᴿ ]∣^ ΔCᴿ) : Set where
    field
      ∣_∣ : ∀ γ → ∣ Γᴿ ∣ γ → ∣ Δᴿ ∣ (σLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (σLᴿ γ , ∣_∣ γ γ')) (ΠΣA σCᴿ) (Γᴿ ᴿᴿ) (λ _ → Δᴿ ᴿᴿ)

  open Subᴿ

  record Tyᴿ (ΓLᴿ : Set) (TLᴿ : ΓLᴿ → Set) : Set1 where
    field
      ∣_∣ : ∀ γ {ΓCᴿ} {Γᴿ : Conᴿ ΓLᴿ ΓCᴿ} (γ' : ∣ Γᴿ ∣ γ) → TLᴿ γ → Set
      _ᴿᴿ : ∀ γ {ΓCᴿ} {Γᴿ} γ' → RRel (Σ[ t ∈ TLᴿ γ ] ∣_∣ γ {ΓCᴿ} {Γᴿ} γ' t)
      total : ∀ γ {ΓCᴿ} {Γᴿ} γ' → Total (_ᴿᴿ γ {ΓCᴿ} {Γᴿ} γ')

  open Tyᴿ

  record Tmᴿ {ΓLᴿ ΓCᴿ TLᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Tᴿ : Tyᴿ ΓLᴿ TLᴿ)
    (aLᴿ : (γ : ΓLᴿ) → TLᴿ γ)
    (aCᴿ : ∣ A [ ΓCᴿ ]∣) : Set where
    field
      ∣_∣ : ∀ γ (γ' : ∣ Γᴿ ∣ γ) → ∣ Tᴿ ∣ γ {ΓCᴿ} {Γᴿ} γ' (aLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (aLᴿ γ , ∣_∣ γ γ')) (ΠA aCᴿ) (Γᴿ ᴿᴿ) (λ (γ , γ') → (Tᴿ ᴿᴿ) γ {ΓCᴿ} {Γᴿ} γ')


  open Tmᴿ

  R : Model

  R .Model.ConL = Set
  R .Model.ConC = ℕ
  R .Model.Con ΓLᴿ ΓCᴿ = Conᴿ ΓLᴿ ΓCᴿ

  R .Model.∙C = zero

  R .Model.SubL ΓLᴿ ΔLᴿ = ΓLᴿ → ΔLᴿ
  R .Model.SubC ΓCᴿ ΔCᴿ = ∣ A [ ΓCᴿ ]∣^ ΔCᴿ
  R .Model.Sub Γᴿ Δᴿ σLᴿ σCᴿ = Subᴿ Γᴿ Δᴿ σLᴿ σCᴿ

  R .Model.TyL ΓLᴿ = ΓLᴿ → Set
  R .Model.TmL ΓLᴿ TLᴿ = (γ : ΓLᴿ) → TLᴿ γ

  R .Model.TmC ΓCᴿ = ∣ A [ ΓCᴿ ]∣

  (R Model.[p*]) {ΓC = n} t = opn n t

  R .Model.Ty ΓLᴿ TLᴿ = Tyᴿ ΓLᴿ TLᴿ
  R .Model.Tm Γᴿ Tᴿ aLᴿ aCᴿ = Tmᴿ Γᴿ Tᴿ aLᴿ aCᴿ

  ∣ R .Model.Spec T c ∣ γ {ΓCᴿ = ΓCᴿ} {Γᴿ = Γᴿ} γ' t
    = Σ[ t' ∈ (∣ T ∣ γ {Γᴿ = Γᴿ} γ' t) ]
      (TrackedAt (ΠA (opn ΓCᴿ c)) (γ , γ') (t , t') (Γᴿ ᴿᴿ) (λ (γ , γ') → (T ᴿᴿ) γ {Γᴿ = Γᴿ} γ'))
  (R .Model.Spec T c ᴿᴿ) γ {ΓCᴿ = ΓCᴿ} γ' a (t , t' , p) = a ＝ extract c
  R .Model.Spec T c .total γ {ΓCᴿ = ΓCᴿ} γ' (t , t' , p) = extract c , refl

  ∣ R .Model.spec t ∣ γ γ' = ∣ t ∣ γ γ' , (t ᵀᴿ) (γ , γ')
  (R .Model.spec {ΓC = ΓC} {aC = aC} t ᵀᴿ) (γ , γ') a p with (t ᵀᴿ) (γ , γ') a p
  ... | (a' , p' , tTR) = a' , p' , just-inj (trs (sym p') ΠA-opn)

  ∣ R .Model.unspec t ∣ γ γ' = proj₁ (∣ t ∣ γ γ')
  (R .Model.unspec t ᵀᴿ) (γ , γ') a p = proj₂ (∣ t ∣ γ γ') a p