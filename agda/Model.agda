module Model where

open import Data.Nat hiding (_^_)
open import Data.Fin
open import Data.Vec
open import Data.Unit
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂)

{-# BUILTIN REWRITE _≡_ #-}
  
_AND_ : (P Q : Set) → Set
_AND_ = _×_
  
_＝_ : ∀ {A : Set} (x : A) → A → Set
_＝_ = _≡_
  
just-inj : ∀ {A : Set} {x y : A} → just x ＝ just y → x ＝ y
just-inj refl = refl

_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) AND (Q → P)

record Model : Set2 where
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
    βL : ∀ {ΓL TL UL} t → apL {ΓL} {TL} {UL} (lamL t) ＝ t
    ηL : ∀ {ΓL TL UL} t → lamL {ΓL} {TL} {UL} (apL t) ＝ t
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
    
record TCA : Set1 where
  field
    ∣_∣ : Set
    app : ∣_∣ → ∣_∣ → ∣_∣
    S K : ∣_∣
    K-id : ∀ x y → app (app K x) y ＝ x
    S-id : ∀ x y z → app (app (app S x) y) z ＝ app (app x z) (app y z)

variable
  A : TCA
  m n : ℕ
  
module TCAWithVars where
  open TCA public
      
  data ∣_[_]∣ (A : TCA) : ℕ → Set where
    v : Fin n → ∣ A [ n ]∣
    ⌜_⌝ : ∣ A ∣ → ∣ A [ n ]∣
    _∙'_ : ∣ A [ n ]∣ → ∣ A [ n ]∣ → ∣ A [ n ]∣
  
  ∣_[_]∣^_ : (A : TCA) → ℕ → ℕ → Set
  ∣ A [ k ]∣^ l = Vec ∣ A [ k ]∣ l

  ∣_∣^_ : (A : TCA) → ℕ → Set
  ∣ A ∣^ l = Vec ∣ A ∣ l
  
module TCACombinators (A : TCA) where
  open TCAWithVars
  
  s : ∣ A ∣
  s = S A

  k : ∣ A ∣
  k = K A
  
  _∙_ : ∣ A ∣ → ∣ A ∣ → ∣ A ∣
  x ∙ y = app A x y
    
  eval : ∣ A [ n ]∣ → ∣ A ∣^ n → ∣ A ∣
  eval (v x) σ = lookup σ x
  eval (⌜ x ⌝) σ = x
  eval (a ∙' b) σ = (eval a σ) ∙ (eval b σ)
  
  wk : {n : ℕ} → ∣ A [ n ]∣ → ∣ A [ suc n ]∣
  wk (v x) = v (suc x)
  wk (⌜ x ⌝) = ⌜ x ⌝
  wk (a ∙' b) = (wk a) ∙' (wk b)
  
  extract : ∣ A [ zero ]∣ → ∣ A ∣
  extract m = eval m []

  opn : ∣ A [ zero ]∣ → ∣ A [ n ]∣
  opn ⌜ x ⌝ = ⌜ x ⌝
  opn (y ∙' y₁) = opn y ∙' opn y₁
  
  eval-opn : ∀ {n σ} x → eval {n} (opn x) σ ＝ eval x []
  eval-opn ⌜ x ⌝ = refl
  eval-opn (x ∙' x₁) = cong₂ _∙_ (eval-opn x) (eval-opn x₁)
  
  _∙*_ : ∀ {n} → ∣ A [ n ]∣^ m → ∣ A ∣^ n → ∣ A ∣^ m
  _∙*_ {zero} xs ys = []
  _∙*_ {suc n} (x ∷ xs) ys = eval x ys ∷ (xs ∙* ys)
  
  i : ∣ A ∣
  i = (s ∙ k) ∙ k

  Λ' : ∣ A [ suc n ]∣ → ∣ A [ n ]∣
  Λ' (v zero) = ⌜ i ⌝
  Λ' (v (suc x)) = ⌜ k ⌝ ∙' v x
  Λ' ⌜ x ⌝ = ⌜ k ∙ x ⌝
  Λ' (t ∙' t') = (⌜ s ⌝ ∙' Λ' t) ∙' Λ' t'

  pair' : ∣ A [ n ]∣ → ∣ A [ n ]∣ → ∣ A [ n ]∣
  pair' x y = Λ' ((v zero ∙' wk x) ∙' wk y)

  pair : ∣ A ∣ → ∣ A ∣ → ∣ A ∣
  pair a b = extract (pair' ⌜ a ⌝ ⌜ b ⌝)

  Λ* : (∣ A [ n ]∣) → ∣ A ∣
  Λ* {n = zero} x = extract x
  Λ* {n = suc n} x = Λ* (Λ' x)

  pair* : ∣ A ∣^ n → ∣ A ∣
  pair* {zero} k = i
  pair* {suc n} (k ∷ ks) = pair k (pair* {n} ks)

  pair*-Λ* : (∣ A [ m ]∣^ n) → ∣ A ∣
  pair*-Λ* k = pair* (Data.Vec.map Λ* k)

module Realizability (A : TCA) where
  open TCA public
  open TCAWithVars public
  open TCACombinators A public

  RRel : (n : ℕ) → Set → Set1
  RRel n X = ∣ A ∣^ n → X → Set
  
  _⊩[_]_ : ∀ {X n} (a : ∣ A ∣^ n) (R : RRel n X) (x : X) → Set
  a ⊩[ R ] x = R a x
  
  transp-⊩ : ∀ {n X} {R : RRel n X} {a a' x} → (a ⊩[ R ] x) → (a ＝ a') → (a' ⊩[ R ] x)
  transp-⊩ t refl = t
  
  Total : ∀ {X n} → RRel n X → Set
  Total {X} {n} R = (x : X) → ∃[ a ] (R a x)
  
  TrackedAt : ∀ {X : Set} {Y : X → Set} {n} {m} (fR : ∣ A [ n ]∣^ m) (x : X) (y : Y x)
    (RX : RRel n X) (RY : (x : X) → RRel m (Y x)) → Set
  TrackedAt {X} {Y} {n} fR x y RX RY = (a : ∣ A ∣^ n) → a ⊩[ RX ] x → (fR ∙* a) ⊩[ RY x ] y
  
  Tracked : ∀ {X : Set} {Y : X → Set} {n m} (f : (x : X) → Y x)
      (fR : ∣ A [ n ]∣^ m) (RX : RRel n X) (RY : (x : X) → RRel m (Y x)) → Set
  Tracked {X} {Y} {n} {m} f fR RX RY = (x : X) → TrackedAt fR x (f x) RX RY
  
  ∃Tracked : ∀ {X : Set} {Y : X → Set} {n m} (f : (x : X) → Y x) (RX : RRel n X) (RY : (x : X) → RRel m (Y x)) → Set
  ∃Tracked {X} {Y} {n} {m} f RX RY = ∃[ fR ] Tracked f fR RX RY

module RealizabilityModel (A : TCA) where

  open Realizability A

  record Conᴿ (ΓLᴿ : Set) (ΓCᴿ : ℕ) : Set1 where
    field
      ∣_∣ : ΓLᴿ → Set
      _ᴿᴿ : RRel ΓCᴿ (Σ[ γ ∈ ΓLᴿ ] ∣_∣ γ)
      total : Total _ᴿᴿ
      -- cart : ΓCᴿ -Cart _ᴿᴿ
      
  open Conᴿ

  record Subᴿ {ΓLᴿ ΓCᴿ ΔLᴿ ΔCᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Δᴿ : Conᴿ ΔLᴿ ΔCᴿ)
    (σLᴿ : ΓLᴿ → ΔLᴿ)
    (σCᴿ : ∣ A [ ΓCᴿ ]∣^ ΔCᴿ) : Set where
    field
      ∣_∣ : ∀ γ → ∣ Γᴿ ∣ γ → ∣ Δᴿ ∣ (σLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (σLᴿ γ , ∣_∣ γ γ')) σCᴿ (Γᴿ ᴿᴿ) (λ _ → Δᴿ ᴿᴿ)

  open Subᴿ

  record Tyᴿ (ΓLᴿ : Set) (TLᴿ : ΓLᴿ → Set) : Set1 where
    field
      ∣_∣ : ∀ γ → TLᴿ γ → Set
      _ᴿᴿ : ∀ γ → RRel 1 (Σ[ t ∈ TLᴿ γ ] ∣_∣ γ t)
      total : ∀ γ  → Total (_ᴿᴿ γ)

  open Tyᴿ

  record Tmᴿ {ΓLᴿ ΓCᴿ TLᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Tᴿ : Tyᴿ ΓLᴿ TLᴿ)
    (aLᴿ : (γ : ΓLᴿ) → TLᴿ γ)
    (aCᴿ : ∣ A [ ΓCᴿ ]∣) : Set where
    field
      ∣_∣ : ∀ γ (γ' : ∣ Γᴿ ∣ γ) → ∣ Tᴿ ∣ γ (aLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (aLᴿ γ , ∣_∣ γ γ')) [ aCᴿ ] (Γᴿ ᴿᴿ) (λ (γ , γ') → (Tᴿ ᴿᴿ) γ)


  open Tmᴿ

  R : Model

  R .Model.ConL = Set
  R .Model.ConC = ℕ
  R .Model.Con ΓLᴿ ΓCᴿ = Conᴿ ΓLᴿ ΓCᴿ

  R .Model.SubL ΓLᴿ ΔLᴿ = ΓLᴿ → ΔLᴿ
  R .Model.SubC ΓCᴿ ΔCᴿ = ∣ A [ ΓCᴿ ]∣^ ΔCᴿ
  R .Model.Sub Γᴿ Δᴿ σLᴿ σCᴿ = Subᴿ Γᴿ Δᴿ σLᴿ σCᴿ

  R .Model.TyL ΓLᴿ = ΓLᴿ → Set
  R .Model.TmL ΓLᴿ TLᴿ = (γ : ΓLᴿ) → TLᴿ γ

  R .Model.TmC ΓCᴿ = ∣ A [ ΓCᴿ ]∣

  R .Model.Ty ΓLᴿ TLᴿ = Tyᴿ ΓLᴿ TLᴿ
  R .Model.Tm Γᴿ Tᴿ aLᴿ aCᴿ = Tmᴿ Γᴿ Tᴿ aLᴿ aCᴿ
  
  R .Model.∙L = ⊤
  (R Model.▷L ΓLᴿ) TLᴿ = Σ[ γ ∈ ΓLᴿ ] TLᴿ γ
  
  R .Model.∙C = zero
  R Model.▷C = suc
  
  ∣ R .Model.∙ ∣ tt = ⊤
  (R .Model.∙ ᴿᴿ) [] (tt , tt) = ⊤
  ∣ (R Model.▷ Γᴿ) Tᴿ ∣ (γ , t) = Σ[ γ' ∈ ∣ Γᴿ ∣ γ ] ∣ Tᴿ ∣ γ t
  ((R Model.▷ Γᴿ) Tᴿ ᴿᴿ) (tR ∷ γR) ((γ , t) , γ' , t')
    = (γR ⊩[ Γᴿ ᴿᴿ ] (γ , γ')) AND ([ tR ] ⊩[ (Tᴿ ᴿᴿ) γ ] (t , t'))
  ∣ (R Model.▷0 Γᴿ) TLᴿ ∣ (γ , t) = ∣ Γᴿ ∣ γ
  ((R Model.▷0 Γᴿ) TLᴿ ᴿᴿ) a ((γ , t) , γ') = (Γᴿ ᴿᴿ) a (γ , γ')
  
  R .Model.∙ .total _ = [] , tt
  (R Model.▷ Γ) T .total ((γ , t) , (γ' , t')) with (Γ .total (γ , γ')) | (T .total γ (t , t'))
  ... | γTR , γTotal | (tTR ∷ []) , tTotal
      = tTR ∷ γTR , γTotal , tTotal
  (R Model.▷0 Γ) T .total ((γ , t) , γ') = Γ .total (γ , γ')

  (R Model.[p*]) {ΓC = n} t = opn t
  
  R .Model._[_]TL TLᴿ σLᴿ γ = TLᴿ (σLᴿ γ)
  ∣ (R Model.[ Tᴿ ]T) σLᴿ ∣ γ = ∣ Tᴿ ∣ (σLᴿ γ)
  ((R Model.[ Tᴿ ]T) σLᴿ ᴿᴿ) γ a (t , t') = a ⊩[ (Tᴿ ᴿᴿ) (σLᴿ γ) ] (t , t')
  (R Model.[ Tᴿ ]T) σLᴿ .total γ = Tᴿ .total (σLᴿ γ)

  R .Model._[_]L tLᴿ σLᴿ γ = tLᴿ (σLᴿ γ)
  R .Model.idL γ = γ
  R .Model._,L_ σLᴿ tLᴿ γ = σLᴿ γ , tLᴿ γ

  R .Model.ΠL TLᴿ ULᴿ γ = (t : TLᴿ γ) → ULᴿ (γ , t)
  R .Model.lamL t γ t₁ = t (γ , t₁)
  R .Model.apL x (γ , t) = x γ t
  R .Model.βL t = refl
  R .Model.ηL t = refl
  
  R .Model.lamC x = Λ' x
  R .Model.appC x y = x ∙' y
  
  ∣ R .Model.Π T U ∣ γ t
    = Σ[ t' ∈ (∀ x (x' : ∣ T ∣ γ x) → ∣ U ∣ (γ , x) (t x)) ]
        (∃Tracked (λ (x , x') → t x , t' x x') ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t)))
  -- (R .Model.Π T U ᴿᴿ) γ a (f , f' , (_ , p)) = Tracked (λ (x , x') → f x , f' x x') a ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t))
  -- R .Model.Π T U .total γ (f , f' , (l , p)) = l , p
  -- ∣ R .Model.lam {tC = tC} record { ∣_∣ = ∣t∣ ; _ᵀᴿ = tᵀᴿ } ∣ γ γ'
  --   = ((λ x x' → ∣t∣ (γ , x) (γ' , x')) , {!   !} )
  --     -- (∃-rec (t ᵀᴿ) (λ a' p → a' , -- ΠAⱽ tC (a' , p .fst) ,
  --     --   λ (t , t') a tTR → let m = p .snd ((γ , t) , γ' , t') in m a {!   !}))
  --     -- (∃-elim (λ ex → ∃Tracked (λ (x , x') → {!   !} x , {!   !} x x') {!   !} {!   !}) (t ᵀᴿ) (λ r s → {!   !} , λ (γ , t) a tr → {!   !}))
  -- R .Model.lam t ᵀᴿ = {!   !}
  -- ∣ R .Model.app {tL = tL} f x ∣ γ γ' = ∣ f ∣ γ γ' .proj₁ (tL γ) (∣ x ∣ γ γ')
  -- R .Model.app record { ∣_∣ = ∣f∣ ; _ᵀᴿ = fᵀᴿ } record { ∣_∣ = ∣x∣ ; _ᵀᴿ = xᵀᴿ } ᵀᴿ
  --   = {!   !}
  

  ∣ R .Model.Spec {ΓL = ΓLᴿ} T c ∣ γ t
    = Σ[ t' ∈ (∣ T ∣ γ t) ] ([ extract c ] ⊩[ (T ᴿᴿ) γ ] (t , t'))
  (R .Model.Spec T c ᴿᴿ) γ a (t , t' , p) = a ＝ [ extract c ]
  R .Model.Spec T c .total γ (t , t' , p) = [ extract c ] , refl
  ∣ R .Model.spec {ΓC = ΓC} {Γ = Γ} {T = T} {aC = aC} t ∣ γ γ'
    = ∣ t ∣ γ γ' ,
        let (γTR , γTotal) = Γ .total (γ , γ')
        in transp-⊩ {R = (T ᴿᴿ) γ} ((t ᵀᴿ) (γ , γ') γTR γTotal) (cong [_] (eval-opn aC))
  (R .Model.spec {ΓC = ΓC} {aC = aC} t ᵀᴿ) (γ , γ') a p = cong (_∷ []) (eval-opn aC)
  ∣ R .Model.unspec t ∣ γ γ' = proj₁ (∣ t ∣ γ γ')
  (R .Model.unspec {T = T} {aC = aC} t ᵀᴿ) (γ , γ') a p 
    = transp-⊩ {R = (T ᴿᴿ) γ} (proj₂ (∣ t ∣ γ γ')) (cong [_] (sym (eval-opn aC)))
  