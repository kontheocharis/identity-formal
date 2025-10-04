module Model where

open import Data.Nat hiding (_^_)
open import Data.Fin
open import Data.List
open import Data.Unit
open import Data.Maybe
open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

{-# BUILTIN REWRITE _≡_ #-}

data ∃ (A : Set) (P : A → Set) : Set where
  _,_ : (x : A) → P x → ∃ A P
  
∃-elim : ∀ {A : Set} {P : A → Set} (Q : ∃ A P → Set)
  (m : ∃ A P) → ((x : A) → (y : P x) → Q (x , y)) → Q m
∃-elim Q (x , x₁) f = f x x₁

∃-rec : ∀ {A P} {Y : Set} (m : ∃ A P) → ((x : A) → P x → Y) → Y
∃-rec (x , x₁) f = f x x₁
  
record _AND_ (P Q : Set) : Set where
  constructor _,_
  field
    fst : P
    snd : Q
    
open _AND_
  
data _＝_ {A : Set} (x : A) : A → Set where
  refl : x ＝ x
  
sym : ∀ {A : Set} {x y : A} → x ＝ y → y ＝ x
sym refl = refl

trs : ∀ {A : Set} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
trs refl refl = refl

cong2 : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B} → x ＝ x' → y ＝ y' → f x y ＝ f x' y'
cong2 f refl refl = refl

just-inj : ∀ {A : Set} {x y : A} → just x ＝ just y → x ＝ y
just-inj refl = refl
  
syntax ∃ A (λ x → P) = ∃[ x ∈ A ] P

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
    NfC : ∀ {ΓC} → TmC ΓC → Set

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
    
Defined : ∀ {X} → Maybe X → Set
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
  
¶ : {A : Prop} → A → A
  
module PCAWithVars where
  open PCA public

  ∣_∣? : PCA → Set
  ∣ A ∣? = Maybe (∣ A ∣)
      
  data ∣_[_]∣ (A : PCA) : ℕ → Set where
    var : Fin n → ∣ A [ n ]∣
    lit : ∣ A ∣ → ∣ A [ n ]∣
    app' : ∣ A [ n ]∣ → ∣ A [ n ]∣ → ∣ A [ n ]∣
    
  eval : ∣ A [ n ]∣ → (Fin n → ∣ A ∣?) → ∣ A ∣?
  eval (var x) σ = σ x
  eval (lit x) σ = just x
  eval {A = A} (app' a b) σ with eval a σ | eval b σ
  ... | just f | just x = app A f x
  ... | _ | _ = nothing
  
  ∣_[_]∣^_ : (A : PCA) → ℕ → ℕ → Set
  ∣ A [ k ]∣^ l = Fin l → ∣ A [ k ]∣

  ∣_∣^_ : (A : PCA) → ℕ → Set
  ∣ A ∣^ l = Fin l → ∣ A ∣
  
  wk : (n : ℕ) → ∣ A [ n ]∣ → ∣ A [ suc n ]∣
  wk n (var x) = var (suc x)
  wk n (lit x) = lit x
  wk n (app' a b) = app' (wk n a) (wk n b)
  
  extract : ∣ A [ zero ]∣ → ∣ A ∣?
  extract (lit x) = just x
  extract {A = A} (app' y y₁) with extract y | extract y₁
  ... | just y' | just z' = app A y' z'
  ... | _ | _ = nothing

  opn : (n : ℕ) → ∣ A [ zero ]∣ → ∣ A [ n ]∣
  opn zero x = x
  opn (suc n) x = wk n (opn n x)

module PCACombinators (A : PCA) where
  open PCAWithVars

  -- lambda' : ∣ A [ suc n ]∣ → ∣ A [ n ]∣

  opaque  
    app?- : ∣ A ∣? → ∣ A ∣ → ∣ A ∣?
    app?- nothing y = nothing
    app?- (just x) y = app A x y
  
  opaque  
    is-def : ∀ (x : ∣ A ∣?) → Defined x → ∣ A ∣
    is-def (just x) _ = x
    is-def nothing p = {!   !}
  
  -- @@TODO
  I : ∣ A ∣

  pair : ∣ A ∣ → ∣ A ∣ → ∣ A ∣
  lambda : ∣ A [ suc n ]∣ → ∣ A [ n ]∣

  ΣA : (∣ A ∣^ n) → ∣ A ∣
  ΣA {n = zero} f = I
  ΣA {n = suc n} f = pair (ΣA (λ i → f (suc i))) (f zero)

  postulate
    ΠA : (∣ A [ n ]∣) → ∣ A ∣?

  postulate
    ΠAⱽ : (x : ∣ A [ n ]∣) → Defined (ΠA x) → ∣ A ∣
  
  -- postulate
    -- ΠA-opn-defined : ∀ {n x'} → Defined (ΠA (opn n x'))
  
  postulate
    appⱽ-opn : ∀ {n a} → (x : ∣ A ∣) → (y : ∣ A ∣) → just x ＝ ΠA (opn n a) → ∣ A ∣
    appⱽ-opn-id : ∀ {n a x y p} → appⱽ-opn {n} {a} x y p ≡ x
    {-# REWRITE appⱽ-opn-id #-}

  postulate
    ΠA-opn-id : ∀ {n a k} → app?- (ΠA (opn n a)) k ＝ extract a
  
  postulate
    ΠΣA : (∣ A [ m ]∣^ n) → ∣ A ∣?

module Realizability (A : PCA) where
  open PCA public
  open PCAWithVars public
  open PCACombinators A public

  RRel : Set → Set1
  RRel X = ∣ A ∣ → X → Set
  
  _⊩[_]_ : ∀ {X} (a : ∣ A ∣) (R : RRel X) (x : X) → Set
  a ⊩[ R ] x = R a x
  
  _!⊩[_]_ : ∀ {X} (a : ∣ A ∣?) (R : RRel X) (x : X) → Set
  a !⊩[ R ] x = ∃[ a' ∈ (∣ A ∣)] ((a ＝ just a') AND (R a' x))
  
  Total : ∀ {X} → RRel X → Set
  Total {X} R = (x : X) → ∃[ a ∈ ∣ A ∣ ] (R a x)
  
  _-Cart_ : ∀ {X} → (n : ℕ) → RRel X → Set
  _-Cart_ {X} n R = (x : X) → (a : ∣ A ∣) → R a x → (∃[ k ∈ ( ∣ A ∣^ n )] (a ＝ ΣA k))
  
  TrackedAt : ∀ {X : Set} {Y : X → Set} (fR : ∣ A ∣) (x : X) (y : Y x)
    (RX : RRel X) (RY : (x : X) → RRel (Y x)) → Set
  TrackedAt {X} {Y} fR x y RX RY = (a : ∣ A ∣) → a ⊩[ RX ] x → (app A fR a) !⊩[ RY x ] y
  
  Tracked : ∀ {X : Set} {Y : X → Set} (f : (x : X) → Y x) (fR : ∣ A ∣) (RX : RRel X) (RY : (x : X) → RRel (Y x)) → Set
  Tracked {X} {Y} f fR RX RY = (x : X) → TrackedAt fR x (f x) RX RY
  
  DefTracked : ∀ {X : Set} {Y : X → Set} (f : (x : X) → Y x) (fR : ∣ A ∣?) (RX : RRel X) (RY : (x : X) → RRel (Y x)) → Set
  DefTracked {X} {Y} f fR RX RY = ∃[ fR' ∈ (∣ A ∣)] ((fR ＝ just fR') AND Tracked f fR' RX RY)
  
  ∃Tracked : ∀ {X : Set} {Y : X → Set} (f : (x : X) → Y x) (RX : RRel X) (RY : (x : X) → RRel (Y x)) → Set
  ∃Tracked {X} {Y} f RX RY = ∃[ fR ∈ (∣ A ∣)] Tracked f fR RX RY

module RealizabilityModel (A : PCA) where

  open Realizability A

  record Conᴿ (ΓLᴿ : Set) (ΓCᴿ : ℕ) : Set1 where
    field
      ∣_∣ : ΓLᴿ → Set
      _ᴿᴿ : RRel (Σ[ γ ∈ ΓLᴿ ] ∣_∣ γ)
      -- cart : ΓCᴿ -Cart _ᴿᴿ
      
  open Conᴿ

  record Subᴿ {ΓLᴿ ΓCᴿ ΔLᴿ ΔCᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Δᴿ : Conᴿ ΔLᴿ ΔCᴿ)
    (σLᴿ : ΓLᴿ → ΔLᴿ)
    (σCᴿ : ∣ A [ ΓCᴿ ]∣^ ΔCᴿ) : Set where
    field
      ∣_∣ : ∀ γ → ∣ Γᴿ ∣ γ → ∣ Δᴿ ∣ (σLᴿ γ)
      _ᵀᴿ : DefTracked (λ (γ , γ') → (σLᴿ γ , ∣_∣ γ γ')) (ΠΣA σCᴿ) (Γᴿ ᴿᴿ) (λ _ → Δᴿ ᴿᴿ)

  open Subᴿ

  record Tyᴿ (ΓLᴿ : Set) (TLᴿ : ΓLᴿ → Set) : Set1 where
    field
      ∣_∣ : ∀ γ → TLᴿ γ → Set
      _ᴿᴿ : ∀ γ → RRel (Σ[ t ∈ TLᴿ γ ] ∣_∣ γ t)
      total : ∀ γ  → Total (_ᴿᴿ γ)

  open Tyᴿ

  record Tmᴿ {ΓLᴿ ΓCᴿ TLᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Tᴿ : Tyᴿ ΓLᴿ TLᴿ)
    (aLᴿ : (γ : ΓLᴿ) → TLᴿ γ)
    (aCᴿ : ∣ A [ ΓCᴿ ]∣) : Set where
    field
      ∣_∣ : ∀ γ (γ' : ∣ Γᴿ ∣ γ) → ∣ Tᴿ ∣ γ (aLᴿ γ)
      _ᵀᴿ : DefTracked (λ (γ , γ') → (aLᴿ γ , ∣_∣ γ γ')) (ΠA aCᴿ) (Γᴿ ᴿᴿ) (λ (γ , γ') → (Tᴿ ᴿᴿ) γ)


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
  R .Model.NfC aC = Defined (ΠA aC)

  R .Model.Ty ΓLᴿ TLᴿ = Tyᴿ ΓLᴿ TLᴿ
  R .Model.Tm Γᴿ Tᴿ aLᴿ aCᴿ = Tmᴿ Γᴿ Tᴿ aLᴿ aCᴿ
  
  R .Model.∙L = ⊤
  (R Model.▷L ΓLᴿ) TLᴿ = Σ[ γ ∈ ΓLᴿ ] TLᴿ γ
  
  R .Model.∙C = zero
  R Model.▷C = suc
  
  ∣ R .Model.∙ ∣ tt = ⊤
  (R .Model.∙ ᴿᴿ) a (tt , tt) = a ＝ I
  ∣ (R Model.▷ Γᴿ) Tᴿ ∣ (γ , t) = Σ[ γ' ∈ ∣ Γᴿ ∣ γ ] ∣ Tᴿ ∣ γ t
  ((R Model.▷ Γᴿ) Tᴿ ᴿᴿ) a ((γ , t) , γ' , t')
    = ∃[ γR ∈ ∣ A ∣ ] ∃[ tR ∈ ∣ A ∣ ]
      ((a ＝ pair γR tR) AND ((γR ⊩[ Γᴿ ᴿᴿ ] (γ , γ')) AND (tR ⊩[ (Tᴿ ᴿᴿ) γ ] (t , t'))))
  ∣ (R Model.▷0 Γᴿ) TLᴿ ∣ (γ , t) = ∣ Γᴿ ∣ γ
  ((R Model.▷0 Γᴿ) TLᴿ ᴿᴿ) a ((γ , t) , γ') = (Γᴿ ᴿᴿ) a (γ , γ')

  (R Model.[p*]) {ΓC = n} t = opn n t
  
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
  
  R .Model.lamC x = lambda x
  R .Model.appC x y = app' x x
  
  ∣ R .Model.Π T U ∣ γ t
    = Σ[ t' ∈ (∀ x (x' : ∣ T ∣ γ x) → ∣ U ∣ (γ , x) (t x)) ]
        (∃Tracked (λ (x , x') → t x , t' x x') ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t)))
  (R .Model.Π T U ᴿᴿ) γ a (f , f' , (_ , p)) = Tracked (λ (x , x') → f x , f' x x') a ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t))
  R .Model.Π T U .total γ (f , f' , (l , p)) = l , p
  ∣ R .Model.lam {tC = tC} record { ∣_∣ = ∣t∣ ; _ᵀᴿ = tᵀᴿ } ∣ γ γ'
    = ((λ x x' → ∣t∣ (γ , x) (γ' , x')) , ∃-rec tᵀᴿ (λ a' p' → {! lambda ?  !} , λ (t , t') a tR → {!   !} , ({!   !} , {!   !})) )
      -- (∃-rec (t ᵀᴿ) (λ a' p → a' , -- ΠAⱽ tC (a' , p .fst) ,
      --   λ (t , t') a tTR → let m = p .snd ((γ , t) , γ' , t') in m a {!   !}))
      -- (∃-elim (λ ex → ∃Tracked (λ (x , x') → {!   !} x , {!   !} x x') {!   !} {!   !}) (t ᵀᴿ) (λ r s → {!   !} , λ (γ , t) a tr → {!   !}))
  R .Model.lam t ᵀᴿ = {!   !}
  ∣ R .Model.app {tL = tL} f x ∣ γ γ' = ∣ f ∣ γ γ' .proj₁ (tL γ) (∣ x ∣ γ γ')
  R .Model.app record { ∣_∣ = ∣f∣ ; _ᵀᴿ = fᵀᴿ } record { ∣_∣ = ∣x∣ ; _ᵀᴿ = xᵀᴿ } ᵀᴿ
    = {!   !}
  

  ∣ R .Model.Spec {ΓL = ΓLᴿ} T c ∣ γ t
    = Σ[ t' ∈ (∣ T ∣ γ t) ] ∃[ c' ∈ ∣ A ∣ ] ((extract c ＝ just c') AND (c' ⊩[ (T ᴿᴿ) γ ] (t , t')))

      -- (∀ {ΓCᴿ} {Γᴿ : Conᴿ ΓLᴿ ΓCᴿ} (γ' : ∣ Γᴿ ∣ γ) → TrackedAt (ΠA (opn ΓCᴿ c)) (γ , γ') (t , t') (Γᴿ ᴿᴿ) (λ (γ , γ') → (T ᴿᴿ) γ))
  (R .Model.Spec T c ᴿᴿ) γ a (t , t' , p) = (c' : ∣ A ∣) → extract c ＝ just c' → a ＝ c'
  R .Model.Spec T c .total γ (t , t' , p) with extract c 
  ... | just c' = c' , λ _ → λ { refl → refl }
  ... | nothing = I , λ _ → λ ()
  ∣ R .Model.spec {ΓC = ΓC} {aC = aC} record { ∣_∣ = ∣t∣ ; _ᵀᴿ = (tC , tC-def , tᵀᴿ) } ∣ γ γ'
    = ∣t∣ γ γ' , is-def (app?- (ΠA (opn ΓC aC)) I) {!   !} , {!   sym ΠA-opn-id !} , {!   !} -- tC , {!   !} , {!   !}
  (R .Model.spec {ΓC = ΓC} {aC = aC} record { ∣_∣ = ∣t∣ ; _ᵀᴿ = tᵀᴿ } ᵀᴿ) = {!   !}
  -- (R .Model.spec {ΓC = ΓC} {aC = aC} t ᵀᴿ) .snd (γ , γ') a p with (t ᵀᴿ) .snd (γ , γ') a p
  -- ... | a' , p' , tTR = a' , p' , λ c' q → just-inj (trs (trs (sym p') ΠA-opn) q)

  ∣ R .Model.unspec t ∣ γ γ' = proj₁ (∣ t ∣ γ γ')
  (R .Model.unspec {T = T} t ᵀᴿ)  = {!   !}
  -- (R .Model.unspec {T = T} t ᵀᴿ) .fst = {!   !}
  -- (R .Model.unspec t ᵀᴿ) .snd (γ , γ') a p = proj₂ (∣ t ∣ γ γ') a p
  