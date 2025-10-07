module Models.Realizability where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; [_]; []; _∷_; lookup; map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

open import Model
open import Realizability
open import Utils

module OverPCA (A : PCA) where

  open Realizability.Relations A public

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

  open Subᴿ public

  record Tyᴿ (ΓLᴿ : Set) (TLᴿ : ΓLᴿ → Set) : Set1 where
    field
      ∣_∣ : ∀ γ → TLᴿ γ → Set
      _ᴿᴿ : ∀ γ → RRel 1 (Σ[ t ∈ TLᴿ γ ] ∣_∣ γ t)
      total : ∀ γ  → Total (_ᴿᴿ γ)

  open Tyᴿ public

  record Tmᴿ {ΓLᴿ ΓCᴿ TLᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Tᴿ : Tyᴿ ΓLᴿ TLᴿ)
    (aLᴿ : (γ : ΓLᴿ) → TLᴿ γ)
    (aCᴿ : ∣ A [ ΓCᴿ ]∣) : Set where
    field
      ∣_∣ : ∀ γ (γ' : ∣ Γᴿ ∣ γ) → ∣ Tᴿ ∣ γ (aLᴿ γ)
      _ᵀᴿ : Tracked (λ (γ , γ') → (aLᴿ γ , ∣_∣ γ γ')) [ aCᴿ ] (Γᴿ ᴿᴿ) (λ (γ , γ') → (Tᴿ ᴿᴿ) γ)


  open Tmᴿ public

  R : TT

  R .TT.ConL = Set
  R .TT.ConC = ℕ
  R .TT.Con ΓLᴿ ΓCᴿ = Conᴿ ΓLᴿ ΓCᴿ

  R .TT.SubL ΓLᴿ ΔLᴿ = ΓLᴿ → ΔLᴿ
  R .TT.SubC ΓCᴿ ΔCᴿ = ∣ A [ ΓCᴿ ]∣^ ΔCᴿ
  R .TT.Sub Γᴿ Δᴿ σLᴿ σCᴿ = Subᴿ Γᴿ Δᴿ σLᴿ σCᴿ

  R .TT.TyL ΓLᴿ = ΓLᴿ → Set
  R .TT.TmL ΓLᴿ TLᴿ = (γ : ΓLᴿ) → TLᴿ γ

  R .TT.TmC ΓCᴿ = ∣ A [ ΓCᴿ ]∣

  R .TT.Ty ΓLᴿ TLᴿ = Tyᴿ ΓLᴿ TLᴿ
  R .TT.Tm Γᴿ Tᴿ aLᴿ aCᴿ = Tmᴿ Γᴿ Tᴿ aLᴿ aCᴿ
  
  R .TT.∙L = ⊤
  (R TT.▷L ΓLᴿ) TLᴿ = Σ[ γ ∈ ΓLᴿ ] TLᴿ γ
  
  R .TT.∙C = zero
  R TT.▷C = suc
  
  ∣ R .TT.∙ ∣ tt = ⊤
  (R .TT.∙ ᴿᴿ) [] (tt , tt) = ⊤
  ∣ (R TT.▷ Γᴿ) Tᴿ ∣ (γ , t) = Σ[ γ' ∈ ∣ Γᴿ ∣ γ ] ∣ Tᴿ ∣ γ t
  ((R TT.▷ Γᴿ) Tᴿ ᴿᴿ) (tR ∷ γR) ((γ , t) , γ' , t')
    = (γR ⊩[ Γᴿ ᴿᴿ ] (γ , γ')) × ([ tR ] ⊩[ (Tᴿ ᴿᴿ) γ ] (t , t'))
  ∣ (R TT.▷0 Γᴿ) TLᴿ ∣ (γ , t) = ∣ Γᴿ ∣ γ
  ((R TT.▷0 Γᴿ) TLᴿ ᴿᴿ) a ((γ , t) , γ') = (Γᴿ ᴿᴿ) a (γ , γ')
  
  R .TT.∙ .total _ = [] , tt
  (R TT.▷ Γ) T .total ((γ , t) , (γ' , t')) with (Γ .total (γ , γ')) | (T .total γ (t , t'))
  ... | γTR , γTotal | (tTR ∷ []) , tTotal
      = tTR ∷ γTR , γTotal , tTotal
  (R TT.▷0 Γ) T .total ((γ , t) , γ') = Γ .total (γ , γ')

  (R TT.[p*]) {ΓC = n} t = opn t
  
  R .TT._[_]TL TLᴿ σLᴿ γ = TLᴿ (σLᴿ γ)
  ∣ (R TT.[ Tᴿ ]T) σLᴿ ∣ γ = ∣ Tᴿ ∣ (σLᴿ γ)
  ((R TT.[ Tᴿ ]T) σLᴿ ᴿᴿ) γ a (t , t') = a ⊩[ (Tᴿ ᴿᴿ) (σLᴿ γ) ] (t , t')
  (R TT.[ Tᴿ ]T) σLᴿ .total γ = Tᴿ .total (σLᴿ γ)

  R .TT._[_]L tLᴿ σLᴿ γ = tLᴿ (σLᴿ γ)
  R .TT.idL γ = γ
  R .TT._,L_ σLᴿ tLᴿ γ = σLᴿ γ , tLᴿ γ

  R .TT.ΠL TLᴿ ULᴿ γ = (t : TLᴿ γ) → ULᴿ (γ , t)
  R .TT.lamL t γ t₁ = t (γ , t₁)
  R .TT.apL x (γ , t) = x γ t
  R .TT.βL t = refl
  R .TT.ηL t = refl
  
  R .TT.lamC x = Λ' x
  R .TT.appC x y = x ∙' y
  
  ∣ R .TT.Π T U ∣ γ t
    = Σ[ t' ∈ (∀ x (x' : ∣ T ∣ γ x) → ∣ U ∣ (γ , x) (t x)) ]
        (∃Tracked (λ (x , x') → t x , t' x x') ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t)))
  (R .TT.Π T U ᴿᴿ) γ (a ∷ []) (f , f' , (_ , p))
    = Tracked (λ (x , x') → f x , f' x x') [ ⌜ a ⌝ ∙' v zero ] ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t))
  -- R .TT.Π T U .total γ (f , f' , (l , p)) = [ {!   !} ] , {!  p !}
  -- ∣ R .TT.lam {tC = tC} record { ∣_∣ = ∣t∣ ; _ᵀᴿ = tᵀᴿ } ∣ γ γ'
  --   = ((λ x x' → ∣t∣ (γ , x) (γ' , x')) , {!   !} )
  --     -- (∃-rec (t ᵀᴿ) (λ a' p → a' , -- ΠAⱽ tC (a' , p .fst) ,
  --     --   λ (t , t') a tTR → let m = p .snd ((γ , t) , γ' , t') in m a {!   !}))
  --     -- (∃-elim (λ ex → ∃Tracked (λ (x , x') → {!   !} x , {!   !} x x') {!   !} {!   !}) (t ᵀᴿ) (λ r s → {!   !} , λ (γ , t) a tr → {!   !}))
  -- R .TT.lam t ᵀᴿ = {!   !}
  -- ∣ R .TT.app {tL = tL} f x ∣ γ γ' = ∣ f ∣ γ γ' .proj₁ (tL γ) (∣ x ∣ γ γ')
  -- R .TT.app record { ∣_∣ = ∣f∣ ; _ᵀᴿ = fᵀᴿ } record { ∣_∣ = ∣x∣ ; _ᵀᴿ = xᵀᴿ } ᵀᴿ
  --   = {!   !}
  

  ∣ R .TT.Spec {ΓL = ΓLᴿ} T c ∣ γ t
    = Σ[ t' ∈ (∣ T ∣ γ t) ] ([ extract c ] !⊩[ (T ᴿᴿ) γ ] (t , t'))
  (R .TT.Spec T c ᴿᴿ) γ a (t , t' , p) = extract c ≡ just (Data.Vec.head a)
  R .TT.Spec T c .total γ (t , t' , (c↓ ∷ []) , p) = [ _ ↓by c↓ ] , def-id c↓
  ∣ R .TT.spec {ΓC = ΓC} {Γ = Γ} {T = T} {aC = aC} t ∣ γ γ'
    = ∣ t ∣ γ γ' ,
        let (γTR , γTotal) = Γ .total (γ , γ') in 
        (t ᵀᴿ) (γ , γ') γTR γTotal
  (R .TT.spec {ΓC = ΓC} {Γ = Γ} {aC = aC} t ᵀᴿ) (γ , γ') a p
    with Γ .total (γ , γ')
  ... | (γTR , γTotal) with (t ᵀᴿ) (γ , γ') γTR γTotal
  ... | (aC↓ ∷ [] , tTotal) = aC↓ ∷ [] , def-id aC↓
  ∣ R .TT.unspec t ∣ γ γ' = proj₁ (∣ t ∣ γ γ')
  (R .TT.unspec {T = T} {aC = aC} t ᵀᴿ) (γ , γ') a p = ∣ t ∣ γ γ' .proj₂
  
  
module Results (A : PCA) where
  open OverPCA A
  open TT R
  
  -- The interpretation of a term in the empty context
  -- produces a defined element of the PCA
  lem1 : ∀ {TL} {T : Ty ∙L TL} {c t}
    → Tm (∙) T t c
    → extract c ↓
  lem1 t with el ∷ [] , tr ← (t ᵀᴿ) (tt , tt) [] tt = el

  -- In particular, every Spec term in the empty context
  -- is annotated by a defined element of the PCA
  lem2 : ∀ {TL} {T : Ty ∙L TL} {c c' t}
    → Tm (∙) (Spec T c) t c'
    → extract c ↓
  lem2 t = lem1 (unspec t)

  -- The 'meaning' interpretation of a term in the empty context
  -- is tracked by its PCA element
  lem3 : ∀ {TL} {T : Ty ∙L TL} {c t}
    → (t' : Tm (∙) T t c)
    → [ extract c ↓by lem1 t' ] ⊩[ (T ᴿᴿ) tt ] (t tt , ∣ t' ∣ tt tt)
  lem3 t' with el ∷ [] , tr ← (t' ᵀᴿ) (tt , tt) [] tt = tr

  -- So for a Spec term in the empty context,
  -- its annotated PCA element tracks its meaning interpretation
  lem4 : ∀ {TL} {T : Ty ∙L TL} {c c' t}
    → (t' : Tm (∙) (Spec T c) t c')
    → [ extract c ↓by lem2 t' ] ⊩[ (T ᴿᴿ) tt ] (t tt , ∣ unspec t' ∣ tt tt)
  lem4 t = lem3 (unspec t)