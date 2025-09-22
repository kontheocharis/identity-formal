module New.New where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sum hiding (rec)

data Con : Set
data Tm : Con → Set
data Var : Con → Set

variable
  Γ Δ : Con
  z s f t a b : Tm _
  v : Var _

data Con where
  ∙ : Con
  _▷ : Con → Con
  
data Var where
  vz : Var (Γ ▷)
  vs : Var Γ → Var (Γ ▷)
  
Sub : Con → Con → Set
Sub Γ Δ = Var Δ → Tm Γ
  
data Tm where
  var : Var Γ → Tm Γ
  lam : Tm (Γ ▷) → Tm Γ
  app : Tm Γ → Tm Γ → Tm Γ

  zero : Tm Γ
  succ : Tm Γ → Tm Γ
  rec : (z : Tm Γ) → (s : Tm (Γ ▷)) → Tm Γ → Tm Γ
  
  recη : rec zero (succ (var vz)) t ≡ t
  
  trunc : isSet (Tm Γ)
  
data Nf' : Tm Γ → Set where
  lamᴺ : Nf' f → Nf' (lam f)
  appᴺ : Nf' f → Nf' a → Nf' (app f a)
  varᴺ : (v : Var Γ) → Nf' (var v)
  zeroᴺ : Nf' (zero {Γ})
  succᴺ : Nf' t → Nf' (succ t)
  recᴺ : Nf' z → Nf' s → Nf' t → Nf' (rec z s t)
  
variable
  zᴺ : Nf' z
  sᴺ : Nf' s
  tᴺ : Nf' t
  aᴺ : Nf' a
  bᴺ : Nf' b
  fᴺ : Nf' f
  
infix 4 _≢_
_≢_ : ∀ {i} {A : Set i} (x : A) (y : A) → Set i
a ≢ b = (a ≡ b) → ⊥

data Wf : Nf' t → Set where
  lamᵂ : Wf fᴺ → Wf (lamᴺ fᴺ)
  appᵂ : Wf fᴺ → Wf aᴺ → Wf (appᴺ fᴺ aᴺ)
  varᵂ : Wf (varᴺ v)
  zeroᵂ : Wf (zeroᴺ {Γ = Γ})
  succᵂ : Wf tᴺ → Wf (succᴺ tᴺ)
  recᵂ : Wf zᴺ → Wf sᴺ → Wf tᴺ
    → (zᴺ ≢ zeroᴺ) ⊎ (sᴺ ≢ succᴺ (varᴺ vz))
    → Wf (recᴺ zᴺ sᴺ tᴺ)

Nf : Tm Γ → Set
Nf t = Σ[ n ∈ Nf' t ] Wf n

nf : (t : Tm Γ) → Nf t
nf (var v) = varᴺ v , varᵂ
nf (lam f) =
  let (fᴺ , fᴼ) = nf f in
  lamᴺ fᴺ , lamᵂ fᴼ
nf (app f x) =
  let (fᴺ , fᵂ) = nf f in
  let (xᴺ , xᵂ) = nf x in
  appᴺ fᴺ xᴺ , appᵂ fᵂ xᵂ
nf zero = zeroᴺ , zeroᵂ
nf (succ t) = 
  let (tᴺ , tᵂ) = nf t in
  succᴺ tᴺ , succᵂ tᵂ
nf (rec x x₁ x₂) = {!   !}
nf (recη i) = {!   !}
nf (trunc x x₁ x₂ y i i₁) = {!   !}
  
-- Sub : Con → Con → Set
-- Sub 