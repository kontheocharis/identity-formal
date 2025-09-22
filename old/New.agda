module New where

open import Relation.Binary.PropositionalEquality
-- open import Cubical.Foundations.Prelude hiding (Sub; _∨_)
-- open import Cubical.Data.Empty hiding (rec)
-- open import Cubical.Data.Sum hiding (rec)
-- open import Cubical.HITs.PropositionalTruncation hiding (rec)
open import Relation.Nullary

data Con : Set
data Tm : Con → Set
data Var : Con → Set

variable
  Γ Δ : Con
  z z' s s' f f' t t' a a' b b' n : Tm _
  v v' : Var _

data _≈_ : Tm Γ → Tm Γ → Set

data Con where
  ∙ : Con
  _▷ : Con → Con
  
data Var where
  vz : Var (Γ ▷)
  vs : Var Γ → Var (Γ ▷)

_var≡?_ : (a : Var Γ) → (b : Var Γ) → Dec (a ≡ b)
vz var≡? vz = yes refl
vz var≡? vs w = no λ ()
vs v var≡? vz = no λ ()
vs v var≡? vs w with v var≡? w
... | yes p = yes (cong vs p)
... | no q = no λ { refl → q refl }
  
Sub : Con → Con → Set
Sub Γ Δ = Var Δ → Tm Γ
  
data Tm where
  var : Var Γ → Tm Γ
  lam : Tm (Γ ▷) → Tm Γ
  app : Tm Γ → Tm Γ → Tm Γ

  zero : Tm Γ
  succ : Tm Γ → Tm Γ
  rec : (z : Tm Γ) → (s : Tm (Γ ▷)) → Tm Γ → Tm Γ
  
data _≈_ where
  var≈ : v ≡ v' → var v ≈ var v'
  lam≈ : f ≈ f' → lam f ≈ lam f'
  app≈ : f ≈ f' → a ≈ a' → app f a ≈ app f' a'

  zero≈ : zero {Γ} ≈ zero
  succ≈ : t ≈ t' → succ t ≈ succ t'
  rec≈ : z ≈ z' → s ≈ s' → t ≈ t' → rec z s t ≈ rec z' s' t'
  
  recη : z ≈ zero → s ≈ succ (var vz) → n ≈ t → rec z s n ≈ t
  recη-sym : zero ≈ z → succ (var vz) ≈ s → t ≈ n → t ≈ rec z s n
  
_≈?_ : (a : Tm Γ) → (b : Tm Γ) → Dec (a ≈ b)
var x ≈? var x₁ with x var≡? x₁
... | yes p = yes (var≈ p)
... | no q = no λ { (var≈ p) → q p }
var x ≈? lam b = no λ ()
var x ≈? app b b₁ = no λ ()
var x ≈? zero = no λ ()
var x ≈? succ b = no λ ()
lam a ≈? var x = no λ ()
lam a ≈? lam b with a ≈? b
... | yes p = yes (lam≈ p)
... | no q = no λ { (lam≈ p) → q p }
lam a ≈? app b b₁ = no λ ()
lam a ≈? zero = no λ ()
lam a ≈? succ b = no λ ()
app a a₁ ≈? var x = no λ ()
app a a₁ ≈? lam b = no λ ()
app a a₁ ≈? app b b₁ with a ≈? b | a₁ ≈? b₁
... | yes p | yes q = yes (app≈ p q)
... | yes p | no q = no λ { (app≈ p r) → q r }
... | no p | _ = no λ { (app≈ r s) → p r }
app a a₁ ≈? zero = no λ ()
app a a₁ ≈? succ b = no λ ()
zero ≈? var x = no λ ()
zero ≈? lam b = no λ ()
zero ≈? app b b₁ = no λ ()
zero ≈? zero = yes zero≈
zero ≈? succ b = no λ ()
succ a ≈? var x = no λ ()
succ a ≈? lam b = no λ ()
succ a ≈? app b b₁ = no λ ()
succ a ≈? zero = no λ ()
succ a ≈? succ b with a ≈? b
... | yes p = yes (succ≈ p)
... | no q = no λ { (succ≈ p) → q p }
u ≈? rec z s t with u | u ≈? t | zero ≈? z | succ (var vz) ≈? s
... | _ | yes p | yes q | yes r = yes (recη-sym q r p)
... | var x | no q | _ | _ = no (λ { (recη-sym r r₁ r₂) → q r₂ })
... | lam u₁ | no q | _ | _ = no (λ { (recη-sym r r₁ r₂) → q r₂ })
... | app u₁ u₂ | no q | _ | _ = no (λ { (recη-sym r r₁ r₂) → q r₂ })
... | zero | no q | _ | _ = no (λ { (recη-sym r r₁ r₂) → q r₂ })
... | succ u₁ | no q | _ | _ = no (λ { (recη-sym r r₁ r₂) → q r₂ })
... | rec u₁ u₂ u₃ | no q | _ | _ = no (λ { (rec≈ s s₁ s₂) → {!   !}
                                          ; (recη s s₁ s₂) → {!   !}
                                          ; (recη-sym s s₁ s₂) → q s₂ })
rec z s t ≈? u = {!   !}
  
-- data Nf' : Tm Γ → Set where
--   lamᴺ : Nf' f → Nf' (lam f)
--   appᴺ : Nf' f → Nf' a → Nf' (app f a)
--   varᴺ : (v : Var Γ) → Nf' (var v)
--   zeroᴺ : Nf' (zero {Γ})
--   succᴺ : Nf' t → Nf' (succ t)
--   recᴺ : Nf' z → Nf' s → Nf' t → Nf' (rec z s t)
  
-- variable
--   zᴺ : Nf' z
--   sᴺ : Nf' s
--   tᴺ : Nf' t
--   aᴺ : Nf' a
--   bᴺ : Nf' b
--   fᴺ : Nf' f
  
-- infix 4 _≢_
-- _≢_ : ∀ {Γ a b} (x : Nf' {Γ} a) (y : Nf' {Γ} b) → Set
-- _≢_ {a = a} {b = b} x y = (p : a ≡ b) → PathP (λ i → Nf' (p i)) x y → ⊥

-- _∨_ : Set → Set → Set
-- A ∨ B = ∥ A ⊎ B ∥₁

-- left : {A B : Set} → A → A ∨ B
-- left a = ∣ inl a ∣₁

-- right : {A B : Set} → B → A ∨ B
-- right b = ∣ inr b ∣₁

-- data Wf : Nf' t → Set where
--   lamᵂ : Wf fᴺ → Wf (lamᴺ fᴺ)
--   appᵂ : Wf fᴺ → Wf aᴺ → Wf (appᴺ fᴺ aᴺ)
--   varᵂ : Wf (varᴺ v)
--   zeroᵂ : Wf (zeroᴺ {Γ = Γ})
--   succᵂ : Wf tᴺ → Wf (succᴺ tᴺ)
--   recᵂ : Wf zᴺ → Wf sᴺ → Wf tᴺ
--     → (zᴺ ≢ zeroᴺ) ∨ (sᴺ ≢ succᴺ (varᴺ vz))
--     → Wf (recᴺ zᴺ sᴺ tᴺ)

-- Nf : Tm Γ → Set
-- Nf t = Σ[ n ∈ Nf' t ] Wf n

-- _≡?_ : (a : Tm Γ) → (b : Tm Γ) → Dec (a ≡ b)
-- var x ≡? var x₁ = {!   !}
-- var x ≡? lam b = {!   !}
-- var x ≡? app b b₁ = {!   !}
-- var x ≡? zero = {!   !}
-- var x ≡? succ b = {!   !}
-- var x ≡? rec b b₁ b₂ = {!   !}
-- var x ≡? recη i = {!   !}
-- var x ≡? trunc b b₁ x₁ y i i₁ = {!   !}
-- lam a ≡? var x = {!   !}
-- lam a ≡? lam b = {!   !}
-- lam a ≡? app b b₁ = {!   !}
-- lam a ≡? zero = {!   !}
-- lam a ≡? succ b = {!   !}
-- lam a ≡? rec b b₁ b₂ = {!   !}
-- lam a ≡? recη i = {!   !}
-- lam a ≡? trunc b b₁ x y i i₁ = {!   !}
-- app a a₁ ≡? var x = {!   !}
-- app a a₁ ≡? lam b = {!   !}
-- app a a₁ ≡? app b b₁ = {!   !}
-- app a a₁ ≡? zero = {!   !}
-- app a a₁ ≡? succ b = {!   !}
-- app a a₁ ≡? rec b b₁ b₂ = {!   !}
-- app a a₁ ≡? recη i = {!   !}
-- app a a₁ ≡? trunc b b₁ x y i i₁ = {!   !}
-- zero ≡? var x = {!   !}
-- zero ≡? lam b = {!   !}
-- zero ≡? app b b₁ = {!   !}
-- zero ≡? zero = {!   !}
-- zero ≡? succ b = {!   !}
-- zero ≡? rec b b₁ b₂ = {!   !}
-- zero ≡? recη i = {!   !}
-- zero ≡? trunc b b₁ x y i i₁ = {!   !}
-- succ a ≡? var x = {!   !}
-- succ a ≡? lam b = {!   !}
-- succ a ≡? app b b₁ = {!   !}
-- succ a ≡? zero = {!   !}
-- succ a ≡? succ b = {!   !}
-- succ a ≡? rec b b₁ b₂ = {!   !}
-- succ a ≡? recη i = {!   !}
-- succ a ≡? trunc b b₁ x y i i₁ = {!   !}
-- rec a a₁ a₂ ≡? var x = {!   !}
-- rec a a₁ a₂ ≡? lam b = {!   !}
-- rec a a₁ a₂ ≡? app b b₁ = {!   !}
-- rec a a₁ a₂ ≡? zero = {!   !}
-- rec a a₁ a₂ ≡? succ b = {!   !}
-- rec a a₁ a₂ ≡? rec b b₁ b₂ = {!   !}
-- rec a a₁ a₂ ≡? recη i = {!   !}
-- rec a a₁ a₂ ≡? trunc b b₁ x y i i₁ = {!   !}
-- recη i ≡? var x = {!   !}
-- recη i ≡? lam b = {!   !}
-- recη i ≡? app b b₁ = {!   !}
-- recη i ≡? zero = {!   !}
-- recη i ≡? succ b = {!   !}
-- recη i ≡? rec b b₁ b₂ = {!   !}
-- recη i ≡? recη i₁ = {!   !}
-- recη i ≡? trunc b b₁ x y i₁ i₂ = {!   !}
-- trunc a a₁ x y i i₁ ≡? var x₁ = {!   !}
-- trunc a a₁ x y i i₁ ≡? lam b = {!   !}
-- trunc a a₁ x y i i₁ ≡? app b b₁ = {!   !}
-- trunc a a₁ x y i i₁ ≡? zero = {!   !}
-- trunc a a₁ x y i i₁ ≡? succ b = {!   !}
-- trunc a a₁ x y i i₁ ≡? rec b b₁ b₂ = {!   !}
-- trunc a a₁ x y i i₁ ≡? recη i₂ = {!   !}
-- trunc a a₁ x y i i₁ ≡? trunc b b₁ x₁ y₁ i₂ i₃ = {!   !}

-- nf : (t : Tm Γ) → Nf t
-- nf (var v) = varᴺ v , varᵂ
-- nf (lam f) =
--   let (fᴺ , fᴼ) = nf f in
--   lamᴺ fᴺ , lamᵂ fᴼ
-- nf (app f x) =
--   let (fᴺ , fᵂ) = nf f in
--   let (xᴺ , xᵂ) = nf x in
--   appᴺ fᴺ xᴺ , appᵂ fᵂ xᵂ
-- nf zero = zeroᴺ , zeroᵂ
-- nf (succ t) = 
--   let (tᴺ , tᵂ) = nf t in
--   succᴺ tᴺ , succᵂ tᵂ
-- nf (rec z s t) with (nf z) | (nf s) | (nf t)
-- ... | (zᴺ , zᵂ) | (sᴺ , sᵂ) | (tᴺ , tᵂ) with zᴺ | zᵂ | sᴺ | sᵂ
-- ... | zeroᴺ | zeroᵂ | succᴺ (varᴺ vz) | succᵂ varᵂ = subst (λ t → Nf t) (sym recη) (tᴺ , tᵂ)
-- ... | lamᴺ zᴺ₁ | lamᵂ zᵂ₁ | lamᴺ sᴺ₁ | lamᵂ sᵂ₁ = recᴺ zᴺ sᴺ tᴺ , recᵂ zᵂ sᵂ tᵂ (left λ p pᴾ → {!   !})
-- ... | lamᴺ zᴺ₁ | lamᵂ zᵂ₁ | appᴺ sᴺ₁ sᴺ₂ | appᵂ sᵂ₁ sᵂ₂ = {!   !}
-- ... | lamᴺ zᴺ₁ | lamᵂ zᵂ₁ | varᴺ v | varᵂ = {!   !}
-- ... | lamᴺ zᴺ₁ | lamᵂ zᵂ₁ | zeroᴺ | zeroᵂ = {!   !}
-- ... | lamᴺ zᴺ₁ | lamᵂ zᵂ₁ | succᴺ sᴺ₁ | succᵂ sᵂ₁ = {!   !}
-- ... | lamᴺ zᴺ₁ | lamᵂ zᵂ₁ | recᴺ sᴺ₁ sᴺ₂ sᴺ₃ | recᵂ sᵂ₁ sᵂ₂ sᵂ₃ x = {!   !}
-- ... | appᴺ zᴺ₁ zᴺ₂ | appᵂ zᵂ₁ zᵂ₂ | lamᴺ sᴺ₁ | lamᵂ sᵂ₁ = {!   !}
-- ... | appᴺ zᴺ₁ zᴺ₂ | appᵂ zᵂ₁ zᵂ₂ | appᴺ sᴺ₁ sᴺ₂ | appᵂ sᵂ₁ sᵂ₂ = {!   !}
-- ... | appᴺ zᴺ₁ zᴺ₂ | appᵂ zᵂ₁ zᵂ₂ | varᴺ v | varᵂ = {!   !}
-- ... | appᴺ zᴺ₁ zᴺ₂ | appᵂ zᵂ₁ zᵂ₂ | zeroᴺ | zeroᵂ = {!   !}
-- ... | appᴺ zᴺ₁ zᴺ₂ | appᵂ zᵂ₁ zᵂ₂ | succᴺ sᴺ₁ | succᵂ sᵂ₁ = {!   !}
-- ... | appᴺ zᴺ₁ zᴺ₂ | appᵂ zᵂ₁ zᵂ₂ | recᴺ sᴺ₁ sᴺ₂ sᴺ₃ | recᵂ sᵂ₁ sᵂ₂ sᵂ₃ x = {!   !}
-- ... | varᴺ v | varᵂ | lamᴺ sᴺ₁ | lamᵂ sᵂ₁ = {!   !}
-- ... | varᴺ v | varᵂ | appᴺ sᴺ₁ sᴺ₂ | appᵂ sᵂ₁ sᵂ₂ = {!   !}
-- ... | varᴺ v | varᵂ | varᴺ v₁ | varᵂ = {!   !}
-- ... | varᴺ v | varᵂ | zeroᴺ | zeroᵂ = {!   !}
-- ... | varᴺ v | varᵂ | succᴺ sᴺ₁ | succᵂ sᵂ₁ = {!   !}
-- ... | varᴺ v | varᵂ | recᴺ sᴺ₁ sᴺ₂ sᴺ₃ | recᵂ sᵂ₁ sᵂ₂ sᵂ₃ x = {!   !}
-- ... | zeroᴺ | zeroᵂ | lamᴺ sᴺ₁ | lamᵂ sᵂ₁ = {!   !}
-- ... | zeroᴺ | zeroᵂ | appᴺ sᴺ₁ sᴺ₂ | appᵂ sᵂ₁ sᵂ₂ = {!   !}
-- ... | zeroᴺ | zeroᵂ | varᴺ v | varᵂ = {!   !}
-- ... | zeroᴺ | zeroᵂ | zeroᴺ | zeroᵂ = {!   !}
-- ... | zeroᴺ | zeroᵂ | succᴺ sᴺ₁ | succᵂ sᵂ₁ = {!   !}
-- ... | zeroᴺ | zeroᵂ | recᴺ sᴺ₁ sᴺ₂ sᴺ₃ | recᵂ sᵂ₁ sᵂ₂ sᵂ₃ x = {!   !}
-- ... | succᴺ zᴺ₁ | succᵂ zᵂ₁ | lamᴺ sᴺ₁ | lamᵂ sᵂ₁ = {!   !}
-- ... | succᴺ zᴺ₁ | succᵂ zᵂ₁ | appᴺ sᴺ₁ sᴺ₂ | appᵂ sᵂ₁ sᵂ₂ = {!   !}
-- ... | succᴺ zᴺ₁ | succᵂ zᵂ₁ | varᴺ v | varᵂ = {!   !}
-- ... | succᴺ zᴺ₁ | succᵂ zᵂ₁ | zeroᴺ | zeroᵂ = {!   !}
-- ... | succᴺ zᴺ₁ | succᵂ zᵂ₁ | succᴺ sᴺ₁ | succᵂ sᵂ₁ = {!   !}
-- ... | succᴺ zᴺ₁ | succᵂ zᵂ₁ | recᴺ sᴺ₁ sᴺ₂ sᴺ₃ | recᵂ sᵂ₁ sᵂ₂ sᵂ₃ x = {!   !}
-- ... | recᴺ zᴺ₁ zᴺ₂ zᴺ₃ | recᵂ zᵂ₁ zᵂ₂ zᵂ₃ x | lamᴺ sᴺ₁ | lamᵂ sᵂ₁ = {!   !}
-- ... | recᴺ zᴺ₁ zᴺ₂ zᴺ₃ | recᵂ zᵂ₁ zᵂ₂ zᵂ₃ x | appᴺ sᴺ₁ sᴺ₂ | appᵂ sᵂ₁ sᵂ₂ = {!   !}
-- ... | recᴺ zᴺ₁ zᴺ₂ zᴺ₃ | recᵂ zᵂ₁ zᵂ₂ zᵂ₃ x | varᴺ v | varᵂ = {!   !}
-- ... | recᴺ zᴺ₁ zᴺ₂ zᴺ₃ | recᵂ zᵂ₁ zᵂ₂ zᵂ₃ x | zeroᴺ | zeroᵂ = {!   !}
-- ... | recᴺ zᴺ₁ zᴺ₂ zᴺ₃ | recᵂ zᵂ₁ zᵂ₂ zᵂ₃ x | succᴺ sᴺ₁ | succᵂ sᵂ₁ = {!   !}
-- ... | recᴺ zᴺ₁ zᴺ₂ zᴺ₃ | recᵂ zᵂ₁ zᵂ₂ zᵂ₃ x | recᴺ sᴺ₁ sᴺ₂ sᴺ₃ | recᵂ sᵂ₁ sᵂ₂ sᵂ₃ x₁ = {!   !}
-- nf (recη i) = {!   !}
-- nf (trunc x x₁ x₂ y i i₁) = {!   !}
  
-- -- -- Sub : Con → Con → Set
-- -- -- Sub 