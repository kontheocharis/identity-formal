{-# OPTIONS --prop --cubical -WnoUnsupportedIndexedMatch #-}
module Synthetic.Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Data.Unit
open import Agda.Primitive

open import Synthetic.Model
  
{-# BUILTIN REWRITE _≡_ #-}

-- We will define semantics for the synthetic model by working in the glued
-- topos Set ↓ Γ. This can be emulated in Agda by postulates.

-- In particular, let Λ be the syntactic (initial) uni-typed CwF of lambda
-- calculus terms quotiented by βη. Its objects are natural numbers. We have the
-- presheaf category Psh(Λ) which is a topos, and contains a second-order model
-- of Λ which is the syntax. We can glue along the global sections functor Γ :
-- Psh(Λ) → Set to get a new topos Set ↓ Γ.

postulate
  Ψ : Prop
  
variable
  M N : Type ℓ
  
record _true (P : Prop) : Type where
  constructor [_]
  field
    fact : P

Ψ⇒_ : Type ℓ → Type ℓ
Ψ⇒_ M = (p : Ψ) → M

data Ψ*_ (M : Type ℓ) : Type ℓ where
  nope : (p : Ψ) → Ψ* M
  η : M → Ψ* M
  trivial : (p : Ψ) {x : M} → nope p ≡ η x

*-collapses : (p : Ψ) (y : Ψ* M) → nope p ≡ y
*-collapses p (nope p) = refl
*-collapses p (η x) = trivial p
*-collapses p (trivial p {x = x} i) j = trivial p {x = x} (i ∧ j)

Ψ*Ψ⇒-trivial : Ψ⇒ (Ψ* M) ≃ ⊤
Ψ*Ψ⇒-trivial .fst x = tt
Ψ*Ψ⇒-trivial .snd .equiv-proof tt = (nope , refl) , λ (y , _) i → (λ p → *-collapses p (y p) i) , refl

record Ψ*-Modal (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = Ψ true × M} {B = Ψ true} (λ (p , _) → p)

record Ψ⇒-Modal (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = M} {B = {{p : Ψ}} → M} (λ x → x)

Ψ⇒ᴰ_ : Ψ⇒ (Type ℓ) → Type ℓ
Ψ⇒ᴰ_ A = (p : Ψ) → A p

ext : (A : Type ℓ) → (P : Prop) → ((p : P) → A) → Type ℓ
ext M P x = Σ[ a ∈ M ] ((p : P) → a ≡ x p)

[_∣_↪_] : (A : Type ℓ) → (P : Prop) → ((p : P) → A) → Type ℓ
[_∣_↪_] = ext

syntax ext M P (λ p → x) = [ M ∣ p ∈ P ↪ x ]

give : ∀ {P} (p : P) A → (M : [ Type ℓ ∣ P ↪ A ]) → A p → M .fst
give p _ (M , l) a = transport (sym (l p)) a

give' : ∀ {P} (p : P) A → (M : [ Type ℓ ∣ P ↪ A ]) → M .fst → A p
give' p _ (M , l) a = transport (l p) a

give-give' : ∀ {P} (p : P) A (M : [ Type ℓ ∣ P ↪ A ]) (a : M .fst)
  → give p A M (give' p A M a) ≡ a
give-give' p A M a = transport⁻Transport (M .snd _) a

give'-give : ∀ {P} (p : P) A (M : [ Type ℓ ∣ P ↪ A ]) (a : A p)
  → give' p A M (give p A M a) ≡ a
give'-give p A M a = transportTransport⁻ (M .snd _) a

G : (A : Ψ⇒ (Type ℓ))
  → (B : Ψ⇒ᴰ A → Type ℓ)
  → {{BΨ* : ∀ {a : Ψ⇒ᴰ A} → Ψ*-Modal (B a)}}
  → Type ℓ
G A B = Σ[ a ∈ Ψ⇒ᴰ A ] B a

syntax G A (λ x → B) = G[ x ∈ A ] B

G-collapses : ∀ (p : Ψ) (A : Ψ⇒ (Type ℓ)) (B : Ψ⇒ᴰ A → Type ℓ)
  {{BΨ* : ∀ {a : Ψ⇒ᴰ A} → Ψ*-Modal (B a)}} → G[ a ∈ A ] B a ≡ A p
G-collapses A B = {!   !}

instance
  [_∣Ψ↪_]-is-Ψ*-Modal : {x : Ψ⇒ M} → Ψ*-Modal [ M ∣ Ψ ↪ x ]
  [_∣Ψ↪_]-is-Ψ*-Modal = {!   !}

  Ψ*-is-Ψ*-Modal : Ψ*-Modal (Ψ* M)
  

record Λ : Set (lsuc ℓ) where
  field
    TmΛ : Type ℓ
    lambda : (f : TmΛ → TmΛ) → TmΛ
    apply : TmΛ → TmΛ → TmΛ
    beta : ∀ {f x} → apply (lambda f) x ≡ f x
    eta : ∀ {f} → lambda (λ x → apply f x) ≡ f
    
  zeroΛ : TmΛ
  zeroΛ = lambda (λ z → lambda (λ s → z))

  succΛ : TmΛ → TmΛ
  succΛ n = lambda (λ z → lambda (λ s → apply (apply n z) s))

-- We have a Ψ⇒-modal model of Λ in the glued topos.
postulate
  Λm : Ψ⇒ Λ {ℓ}
  
module _ (p : Ψ) where
  open Λ {lzero} (Λm p) public 
  
open OpTT
open OpTT-sorts
open OpTT-ctors


ms : OpTT-sorts {lzero} {lsuc lzero} {lzero}
ms .$ = Ψ
ms .Ty = [ Type ∣ Ψ ↪ TmΛ ]
ms .Tm z A = Ψ* A .fst
ms .Tm ω A = A .fst
ms .Ex = Ψ⇒ᴰ TmΛ
[ ms ]' = η

id : Ψ⇒ᴰ TmΛ
id p = lambda p (λ x → x)

_>>=_ : Ψ* A → (A → Ψ* B) → Ψ* B
nope p >>= f = nope p
η x >>= f = f x
_>>=_ {B = B} (trivial p {x = x} i) f = *-collapses {M = B} p (f x) i


mc : OpTT-ctors ms
∣ mc ∣ {A~ = A~} x p = give' p TmΛ (A~ p) (x p)
⟨ mc ⟩ {z} x p = nope p
⟨ mc ⟩ {ω} {A~} x p = give p TmΛ (A~ p) (x p)
mc .∣⟨⟩∣ {A~ = A~} {e} j p = give'-give p TmΛ (A~ p) (e p) j
mc .⟨∣∣⟩ {A~ = A~} {t~ = t~} j p = give-give' p TmΛ (A~ p) (t~ p) j
mc .[⟨⟩] {p = p} = sym (trivial p)
mc .∅ = id
mc .bind x ε = x ε
mc .bind x (nope p , γ) = nope p
mc .bind x (η x₁ , γ) = {!   !}
mc .bind x (trivial p i , γ) = {!   !}
mc .bind[]-1 = {!   !}
mc .bind[]-2 = {!   !}
mc .lm f p = lambda p (λ q → f (λ _ → q) p)
mc .ap x y p = apply p (x p) (y p)
mc .ze = zeroΛ
mc .su x p = succΛ p (x p)
-- mc .rec = {!   !}
mc .Π z A X
  = G[ f ∈ TmΛ ]
      [ ((a : Ψ* A .fst) → X a .fst)
        ∣ p ∈ Ψ ↪ (λ a → give p TmΛ (X a) (f p)) ] , {!   !}
mc .Π ω A X
  = G[ f ∈ TmΛ ]
      [ ((a : A .fst) → X (η a) .fst)
        ∣ p ∈ Ψ ↪ (λ a → give p TmΛ (X (η a)) (apply p (f p) (give' p TmΛ A a))) ] , {!   !}
mc .lam {z} {i = z} f = do
  
  {!!}
mc .lam {ω} {i = z} f = {!!}
mc .lam {z} {i = ω} {X} f
  = (λ p → give' p TmΛ (X _) (f (nope p))) ,
    f , λ p q → {!!}
mc .lam {ω} {i = ω} f = {!   !}
-- mc .app = {!   !}
-- mc .lam-app-z = {!   !}
-- mc .app-lam-z = {!   !}
-- mc .∣lam-ω∣ = {!   !}
-- mc .∣app-ω∣ = {!   !}
-- mc .∣lam-z∣ = {!   !}
-- mc .∣app-z∣ = {!   !}
-- mc .[lam] = {!   !}
-- mc .[app] = {!   !}
-- mc .* = {!   !}
-- ⌜ mc ⌝ = {!   !}
-- ⌞ mc ⌟ = {!   !}
-- mc .⌞⌟-⌜⌝ = {!   !}
-- mc .⌜⌝-⌞⌟ = {!   !}
-- mc .Spec = {!   !}
-- mc .specz = {!   !}
-- mc .spec = {!   !}
-- mc .unspec = {!   !}
-- mc .∣spec∣ = {!   !}
-- mc .∣unspec∣ = {!   !}
-- mc .[spec] = {!   !}
-- mc .[unspec] = {!   !}
-- mc .Nat = {!   !}
-- mc .zero = {!   !}
-- mc .succ = {!   !}
-- mc .elim-Nat = {!   !}
-- mc .elim-Nat-zero-z = {!   !}
-- mc .elim-Nat-succ-z = {!   !}
-- mc .∣zero∣ = {!   !}
-- mc .∣succ∣ = {!   !}
-- mc .∣elim-Nat-ω∣ = {!   !}
-- mc .[zero] = {!   !}
-- mc .[succ] = {!   !}
-- mc .[elim-Nat] = {!   !}
-- mc .Num = {!   !}
-- mc .nat-num = {!   !}
-- mc .rec-η-1 = {!   !}
-- mc .rec-η-2 = {!   !}

  
m : OpTT {lzero} {lsuc lzero} {lzero}
m .sorts = ms
m .ctors = mc
