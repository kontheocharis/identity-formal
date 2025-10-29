{-# OPTIONS --prop --cubical -WnoUnsupportedIndexedMatch --allow-unsolved-metas #-}
module Synthetic.Utils where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Data.Unit
open import Data.Empty
open import Agda.Primitive

private
  variable
    ℓ ℓ' : Level
    M N : Type ℓ
    P : Prop
  
record _true (P : Prop) : Type where
  constructor [_]
  field
    fact : P

data _or_ (P Q : Prop) : Prop where
  inl : P → P or Q
  inr : Q → P or Q

open _true

data _⋆_ (P : Prop) (M : Type ℓ) : Type ℓ where
  nope : (p : P) → P ⋆ M
  η : M → P ⋆ M
  trivial : (p : P) {x : M} → nope p ≡ η x

⋆-collapses : (p : P) (y : P ⋆ M) → nope p ≡ y
⋆-collapses p (nope p) = refl
⋆-collapses p (η x) = trivial p
⋆-collapses p (trivial p {x = x} i) j = trivial p {x = x} (i ∧ j)

⋆→-trivial : P → (P ⋆ M) ≃ ⊤
⋆→-trivial p .fst x = tt
⋆→-trivial p .snd .equiv-proof tt = (nope p , refl) , λ (y , _) i → (⋆-collapses p y i) , refl

record _⋆-Modal_ (P : Prop) (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = P true × M} {B = P true} (λ (p , _) → p)

  collapses : P → isContr M
  collapses p = invIsEq prf [ p ] .snd
    ,  λ m →  λ i → retIsEq prf ([ p ] , m) i .snd

  nope' : (p : P) → M
  nope' p = invIsEq prf [ p ] .snd

  trivial' : (p : P) {x : M} → nope' p ≡ x
  trivial' p {x = x} = collapses p .snd x

open _⋆-Modal_

record _→-Modal (P : Prop) (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = M} {B = {{p : P}} → M} (λ x → x)

_→ᴰ_ : (P : Prop) → (P → Type ℓ) → Type ℓ
_→ᴰ_ P A = (p : P) → A p

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

G : (A : P → (Type ℓ))
  → (B : (P →ᴰ A) → Type ℓ)
  → {{BP⋆ : ∀ {a : P →ᴰ A} → P ⋆-Modal (B a)}}
  → Type ℓ
G {P = P} A B = Σ[ a ∈ P →ᴰ A ] B a

syntax G A (λ x → B) = G[ x ∈ A ] B

G-collapses : ∀ (p : P) (A : P → (Type ℓ)) (B : P →ᴰ A → Type ℓ)
  {{BP⋆ : ∀ {a : P →ᴰ A} → P ⋆-Modal (B a)}} → G[ a ∈ A ] B a ≡ A p
G-collapses p A B = {!   !}

instance
  [∣↪]-is-Ψ⋆-Modal : {x : P → M} → P ⋆-Modal [ M ∣ P ↪ x ]
  [∣↪]-is-Ψ⋆-Modal = {!   !}

  ⋆-is-⋆-Modal : P ⋆-Modal (P ⋆ M)
  ⋆-is-⋆-Modal = {!!}

  ×-is-⋆-Modal : {A B : Type ℓ}
    → {{_ : P ⋆-Modal A}} → {{_ : P ⋆-Modal B}} → P ⋆-Modal (A × B)
  ×-is-⋆-Modal = {!!}

