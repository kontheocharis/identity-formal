{-# OPTIONS --prop --cubical -WnoUnsupportedIndexedMatch #-}
module Synthetic.Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Data.Unit
open import Agda.Primitive

open import Synthetic.Model
  
{-# BUILTIN REWRITE _≡_ #-}

-- We will define semantics for the synthetic model by working in a glued topos.
-- This can be emulated in Agda by postulates.

-- In particular, let Λ be the syntactic (initial) uni-typed CwF of lambda
-- calculus terms quotiented by βη. Its objects are natural numbers. We have the
-- presheaf category Psh(Λ) which is a topos, and contains a second-order model
-- of Λ which is the syntax.

-- At the same time, there is the category of Λ-sets (Λ-Set). This is the
-- category of assemblies over the PCA defined by closed Λ terms. It can be
-- extended to the realizability topos RT(Λ).

-- Our first goal is to find a functor G : Psh(Λ) → RT(Λ) to glue along.
--
-- In fact, it suffices to find a functor g : Λ → Λ-Set, which we can extend to
-- G = i ∘ g! by universal property of Psh(Λ) and inclusion i : Λ-Set → RT(Λ).
--
-- To do this, we map each object n of Λ to the assembly g(n) whose underlying
-- set is the n-fold product of closed Λ terms, and whose n-fold realizability
-- relation is given by the identity. For a morphism f : n → m in Λ, which is m
-- lambda terms with n free variables each, we define g(f) to be the function
-- which maps a tuple of n closed terms to the tuple of m closed terms given by
-- n-currying f pointwise, tracked by f itself. Compositions and identities are
-- respected. Additionally, finite limits are preserved.

-- Once we do all this, we are awarded with a second-order model of Λ in
-- RT(Λ). (?)

-- Therefore, the gluing category is RT(Λ) ↓ G, which is again a topos.
-- We can use this as a semantics for code extraction.

postulate
  Ψ : Prop
  
variable
  M N : Type ℓ
  
record _true (P : Prop) : Type where
  constructor [_]
  field
    fact : P

◯ : Type ℓ → Type ℓ
◯ M = {{_ : Ψ}} → M

data ● (M : Type ℓ) : Type ℓ where
  * : {{_ : Ψ}} → ● M
  η : M → ● M
  trivial : {{p : Ψ}} {x : M} → * ≡ η x

*-collapses : {{_ : Ψ}} {y : ● M} → * ≡ y
*-collapses {y = *} = refl
*-collapses {y = η x} = trivial
*-collapses {y = trivial {x = x} i} j = trivial {x = x} (i ∧ j)

●◯-trivial : ◯ (● M) ≃ ⊤
●◯-trivial .fst x = tt
●◯-trivial .snd .equiv-proof tt = (* , refl) , λ (y , p) i → *-collapses {y = y} i , refl

record ●-Modal (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = Ψ true × M} {B = Ψ true} (λ (p , _) → p)

record ◯-Modal (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = M} {B = {{_ : Ψ}} → M} (λ x → x)

◯ᴰ : ◯ (Type ℓ) → Type ℓ
◯ᴰ A = {{_ : Ψ}} → A

[_∣_↪_] : (A : Type ℓ) → (P : Prop) → ({{_ : P}} → A) → Type ℓ
[ M ∣ P ↪ x ] = Σ[ a ∈ M ] ({{_ : P}} → a ≡ x)

give : ∀ {P} {{_ : P}} A → (M : [ Type ℓ ∣ P ↪ A ]) → A → M .fst
give _ (M , p) a = transport (sym p) a

give' : ∀ {P} {{_ : P}} A → (M : [ Type ℓ ∣ P ↪ A ]) → M .fst → A
give' _ (M , p) a = transport p a

G : (A : ◯ (Type ℓ))
  → (B : ◯ᴰ A → Type ℓ)
  → {{B● : ∀ {a : ◯ᴰ A} → ●-Modal (B a)}}
  → Type ℓ
G A B = Σ[ a ∈ ◯ᴰ A ] B a

syntax G A (λ x → B) = G[ x ∈ A ] B

G-collapses : ∀ {{_ : Ψ}} (A : ◯ (Type ℓ)) (B : ◯ᴰ A → Type ℓ)
  {{B● : ∀ {a : ◯ᴰ A} → ●-Modal (B a)}} → G[ a ∈ A ] B a ≡ A
G-collapses A B = {!   !}

instance
  [_∣Ψ↪_]-is-●-Modal : {A : Type ℓ} → {x : ◯ A} → ●-Modal [ A ∣ Ψ ↪ x ]
  [_∣Ψ↪_]-is-●-Modal = {!   !}
  
open OpTT
open OpTT-sorts
open OpTT-ctors

ms : OpTT-sorts {lzero} {lsuc lzero} {lzero}
ms .$ = {!   !}
ms .Ty = {!   !}
ms .Tm = {!   !}
ms .Ex = {!   !}
[ ms ]' = {!   !}

mc : OpTT-ctors ms

  
m : OpTT {lzero} {lsuc lzero} {lzero}
m .sorts = ms
m .ctors = mc