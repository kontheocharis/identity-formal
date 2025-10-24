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

Ψ⇒_ : Type ℓ → Type ℓ
Ψ⇒_ M = {{p : Ψ}} → M

data Ψ*_ (M : Type ℓ) : Type ℓ where
  nope : {{_ : Ψ}} → Ψ* M
  η : M → Ψ* M
  trivial : {{p : Ψ}} {x : M} → nope ≡ η x

*-collapses : {{_ : Ψ}} {y : Ψ* M} → nope ≡ y
*-collapses {y = nope} = refl
*-collapses {y = η x} = trivial
*-collapses {y = trivial {x = x} i} j = trivial {x = x} (i ∧ j)

Ψ*Ψ⇒-trivial : Ψ⇒ (Ψ* M) ≃ ⊤
Ψ*Ψ⇒-trivial .fst x = tt
Ψ*Ψ⇒-trivial .snd .equiv-proof tt = (nope , refl) , λ (y , p) i → *-collapses {y = y} i , refl

record Ψ*-Modal (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = Ψ true × M} {B = Ψ true} (λ (p , _) → p)

record Ψ⇒-Modal (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = M} {B = {{p : Ψ}} → M} (λ x → x)

Ψ⇒ᴰ_ : Ψ⇒ (Type ℓ) → Type ℓ
Ψ⇒ᴰ_ A = {{p : Ψ}} → A

[_∣_↪_] : (A : Type ℓ) → (P : Prop) → ({{_ : P}} → A) → Type ℓ
[ M ∣ P ↪ x ] = Σ[ a ∈ M ] ({{_ : P}} → a ≡ x)

give : ∀ {P} {{p : P}} A → (M : [ Type ℓ ∣ P ↪ A ]) → A → M .fst
give _ (M , p) a = transport (sym p) a

give' : ∀ {P} {{p : P}} A → (M : [ Type ℓ ∣ P ↪ A ]) → M .fst → A
give' _ (M , p) a = transport p a

G : (A : Ψ⇒ (Type ℓ))
  → (B : Ψ⇒ᴰ A → Type ℓ)
  → {{BΨ* : ∀ {a : Ψ⇒ᴰ A} → Ψ*-Modal (B a)}}
  → Type ℓ
G A B = Σ[ a ∈ Ψ⇒ᴰ A ] B a

syntax G A (λ x → B) = G[ x ∈ A ] B

G-collapses : ∀ {{p : Ψ}} (A : Ψ⇒ (Type ℓ)) (B : Ψ⇒ᴰ A → Type ℓ)
  {{BΨ* : ∀ {a : Ψ⇒ᴰ A} → Ψ*-Modal (B a)}} → G[ a ∈ A ] B a ≡ A
G-collapses A B = {!   !}

instance
  [_∣Ψ↪_]-is-Ψ*-Modal : {x : Ψ⇒ M} → Ψ*-Modal [ M ∣ Ψ ↪ x ]
  [_∣Ψ↪_]-is-Ψ*-Modal = {!   !}

  Ψ*-is-Ψ*-Modal : Ψ*-Modal (Ψ* M)
  

record Λ : Set (lsuc ℓ) where
  field
    Tm : Type ℓ
    lambda : (f : Tm → Tm) → Tm
    apply : Tm → Tm → Tm
    beta : ∀ {f x} → apply (lambda f) x ≡ f x
    eta : ∀ {f} → lambda (λ x → apply f x) ≡ f

-- We have a Ψ⇒-modal model of Λ in the glued topos.
postulate
  Λm : Ψ⇒ Λ {ℓ}
  
open Λ
open OpTT
open OpTT-sorts
open OpTT-ctors

ms : OpTT-sorts {lzero} {lsuc lzero} {lzero}
ms .$ = Ψ
ms .Ty = [ Type ∣ Ψ ↪ (Λm .Tm) ]
ms .Tm z A = [ A .fst ∣ Ψ ↪ transport (sym (A .snd)) (Λm .lambda (λ y → y)) ]
ms .Tm ω A = G[ x ∈ Λm .Tm ] [ A .fst ∣ Ψ ↪ transport (sym (A .snd)) x ]
ms .Ex = Ψ⇒ᴰ Λm .Tm
[ ms ]' = {!   !} -- (tΛ , t0) = {!   !}

mc : OpTT-ctors ms
-- ∣ mc ∣ {z} x = Λm .lambda λ z₁ → z₁
-- ∣ mc ∣ {ω} x ⦃ p ⦄ = x p .fst
-- ⟨ mc ⟩ {z} x p = nope {{p}}
-- ⟨ mc ⟩ {ω} x p = x , nope {{p}}
-- mc .∣⟨⟩∣ {z} {e = e} = {!   !}
-- mc .∣⟨⟩∣ {ω} = refl
-- mc .⟨∣∣⟩ = {!  i !}
-- mc .∅ = Λm .lambda λ z₁ → z₁
-- mc .∣z∣ = refl
-- mc .bind = {!   !}
-- mc .bind[]-1 = {!   !}
-- mc .bind[]-2 = {!   !}
-- mc .lm = {!   !}
-- mc .ap = {!   !}
-- mc .ze = {!   !}
-- mc .su = {!   !}
-- mc .rec = {!   !}
-- mc .Π = {!   !}
-- mc .lam = {!   !}
-- mc .app = {!   !}
-- mc .lam-app-z = {!   !}
-- mc .app-lam-z = {!   !}
-- mc .∣lam-ω∣ = {!   !}
-- mc .∣app-ω∣ = {!   !}
-- mc .∣lam-z∣ = {!   !}
-- mc .∣app-z∣ = {!   !}
-- mc .[lam] = {!   !}
-- mc .[app] = {!   !}
-- mc .OpTT-ctors.* = {!   !}
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