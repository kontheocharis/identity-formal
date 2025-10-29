{-# OPTIONS --prop --cubical -WnoUnsupportedIndexedMatch #-}
module Synthetic.Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Data.Unit
open import Data.Empty
open import Agda.Primitive

open import Synthetic.Model
open import Synthetic.Utils
  
{-# BUILTIN REWRITE _≡_ #-}

-- We will define semantics for the synthetic model by working in the glued
-- topos Set ↓ <Γ , Id> . This can be emulated in Agda by postulates.

-- In particular, let Λ be the syntactic (initial) uni-typed CwF of lambda
-- calculus terms quotiented by βη. Its objects are natural numbers. We have the
-- presheaf category Psh(Λ) which is a topos, and contains a second-order model
-- of Λ which is the syntax. We can glue along the global sections functor Γ :
-- Psh(Λ) → Set to get a new topos Set ↓ Γ. However, instead we glue along
-- < Γ , Id > : Psh(Λ) × Set → Set which sends (X , A) to X × Γ(A). This
-- also gives us a "purely logical" projection free of any syntactic data.
-- We will use the left slot Psh(Λ) for the computational layer, and the
-- right slot Set for the logical layer. We postulate two propositions Ψ and L
-- in the internal language of Set ↓ < Γ , Id > which are disjoint, i.e., Ψ
-- ∧ L → ⊥. These correspond to the unique maps 0 → 0 × Γ(1) and 0 → 1 × Γ(0)
-- respectively.

private
  variable
    ℓ : Level

postulate
  Ψ : Prop
  L : Prop
  disjoint : Ψ → L → ⊥

●_ : Type ℓ → Type ℓ
● A = (L or Ψ) ⋆ A

nocompᴰ : ∀ {A : Ψ → Type ℓ} → (q : L) → (Ψ →ᴰ A)
nocompᴰ q = λ p → ⊥-elim (disjoint p q)

nocomp : ∀ {A : Type ℓ} → L → (Ψ → A)
nocomp q = λ p → ⊥-elim (disjoint p q)

Ψ-contr-under-L : ∀ {A : Ψ → Type ℓ} → L → isContr (Ψ →ᴰ A)
Ψ-contr-under-L q = nocompᴰ q ,  λ y → propFunExt (nocompᴰ q)

no-Ψ-glue-in-L : ∀ {A : Ψ → Type ℓ} {X : (Ψ →ᴰ A) → Type ℓ} {y : {a : Ψ →ᴰ A} → Ψ ⋆-Modal (X a)}
  → (q : L) → G A X {{y}} ≡ X (nocompᴰ q)
no-Ψ-glue-in-L q = isoToPath (Σ-contractFstIso (Ψ-contr-under-L q))
  
record LC : Set (lsuc ℓ) where
  field
    Λ : Type ℓ
    lambda : (f : Λ → Λ) → Λ
    apply : Λ → Λ → Λ
    beta : ∀ {f x} → apply (lambda f) x ≡ f x
    eta : ∀ {f} → lambda (λ x → apply f x) ≡ f
    
  zeroΛ : Λ
  zeroΛ = lambda (λ z → lambda (λ s → z))

  succΛ : Λ → Λ
  succΛ n = lambda (λ z → lambda (λ s → apply (apply n z) s))

  id : Λ
  id = lambda (λ x → x)

-- We have a Ψ →-modal model of Λ in the glued topos.
postulate
  LC-syntax : Ψ → LC {ℓ}
  
module _ (p : Ψ) where
  open LC {lzero} (LC-syntax p) public 
  
open OpTT
open OpTT-sorts
open OpTT-ctors

ms : OpTT-sorts {lzero} {lsuc lzero} {lzero}
ms .$ = Ψ
ms .Ty = [ Type ∣ Ψ ↪ Λ ]
ms .Tm z A = L → A .fst
ms .Tm ω A = A .fst
ms .Ex = Ψ →ᴰ Λ
[ ms ]' {A} x q = x

uneraseTms : ∀ {Δ} → L → Tms ms z Δ → Tms ms ω Δ
uneraseTms q ε = ε
uneraseTms q (_,_ {j = z} a γ) = (λ z₁ → a q) , uneraseTms q γ
uneraseTms q (_,_ {j = ω} a γ) = a q , uneraseTms q γ

uneraseTms-id : ∀ {Δ} {q : L} {γ : Tms ms z Δ} → [[_]] ms (uneraseTms q γ) ≡ γ
uneraseTms-id {q = q} {γ = ε} = refl
uneraseTms-id {q = q} {γ = _,_ {j = z} a γ} i = a , uneraseTms-id {q = q} {γ = γ} i
uneraseTms-id {q = q} {γ = _,_ {j = ω} a γ} i = a , uneraseTms-id {q = q} {γ = γ} i

mc : OpTT-ctors ms
∣ mc ∣ {A~ = A~} x p = give' p Λ (A~ p) (x p)
⟨ mc ⟩ {z} {A~} x p q = nocomp q p
⟨ mc ⟩ {ω} {A~} x p = give p Λ (A~ p) (x p)
mc .∣⟨⟩∣ {A~ = A~} {e} j p = give'-give p Λ (A~ p) (e p) j
mc .⟨∣∣⟩ {A~ = A~} {t~ = t~} j p = give-give' p Λ (A~ p) (t~ p) j
mc .[⟨⟩] {A~} {p = p} = propFunExt λ q → nocomp q p
mc .∅ = id
mc .bind {X' = X'} f γ q = transport (λ i → X' (uneraseTms-id {q = q} {γ = γ} i) .fst) (f (uneraseTms q γ) q)
mc .bind[]-1 = {!   !}  -- ok
mc .bind[]-2 = {!   !}  -- ok
mc .lm f p = lambda p (λ q → f (λ _ → q) p)
mc .ap x y p = apply p (x p) (y p)
mc .ze = zeroΛ
mc .su x p = succΛ p (x p)
-- mc .rec = λ z₁ z₂ z₃ → z₁
mc .Π z A X = G[ f ∈ Λ ]
  [ ((a : L → A .fst) → X a .fst)
    ∣ p ∈ Ψ ↪ (λ a → give p Λ (X a) (f p)) ]
  , λ p → G-collapses p _ _
mc .Π ω A X =  G[ f ∈ Λ ]
  [ ((a : A .fst) → X (λ _ → a) .fst)
    ∣ p ∈ Ψ ↪ (λ a → give p Λ (X (λ _ → a)) (apply p (f p) (give' p Λ A a))) ]
  , λ p → G-collapses p _ _
mc .lam {z} {i = z} f q = transport (sym (no-Ψ-glue-in-L {y = [∣↪]-is-Ψ⋆-Modal} q)) ((λ a → f a q) , nocompᴰ q) 
mc .lam {ω} {i = z} f q = transport (sym (no-Ψ-glue-in-L {y = [∣↪]-is-Ψ⋆-Modal} q)) ((λ a → f a q) , nocompᴰ q) 
mc .lam {z} {A = A} {i = ω} {X = X} f =
  (λ p → give' p Λ (X _) (f (λ q → nocomp q p)))
  , f
  ,  λ p → funExt λ a →  sym ({!!}) -- ok
mc .lam {ω} {A = A} {i = ω} {X = X} f =
  ( λ p →  lambda p (λ x → give' p Λ (X _) (f (give p Λ A x))))
  , f
  , {!!}  -- ok
mc .app {z} {z} f a q =  f q .snd .fst a
mc .app {z} {ω} f a q =  f q .snd .fst (a q) 
mc .app {ω} {z} (_ , f' , _) a = f' a
mc .app {ω} {ω} (_ , f' , _) a = f' a 
mc .lam-app-z = {! !} -- ok
mc .app-lam-z = {! !} -- ok
mc .∣lam-ω∣ = {!   !}
-- mc .∣app-ω∣ = {!   !}
-- -- mc .∣lam-z∣ = {!   !}
-- -- mc .∣app-z∣ = {!   !}
-- mc .[lam] = {! refl  !}
-- -- mc .[app] = {!   !}
mc .Spec A x = G[ y ∈ Λ ] ([ A .fst ∣ p ∈ Ψ ↪ give p Λ A (y p) ] × (● (x ≡ y))) , λ p → G-collapses p _ _ 
mc .specz t q = transport (sym (no-Ψ-glue-in-L {y = ×-is-⋆-Modal} q)) ((t q , nocompᴰ q) , nope (inl q))
mc .spec {A = A} {e = e} t prf = (λ p → give' p Λ A t) , ( t ,  λ p → sym (give-give' p Λ A t)) , η (sym prf)
mc .unspec {z} {A = A} {e} t q = t q .snd .fst .fst
mc .unspec {ω} {A = A} {e} t = t .snd .fst .fst
mc .∣spec∣ = {!   !} -- ok
mc .∣unspec∣ {e} {A~} {t~} = {! !} -- ok
-- -- mc .[spec] = {!   !}
-- -- mc .[unspec] = {!   !}
-- -- mc .Nat = {!   !}
-- -- mc .zero = {!   !}
-- -- mc .succ = {!   !}
-- -- mc .elim-Nat = {!   !}
-- -- mc .elim-Nat-zero-z = {!   !}
-- -- mc .elim-Nat-succ-z = {!   !}
-- -- mc .∣zero∣ = {!   !}
-- -- mc .∣succ∣ = {!   !}
-- -- mc .∣elim-Nat-ω∣ = {!   !}
-- -- mc .[zero] = {!   !}
-- -- mc .[succ] = {!   !}
-- -- mc .[elim-Nat] = {!   !}
-- -- mc .Num = {!   !}
-- -- mc .nat-num = {!   !}
-- -- mc .rec-η-1 = {!   !}
-- -- mc .rec-η-2 = {!   !}

  
-- m : OpTT {lzero} {lsuc lzero} {lzero}
-- m .sorts = ms
-- m .ctors = mc
