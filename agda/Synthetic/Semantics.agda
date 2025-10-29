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

-- record Tyᴿ : Type1 where
--   field
--     irr : Type
--     irr-modal :  ⋆-Modal irr
--     rel : irr → [ Type ∣ Ψ ↪ Λ ]
--     sec : (a : irr) → Ψ ⋆ (rel a .fst)

--   bundle-collapses : (p : Ψ) → (Σ[ t ∈ irr ] rel t .fst) ≡ Λ p
--   bundle-collapses p =
--     let k = isoToPath (Σ-contractFstIso (collapses irr-modal p))
--     in  _∙_ k (rel (collapses irr-modal p .fst) .snd p) 

--   rel' : [ Type ∣ Ψ ↪ Λ ]
--   rel' =  ( Σ[ t ∈ irr ] rel t .fst) , bundle-collapses

-- open Tyᴿ

ms : OpTT-sorts {lzero} {lsuc lzero} {lzero}
ms .$ = Ψ
ms .Ty = [ Type ∣ Ψ ↪ Λ ]
ms .Tm z A = L → A .fst
ms .Tm ω A = A .fst
ms .Ex = Ψ →ᴰ Λ
[ ms ]' {A} x q = x

foo = funExt

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
⟨ mc ⟩ {z} {A~} x p q = ⊥-elim (disjoint p q)
⟨ mc ⟩ {ω} {A~} x p = give p Λ (A~ p) (x p)
mc .∣⟨⟩∣ {A~ = A~} {e} j p = give'-give p Λ (A~ p) (e p) j
mc .⟨∣∣⟩ {A~ = A~} {t~ = t~} j p = give-give' p Λ (A~ p) (t~ p) j
mc .[⟨⟩] {A~} {p = p} = propFunExt λ q → ⊥-elim (disjoint p q)
mc .∅ = id
mc .bind {X' = X'} f γ q = transport (λ i → X' (uneraseTms-id {q = q} {γ = γ} i) .fst) (f (uneraseTms q γ) q)
mc .bind[]-1 = {!   !}
mc .bind[]-2 = {!   !}
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
mc .lam {z} {i = z} = {! !}
-- mc .lam {ω} {A = A} {i = z} {X = X} f a =  A .sec a >>= (λ a' → f (a , a')) by  X a .irr-modal
-- mc .lam {z} {A = A} {i = ω} {X} f =  (λ a → f a .fst)
--   , (λ p →
--     let a' = nope' (A .irr-modal) p in
--     give' p Λ (rel' (X a')) (f a'))
--   -- ,  (λ a → X a .sec (f a .fst)) , {!!} -- doable
--   ,  ({!!}) , {!!} -- doable
-- mc .lam {ω} {A = A} {i = ω} {X = X} f = ( λ a → 
   
--    {!!}) , {!!}
--   -- , (λ p → lambda p (λ x → give' p Λ (rel' (X _)) (f (give p Λ (rel' A) x)) ))
--   -- , (λ {a} ar → X a .sec (f (a , A .sec a) .fst)) 
--   -- ,  λ p → {!!} -- doable
-- mc .app {z} {z} x a = x a
-- mc .app {z} {ω} x a = {! !}
-- mc .app {ω} {z} x a = x .fst a , x .snd .snd .fst a
-- mc .app {ω} {ω} x a = {! !}
-- mc .lam-app-z = refl
-- mc .app-lam-z = refl
-- mc .∣lam-ω∣ = {!   !}
-- mc .∣app-ω∣ = {!   !}
-- -- mc .∣lam-z∣ = {!   !}
-- -- mc .∣app-z∣ = {!   !}
-- mc .[lam] = {! refl  !}
-- -- mc .[app] = {!   !}
-- mc .Spec A x .irr = A .irr
-- mc .Spec A x .irr-modal = A .irr-modal
-- mc .Spec A x .rel t = G[ e ∈ Λ ] ([ A .rel t .fst ∣ p ∈ Ψ ↪ give p Λ (A .rel t) (e p) ] × Ψ ⋆ (x ≡ e))
--   ,  λ p →  G-collapses p _ _
-- mc .Spec A x .sec a = {!  !}
-- -- mc .specz = {!   !}
-- -- mc .spec = {!   !}
-- -- mc .unspec = {!   !}
-- -- mc .∣spec∣ = {!   !}
-- -- mc .∣unspec∣ = {!   !}
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
