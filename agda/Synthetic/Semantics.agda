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

postulate
  Ψ : Prop
  L : Prop
  disjoint : Ψ → L → ⊥
  
variable
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

Ψ⇒_ : Type ℓ → Type ℓ
Ψ⇒_ M = (p : Ψ) → M

L⇒_ : Type ℓ → Type ℓ
L⇒_ M = (p : L) → M

data _⋆_ (P : Prop) (M : Type ℓ) : Type ℓ where
  nope : (p : P) → P ⋆ M
  η : M → P ⋆ M
  trivial : (p : P) {x : M} → nope p ≡ η x

Ψ*_ : Type ℓ → Type ℓ
Ψ* M = Ψ ⋆ M

L*_ : Type ℓ → Type ℓ
L* M = L ⋆ M

*-collapses : (p : P) (y : P ⋆ M) → nope p ≡ y
*-collapses p (nope p) = refl
*-collapses p (η x) = trivial p
*-collapses p (trivial p {x = x} i) j = trivial p {x = x} (i ∧ j)

Ψ*Ψ⇒-trivial : P → (P ⋆ M) ≃ ⊤
Ψ*Ψ⇒-trivial p .fst x = tt
Ψ*Ψ⇒-trivial p .snd .equiv-proof tt = (nope p , refl) , λ (y , _) i → ( *-collapses p y i) , refl

record Ψ*-Modal (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = Ψ true × M} {B = Ψ true} (λ (p , _) → p)

  collapses : Ψ → isContr M
  collapses p = invIsEq prf [ p ] .snd
    ,  λ m →  λ i → retIsEq prf ([ p ] , m) i .snd

  nope' : (p : Ψ) → M
  nope' p = invIsEq prf [ p ] .snd

  trivial' : (p : Ψ) {x : M} → nope' p ≡ x
  trivial' p {x = x} = collapses p .snd x

open Ψ*-Modal

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
G-collapses p A B = {!   !}

instance
  [_∣Ψ↪_]-is-Ψ*-Modal : {x : Ψ⇒ M} → Ψ*-Modal [ M ∣ Ψ ↪ x ]
  [_∣Ψ↪_]-is-Ψ*-Modal = {!   !}

  Ψ*-is-Ψ*-Modal : Ψ*-Modal (Ψ* M)
  Ψ*-is-Ψ*-Modal = {!!}

  ×-is-Ψ*-Modal : {A B : Type ℓ}
    → {{_ : Ψ*-Modal A}} → {{_ : Ψ*-Modal B}} → Ψ*-Modal (A × B)

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

  id : TmΛ
  id = lambda (λ x → x)

-- We have a Ψ⇒-modal model of Λ in the glued topos.
postulate
  Λm : Ψ⇒ Λ {ℓ}
  
module _ (p : Ψ) where
  open Λ {lzero} (Λm p) public 
  
open OpTT
open OpTT-sorts
open OpTT-ctors

record Tyᴿ : Type1 where
  field
    irr : Type
    irr-modal : Ψ*-Modal irr
    rel : irr → [ Type ∣ Ψ ↪ TmΛ ]
    sec : (a : irr) → Ψ* (rel a .fst)

  bundle-collapses : (p : Ψ) → (Σ[ t ∈ irr ] rel t .fst) ≡ TmΛ p
  bundle-collapses p =
    let k = isoToPath (Σ-contractFstIso (collapses irr-modal p))
    in  _∙_ k (rel (collapses irr-modal p .fst) .snd p) 

  rel' : [ Type ∣ Ψ ↪ TmΛ ]
  rel' =  ( Σ[ t ∈ irr ] rel t .fst) , bundle-collapses

open Tyᴿ

ms : OpTT-sorts {lzero} {lsuc lzero} {lzero}
ms .$ = Ψ
ms .Ty = Tyᴿ
ms .Tm z A = A .irr
ms .Tm ω A = rel' A .fst
ms .Ex = Ψ⇒ᴰ TmΛ
[ ms ]' {A} x = x .fst

-- _>>=_ : Ψ* A → (A → Ψ* B) → Ψ* B
-- nope p >>= f = nope p
-- η x >>= f = f x
-- _>>=_ {B = B} (trivial p {x = x} i) f = *-collapses {M = B} p (f x) i

_>>=_by_ : Ψ* M → (M → N) → Ψ*-Modal N → N
nope p >>= f by m = nope' m p
η x >>= f by m = f x
_>>=_by_ {N = N} (trivial p {x = x} i) f m = trivial' {M = N} m p {x = f x} i  

mc : OpTT-ctors ms
∣ mc ∣ {A~ = A~} x p = give' p TmΛ (rel' (A~ p)) (x p)
⟨ mc ⟩ {z} {A~} x p =  nope' (A~ p .irr-modal) p  
⟨ mc ⟩ {ω} {A~} x p = give p TmΛ (rel' (A~ p)) (x p)
mc .∣⟨⟩∣ {A~ = A~} {e} j p = give'-give p TmΛ (rel' (A~ p)) (e p) j
mc .⟨∣∣⟩ {A~ = A~} {t~ = t~} j p = give-give' p TmΛ (rel' (A~ p)) (t~ p) j
mc .[⟨⟩] {A~} {p = p} = sym (trivial' (A~ p .irr-modal) p) 
mc .∅ = id
-- mc .bind x ε = x ε
-- mc .bind x (nope p , γ) = nope p
-- mc .bind x (η x₁ , γ) = {!   !}
-- mc .bind x (trivial p i , γ) = {!   !}
-- mc .bind[]-1 = {!   !}
-- mc .bind[]-2 = {!   !}
mc .lm f p = lambda p (λ q → f (λ _ → q) p)
mc .ap x y p = apply p (x p) (y p)
mc .ze = zeroΛ
mc .su x p = succΛ p (x p)
mc .rec = λ z₁ z₂ z₃ → z₁
mc .Π z A X .irr = (a : A .irr) → X a .irr
mc .Π z A X .rel f = G[ fΛ ∈ TmΛ ]
      [ ((a : A .irr) → X a .rel (f a) .fst)
        ∣ p ∈ Ψ ↪ (λ a → give p TmΛ (X a .rel (f a)) (fΛ p)) ]
      ,  λ p → G-collapses p _ _
mc .Π z A X .irr-modal .prf .equiv-proof y = {!  !}
-- mc .Π z A X .sec f
--   = ((λ p → 
--       let a = nope' (A .irr-modal) p in
--       give' p TmΛ (X a .rel (f a)) (X a .sec (f a)))
--     , (λ a → X a .sec (f a)) , λ p → funExt λ a →
--       let a' = nope' (A .irr-modal) p in
--       subst (λ a → X a .sec (f a) ≡ give p TmΛ (X a .rel (f a)) _)
--         (trivial' (A .irr-modal) p {x = a})
--         (sym (give-give' p TmΛ (X a' .rel (f a')) _)))
mc .Π ω A X .irr =  (a : A .irr) → X a .irr
mc .Π ω A X .rel f = G[ fΛ ∈ TmΛ ]
      [ ( ∀ {a : A .irr} (ar : A .rel a .fst) →  X a .rel (f a) .fst)
        ∣ p ∈ Ψ ↪ (λ {a} ar → give p TmΛ (X a .rel (f a))
        (apply p (fΛ p) (give' p TmΛ ( A .rel a) ar))) ]
      ,  λ p → G-collapses p _ _
mc .Π ω A X .irr-modal .prf .equiv-proof y = {!  !}
-- mc .Π ω A X .sec f
--   = (λ p →
--       let a = nope' (A .irr-modal) p in
--        lambda p (λ x →  give' p TmΛ (X a .rel (f a)) (X a .sec (f a))))
--     ,  (λ {a} ar → X a .sec (f a)) ,  λ p → implicitFunExt λ {a} → funExt λ ar →
--       let a' = nope' (A .irr-modal) p in
--       {!!} -- doable
--        -- subst (λ aa → X aa .sec (f aa) ≡ give p TmΛ (X aa .rel (f aa))
--        --    (Λ.apply (Λm _)
--        --          (Λ.lambda (Λm _)
--        --            (λ x →
--        --              give' _ (λ p₁ → Λ.TmΛ (Λm _)) (X a' .rel (f a'))
--        --              (X a' .sec (f a'))))
--        --          (give' _ (λ p₁ → Λ.TmΛ (Λm _)) (A .rel a) ar))
--        --  ) {!!} {!!} 
mc .lam {z} {i = z} f = f
mc .lam {ω} {A = A} {i = z} {X = X} f a =  A .sec a >>= (λ a' → f (a , a')) by  X a .irr-modal
mc .lam {z} {A = A} {i = ω} {X} f =  (λ a → f a .fst)
  , (λ p →
    let a' = nope' (A .irr-modal) p in
    give' p TmΛ (rel' (X a')) (f a'))
  -- ,  (λ a → X a .sec (f a .fst)) , {!!} -- doable
  ,  ({!!}) , {!!} -- doable
mc .lam {ω} {A = A} {i = ω} {X = X} f = ( λ a → 
   
   {!!}) , {!!}
  -- , (λ p → lambda p (λ x → give' p TmΛ (rel' (X _)) (f (give p TmΛ (rel' A) x)) ))
  -- , (λ {a} ar → X a .sec (f (a , A .sec a) .fst)) 
  -- ,  λ p → {!!} -- doable
mc .app {z} {z} x a = x a
mc .app {z} {ω} x a = {! !}
mc .app {ω} {z} x a = x .fst a , x .snd .snd .fst a
mc .app {ω} {ω} x a = {! !}
mc .lam-app-z = refl
mc .app-lam-z = refl
mc .∣lam-ω∣ = {!   !}
mc .∣app-ω∣ = {!   !}
-- mc .∣lam-z∣ = {!   !}
-- mc .∣app-z∣ = {!   !}
mc .[lam] = {! refl  !}
-- mc .[app] = {!   !}
mc .Spec A x .irr = A .irr
mc .Spec A x .irr-modal = A .irr-modal
mc .Spec A x .rel t = G[ e ∈ TmΛ ] ([ A .rel t .fst ∣ p ∈ Ψ ↪ give p TmΛ (A .rel t) (e p) ] × Ψ* (x ≡ e))
  ,  λ p →  G-collapses p _ _
mc .Spec A x .sec a = {!  !}
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
