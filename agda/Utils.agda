module Utils where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Nat hiding (_^_)
open import Level using (Level; _⊔_; suc)

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂; subst)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

variable
  ℓ ℓ' : Level

postulate
  funext : Extensionality ℓ ℓ'

{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡[_]_

coe : ∀ {A B : Set ℓ} (p : A ≡ B) → A → B
coe p = subst (λ s → s) p

_≡[_]_ : ∀ {A B : Set ℓ} (a : A) (p : A ≡ B) (b : B) → Set ℓ
_≡[_]_ {A} {B} a p b = coe p a ≡ b

pure : ∀ {A : Set} → A → Maybe A
pure = just

_^_ : (A : Set) → ℕ → Set
A ^ l = Vec A l
  
data _↓ {X : Set} : Maybe X → Set where
  def : ∀ x → (just x) ↓

_↓by_ : ∀ {X : Set} (x : Maybe X) → x ↓ → X
_↓by_ x (def y) = y

_↓* : ∀ {n} {X : Set} (x : Maybe X ^ n) → Set
_↓* = All (λ x → x ↓)

_↓*by_ : ∀ {n} {X : Set} (x : (Maybe X) ^ n) → x ↓* → X ^ n
[] ↓*by [] = []
(x ∷ xs) ↓*by (px ∷ ys) = x ↓by px ∷ (xs ↓*by ys)
  
def-id : ∀ {X : Set} {x : Maybe X} → (p : x ↓) → x ≡ just (x ↓by p)
def-id (def y) = refl
    
id-def : ∀ {X : Set} {x : Maybe X} {y : X} → (p : x ≡ just y) → x ↓
id-def {y = y} refl = def y