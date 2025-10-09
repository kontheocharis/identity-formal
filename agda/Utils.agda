module Utils where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Nat hiding (_^_)

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂; subst)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

postulate
  funext : ∀ {i j} → Extensionality i j

{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡[_]_

_≡[_]_ : ∀ {i} {A B : Set i} (a : A) (p : A ≡ B) (b : B) → Set i
_≡[_]_ {i} {A} {B} a p b = subst (λ s → s) p a ≡ b

coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
coe p a = subst (λ s → s) p a

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