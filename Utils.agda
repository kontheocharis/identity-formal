{-# OPTIONS --prop --rewriting #-}
module Utils where

infix 4 _≡_
data _≡_ {i} {A : Set i} : (a b : A) → Prop i where
  refl : ∀ {a} → a ≡ a
  
{-# BUILTIN REWRITE _≡_ #-}
  
postulate
  coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
  coe-id : ∀ {i} {A} {x : A} → coe {i} {A} {A} refl x ≡ x
  {-# REWRITE coe-id #-}
  
infix 4 _≡[_]_
_≡[_]_ : ∀ {i} {A B : Set i} → A → A ≡ B → B → Prop i
x ≡[ p ] y = coe p x ≡ y

cong : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {a} {b} (p : a ≡ b) → f a ≡ f b
cong f refl = refl