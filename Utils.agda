{-# OPTIONS --prop --rewriting #-}
module Utils where

infix 4 _≡_
data _≡_ {i} {A : Set i} : (a b : A) → Prop i where
  refl : ∀ {a} → a ≡ a
  
{-# BUILTIN REWRITE _≡_ #-}
  
postulate
  coe : {A B : Set} → A ≡ B → A → B
  coe-id : ∀ {A} {x : A} → coe {A} {A} refl x ≡ x
  {-# REWRITE coe-id #-}
  