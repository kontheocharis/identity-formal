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

cong2 : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (f : A → B → C) {a b c d} (p : a ≡ c) (q : b ≡ d) → f a b ≡ f c d
cong2 f refl refl = refl

sym : ∀ {i} {A : Set i} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

hsym : ∀ {i} {A : Set i} {a b : A} {p} → a ≡[ p ] b → b ≡[ sym p ] a
hsym refl = refl

trs :  ∀ {i} {A : Set i} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trs refl refl = refl