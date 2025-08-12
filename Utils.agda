module Utils where

postulate
  _~>_ : ∀ {i} {A B : Set i} → (a : A) → (b : B) → Set i

{-# BUILTIN REWRITE _~>_ #-}

-- Equality

infix 4 _＝_
data _＝_ {i} {A : Set i} : (a b : A) → Prop i where
  refl : ∀ {x} → x ＝ x

{-# BUILTIN REWRITE _＝_ #-}
  
postulate
  transport : ∀ {i j} {A : Set j} {x y} (P : A → Set i) → x ＝ y → P x → P y
  transport-id : ∀ {i} {A : Set i} {P : A → Set i} {x} {r : P x} → transport P refl r ~> x

  coe : ∀ {i} {A B : Set i} → A ＝ B → A → B
  coe-id : ∀ {i} {A} {x : A} → coe {i} {A} {A} refl x ~> x

{-# REWRITE transport-id #-}
{-# REWRITE coe-id #-}
  
infix 4 _＝[_]_
_＝[_]_ : ∀ {i} {A B : Set i} → A → A ＝ B → B → Prop i
x ＝[ p ] y = coe p x ＝ y

cong : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {a} {b} (p : a ＝ b) → f a ＝ f b
cong f refl = refl

congᴰ : ∀ {i j} {A : Set i} {B : A → Set j} (f : (a : A) → B a) {a} {b} (p : a ＝ b) → f a ＝[ cong B p ] f b
congᴰ f refl = refl

-- cong2ᴰ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : ∀ {a} → B a → Set k}
--   (f : (a : A) → (b : B a) → C b) {a a' b b'} (p : a ＝ a') (q : b ＝[ cong B p ] b') → f a b ＝[ cong {!   !} {!   !} ] f a' b'
-- cong2ᴰ f refl refl = refl

sym : ∀ {i} {A : Set i} {a b : A} → a ＝ b → b ＝ a
sym refl = refl

hsym : ∀ {i} {A : Set i} {a b : A} {p} → a ＝[ p ] b → b ＝[ sym p ] a
hsym refl = refl

trs :  ∀ {i} {A : Set i} {a b c : A} → a ＝ b → b ＝ c → a ＝ c
trs refl refl = refl

module ＝-Reasoning {A : Set} where
  infix  1 begin_
  infixr 2 step-＝-∣ step-＝-⟩
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ＝ y → x ＝ y
  begin x＝y  =  x＝y

  step-＝-∣ : ∀ (x : A) {y : A} → x ＝ y → x ＝ y
  step-＝-∣ x x＝y  =  x＝y

  step-＝-⟩ : ∀ (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
  step-＝-⟩ x y＝z x＝y = trs x＝y y＝z

  syntax step-＝-∣ x x＝y      =  x ＝⟨⟩ x＝y
  syntax step-＝-⟩ x y＝z x＝y  =  x ＝⟨  x＝y ⟩ y＝z

  _∎ : ∀ (x : A) → x ＝ x
  x ∎  =  refl

open ＝-Reasoning