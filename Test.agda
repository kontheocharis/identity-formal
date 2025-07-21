{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Foo : Set1 where
  field
    A : Set
    a : A
    b : A
  
open Foo 

postulate
  F : Foo
  boo : F .a ≡ F .b
  
{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE boo #-}

f : F .a ≡ F .b
f = refl