{-# OPTIONS --cubical #-}
module Models.Test where

open import Cubical.Core.Primitives
open import Cubical.Core.Glue

open import Data.Nat using (ℕ; zero; suc)

open import Realizability
open import Utils

data SConC : Set where
  ∙C : SConC
  _▷C : SConC → SConC

data STmC : SConC → Set where
  lamC : ∀ {ΓC} → STmC (ΓC ▷C) → STmC ΓC
  -- lamC[] : ∀ {ΓC ΔC t} {σ : SubC ΔC ΓC} → (lamC {ΓC} t) [ σ ]C ≡ lamC (t [ σ ⁺C ]C)

  appC : ∀ {ΓC} → STmC ΓC → STmC ΓC → STmC ΓC
  -- appC[] : ∀ {ΓC ΔC t u} {σ : SubC ΔC ΓC} → (appC {ΓC} t u) [ σ ]C ≡ appC (t [ σ ]C) (u [ σ ]C)
  
  -- Unit
  unit : ∀ {ΓC} → STmC ΓC
  -- unit[] : ∀ {ΓC ΔC} {σ : SubC ΔC ΓC} → (unit {ΓC}) [ σ ]C ≡ unit

  -- Natural numbers
  zeroC : ∀ {ΓC} → STmC ΓC
  -- zeroC[] : ∀ {ΓC ΔC σ} → (zeroC {ΓC}) [ σ ]C ≡ zeroC {ΔC}

  succC : ∀ {ΓC} → STmC ΓC → STmC ΓC
  -- succC[] : ∀ {ΓC ΔC t} {σ : SubC ΔC ΓC} → (succC {ΓC} t) [ σ ]C ≡ succC (t [ σ ]C)
  
  recC : ∀ {ΓC} → STmC ΓC → STmC (ΓC ▷C) → STmC ΓC → STmC ΓC
  -- recC[] : ∀ {ΓC ΔC z s n} {σ : SubC ΔC ΓC}
  --   → (recC {ΓC} z s n) [ σ ]C ≡ recC (z [ σ ]C) (s [ σ ⁺C ]C) (n [ σ ]C)
  
  qC : ∀ {ΓC} → STmC (ΓC ▷C)
  _[_]C : ∀ {ΓC} → STmC (ΓC ▷C) → STmC ΓC → STmC ΓC

  recC-η1 : ∀ {ΓC n} → recC {ΓC} zeroC (succC qC) n ≡ n
  recC-β-zero : ∀ {ΓC z s} → recC {ΓC} z s zeroC ≡ z
  recC-β-succ : ∀ {ΓC z s n} → recC {ΓC} z s (succC n) ≡ s [ recC z s n ]C
  
size : SConC → ℕ
size ∙C = zero
size (x ▷C) = suc (size x)

module _ (A : PCA) where
  open Realizability.Relations A public

  interp : ∀ {ΓC} → STmC ΓC → ∣ A [ size ΓC ]∣
  interp (lamC x) = {!   !}
  interp (appC x x₁) = {!   !}
  interp unit = {!   !}
  interp zeroC = {!   !}
  interp (succC x) = {!   !}
  interp (recC x x₁ x₂) = {!   !}
  interp qC = {!   !}
  interp (x [ x₁ ]C) = {!   !}
  interp (recC-η1 i) = {!   !}
  interp (recC-β-zero i) = {!   !}
  interp (recC-β-succ i) = {!   !}
