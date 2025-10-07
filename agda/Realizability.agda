{-# OPTIONS --allow-unsolved-metas #-}
module Realizability where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂; subst)

open import Utils

record PAS : Set1 where
  field
    ∣_∣ : Set
    _∙_ : ∣_∣ → ∣_∣ → Maybe ∣_∣
    S K : ∣_∣
    
module PASUtils (A : PAS) where
  open PAS A

  _↓∙_by_ : ∀ (x : Maybe ∣_∣) → ∣_∣ → x ↓ → Maybe ∣_∣
  _↓∙_by_ x y p = (x ↓by p) ∙ y

  _?∙?_ : ∀ (x y : Maybe ∣_∣) → Maybe ∣_∣
  _?∙?_ (just x) (just y) = x ∙ y
  _?∙?_ _ _ = nothing
  
  ?∙?-def : ∀ {x y} → (x↓ : x ↓) → (y↓ : y ↓) → (x ?∙? y) ≡ ((x ↓by x↓) ∙ (y ↓by y↓))
  ?∙?-def (def x) (def y) = refl

record PCA : Set1 where
  field
    pas : PAS
  open PAS pas public
  open PASUtils pas
  field
    Kx-def : ∀ {x} → (K ∙ x) ↓
    Kxy-id : ∀ {x y} → ((K ∙ x) ↓∙ y by Kx-def) ≡ just x

    Sx-def : ∀ {x} → (S ∙ x) ↓
    Sxy-def : ∀ {x y} → ((S ∙ x) ↓∙ y by Sx-def) ↓
    Sxyz-id : ∀ {x y z} → (((S ∙ x) ↓∙ y by Sx-def) ↓∙ z by Sxy-def) ≡ ((x ∙ z) ?∙? (y ∙ z))

variable
  A : PCA
  m n : ℕ
  
module PCATerms where
  open PCA
      
  data ∣_[_]∣ (A : PCA) : ℕ → Set where
    v : Fin n → ∣ A [ n ]∣
    ⌜_⌝ : ∣ A ∣ → ∣ A [ n ]∣
    _∙'_ : ∣ A [ n ]∣ → ∣ A [ n ]∣ → ∣ A [ n ]∣
  
  ∣_[_]∣^_ : (A : PCA) → ℕ → ℕ → Set
  ∣ A [ k ]∣^ l = Vec ∣ A [ k ]∣ l

  ∣_∣^_ : (A : PCA) → ℕ → Set
  ∣ A ∣^ l = Vec ∣ A ∣ l
  
  ∣_∣? : (A : PCA) → Set
  ∣ A ∣? = Maybe ∣ A ∣

  ∣_∣?^_ : (A : PCA) → ℕ → Set
  ∣ A ∣?^ l = Vec ∣ A ∣? l
  
module PCAUtils (A : PCA) where
  open PCATerms
  open PASUtils (A .PCA.pas) public
  open PCA A public
  
  eval : ∣ A [ n ]∣ → ∣ A ∣^ n → ∣ A ∣?
  eval (v x) σ = just (Data.Vec.lookup σ x)
  eval (⌜ x ⌝) σ = just x
  eval (a ∙' b) σ = do
    a' ← eval a σ
    b' ← eval b σ
    a' ∙ b'
  
  wk : {n : ℕ} → ∣ A [ n ]∣ → ∣ A [ suc n ]∣
  wk (v x) = v (suc x)
  wk (⌜ x ⌝) = ⌜ x ⌝
  wk (a ∙' b) = (wk a) ∙' (wk b)
  
  extract : ∣ A [ zero ]∣ → ∣ A ∣?
  extract m = eval m []
  
  extract* : ∀ {n} → ∣ A [ zero ]∣^ n → ∣ A ∣?^ n
  extract* m = Data.Vec.map (λ x → eval x []) m

  opn : ∣ A [ zero ]∣ → ∣ A [ n ]∣
  opn ⌜ x ⌝ = ⌜ x ⌝
  opn (y ∙' y₁) = opn y ∙' opn y₁
  
  eval-opn : ∀ {n σ} x → eval {n} (opn x) σ ≡ eval x []
  eval-opn ⌜ x ⌝ = refl
  eval-opn (x ∙' x₁) = cong₂ _>>=_ (eval-opn x) (funext λ a → cong₂ _>>=_ (eval-opn x₁) refl)
  {-# REWRITE eval-opn #-}
  
  _∙*_ : ∀ {n} → ∣ A [ n ]∣^ m → ∣ A ∣^ n → ∣ A ∣?^ m
  _∙*_ {zero} xs ys = []
  _∙*_ {suc n} (x ∷ xs) ys = eval x ys ∷ xs ∙* ys
  
  I : ∣_∣
  I = ((S ∙ K) ↓∙ K by Sx-def) ↓by Sxy-def

  Λ' : ∣ A [ suc n ]∣ → ∣ A [ n ]∣
  Λ' (v zero) = ⌜ I ⌝
  Λ' (v (suc x)) = ⌜ K ⌝ ∙' v x
  Λ' ⌜ x ⌝ = ⌜ (K ∙ x) ↓by Kx-def ⌝
  Λ' (t ∙' t') = (⌜ S ⌝ ∙' Λ' t) ∙' Λ' t'
  
  >>=-just : ∀ {X Y : Set} {a : Maybe X} {a' : X} {b : X → Maybe Y} {b' : Y}
    → (a ≡ just a') → (b a' ≡ just b')
    → ((a >>= b) ≡ just b')
  >>=-just refl p = p
  
  -- Functional completeness:
  Λ'-def : (x : ∣ A [ 1 ]∣) → (extract (Λ' x)) ↓
  Λ'-def (v zero) = def I
  Λ'-def (⌜ x ⌝) = def ((K ∙ x) ↓by Kx-def)
  Λ'-def (x ∙' y) =
    let x-def = def-id (Λ'-def x) in
    let y-def = def-id (Λ'-def y) in
    id-def (>>=-just (cong₂ _>>=_ x-def (funext (λ y → def-id Sx-def)))
      (>>=-just y-def (def-id Sxy-def)))
      
  Λ : ∣ A [ 1 ]∣ → ∣_∣
  Λ x = (extract (Λ' x)) ↓by (Λ'-def x)
  
  β : ∀ {x y} → eval (⌜ Λ x ⌝ ∙' ⌜ y ⌝) [] ≡ eval x (y ∷ [])
  β {v zero} {y} = trans Sxyz-id (trans (?∙?-def Kx-def Kx-def) Kxy-id)
  β {⌜ x ⌝} {y} = Kxy-id
  β {x ∙' x₁} {y} = {!   !}

  pair' : ∣ A [ n ]∣ → ∣ A [ n ]∣ → ∣ A [ n ]∣
  pair' x y = Λ' ((v zero ∙' wk x) ∙' wk y)

  pair : ∣_∣ → ∣_∣ → ∣_∣
  pair a b = (extract (pair' ⌜ a ⌝ ⌜ b ⌝)) ↓by (Λ'-def ((v zero ∙' wk ⌜ a ⌝) ∙' wk ⌜ b ⌝))
  

module Relations (A : PCA) where
  open PCA public
  open PCATerms public
  open PCAUtils A public

  RRel : (n : ℕ) → Set → Set1
  RRel n X = ∣ A ∣^ n → X → Set
  
  _⊩[_]_ : ∀ {X n} (a : ∣ A ∣^ n) (R : RRel n X) (x : X) → Set
  a ⊩[ R ] x = R a x
  
  _!⊩[_]_ : ∀ {X n} (a : ∣ A ∣?^ n) (R : RRel n X) (x : X) → Set
  a !⊩[ R ] x = ∃[ a↓ ] R (a ↓*by a↓) x
  
  transp-⊩ : ∀ {n X} {R : RRel n X} {a a' x} → (a ⊩[ R ] x) → (a ≡ a') → (a' ⊩[ R ] x)
  transp-⊩ t refl = t
  
  Total : ∀ {X n} → RRel n X → Set
  Total {X} {n} R = (x : X) → ∃[ a ] (R a x)
  
  TrackedAt : ∀ {X : Set} {Y : X → Set} {n} {m} (fR : ∣ A [ n ]∣^ m) (x : X) (y : Y x)
    (RX : RRel n X) (RY : (x : X) → RRel m (Y x)) → Set
  TrackedAt {X} {Y} {n} fR x y RX RY = (a : ∣ A ∣^ n) → a ⊩[ RX ] x → (fR ∙* a) !⊩[ RY x ] y
  
  Tracked : ∀ {X : Set} {Y : X → Set} {n m} (f : (x : X) → Y x)
      (fR : ∣ A [ n ]∣^ m) (RX : RRel n X) (RY : (x : X) → RRel m (Y x)) → Set
  Tracked {X} {Y} {n} {m} f fR RX RY = (x : X) → TrackedAt fR x (f x) RX RY
  
  ∃Tracked : ∀ {X : Set} {Y : X → Set} {n m} (f : (x : X) → Y x) (RX : RRel n X) (RY : (x : X) → RRel m (Y x)) → Set
  ∃Tracked {X} {Y} {n} {m} f RX RY = ∃[ fR ] Tracked f fR RX RY