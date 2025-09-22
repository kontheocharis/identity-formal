module CTT.Normal where

open import Data.Bool
open import CTT.Theory
open import Utils
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (cong to cong'; sym to sym')

open Relation.Binary.PropositionalEquality.≡-Reasoning

open CTT.Theory.Model syn

data CNf : (CΓ : CCon) → CTm CΓ → Set
data CNe : (CΓ : CCon) → CTm CΓ → Set
data CVar : (CΓ : CCon) → CTm CΓ → Set

coerce : ∀ {i} {A B : Set i} → A ≡ B → A → B
coerce refl a = a

infix 4 _≡[_]_
_≡[_]_ : ∀ {i} {A B : Set i} → A → A ≡ B → B → Set i
x ≡[ p ] y = coerce p x ≡ y

data CVar where
  vz : CVar (CΓ ▷) q
  vs : CVar CΓ Ca → CVar (CΓ ▷) (Ca [ p ])

data CNf where
  nlam : CNf (CΓ ▷) Ca → CNf CΓ (lam Ca)
  ne : CNe CΓ Ca → CNf CΓ Ca
  
data CNe where
  napp : CNe CΓ Ca → CNf CΓ Cb → CNe CΓ (app Ca [ < Cb > ])
  nvar : CVar CΓ Ca → CNe CΓ Ca
  
np : CNe CΓ Ca → CNe (CΓ ▷) (Ca [ p ])

lift : ∀ {i} {A : Set i} {a b : A} → a ＝ b → a ≡ b

p⁺∘<q>≡id : ((p {CΓ} ⁺) ∘ < q >) ≡ id
p⁺∘<q>≡id = begin
    (p ⁺) ∘ < q >
  ≡⟨⟩
    ((p ∘ p) , q) ∘ (id , (q [ id ]))
  ≡⟨ lift ,∘ ⟩
    (((p ∘ p) ∘ (id , (q [ id ]))) , (q [ id , (q [ id ]) ]))
  ≡⟨ lift (cong (λ σ → σ , (q [ id , (q [ id ]) ])) ∘assoc) ⟩
    ((p ∘ (p ∘ (id , (q [ id ])))) , (q [ id , (q [ id ]) ]))
  ≡⟨ lift (cong (λ σ →  (p ∘ σ) , (q [ id , (q [ id ]) ]) ) p∘,) ⟩
    ((p ∘ id) , (q [ id , (q [ id ]) ]))
  ≡⟨ lift (cong (λ σ →  σ , (q [ id , (q [ id ]) ]) ) ∘id) ⟩
    (p , (q [ id , (q [ id ]) ]))
  ≡⟨ lift (cong (λ a →  p , a ) q[,]) ⟩
    (p , (q [ id ]))
  ≡⟨ lift (cong (λ a →  p , a ) [id]) ⟩
    (p , q)
  ≡⟨ lift p,q ⟩
    id
  ∎

Cη : lam (app (Ca [ p ]) [ < q > ]) ≡ Ca
Cη {Ca = Ca} =
  begin
    lam (app (Ca [ p ]) [ < q > ])
  ≡⟨ {!  cong (lam (app  !} ⟩
    lam (((app Ca) [ p ⁺ ]) [ < q > ])
  ≡⟨ lift (cong lam (sym [∘])) ⟩
    lam ((app Ca) [ (p ⁺) ∘ < q > ])
  ≡⟨ cong' (λ σ → lam ((app Ca) [ σ ])) p⁺∘<q>≡id ⟩
    lam ((app Ca) [ id ])
  ≡⟨ lift (cong lam [id]) ⟩
    lam (app Ca)
  ≡⟨ lift Πη ⟩
    Ca
  ∎
  
data _≈[_]CNf_ : CNf CΓ Ca → Ca ≡ Cb → CNf CΓ Cb → Set where
  n-η : ∀ {f} → nlam (ne (napp (np {Ca = Ca} f) (ne (nvar vz)))) ≈[ Cη ]CNf ne f
  
-- record _≡Nf_ (a : CNf CΓ Ca) (b : CNf CΓ Cb) : Set where
--   constructor _over_
--   field
--     p : Ca ≡ Cb
--     np : a ≡[ congruence (CNf CΓ) p ] b
  
-- record _≡Ne_ (a : CNe CΓ Ca) (b : CNe CΓ Cb) : Set where
--   constructor _over_
--   field
--     p : Ca ≡ Cb
--     np : a ≡[ congruence (CNe CΓ) p ] b
    
-- {-# INJECTIVE lam #-}

-- _＝Nf?_ : (a : CNf CΓ Ca) → (b : CNf CΓ Cb) → Dec (a ≡Nf b)
-- nlam a ＝Nf? nlam b with a ＝Nf? b
-- ... | yes (refl over refl) = yes (refl over refl)
-- ... | no ¬p = no λ { (p' over p) → ¬p {!   !} }
-- nlam a ＝Nf? ne x = {!   !}
-- ne x ＝Nf? nlam b = {!   !}
-- ne x ＝Nf? ne x₁ = {!   !}

-- _＝Ne?_ : (a : CNe CΓ Ca) → (b : CNe CΓ Cb) → Dec (a ≡Ne b) 