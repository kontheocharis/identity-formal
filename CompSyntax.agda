{-# OPTIONS --prop --rewriting #-}
module CompSyntax where

open import Utils

record CTT-Sorts : Set1 where
  field
    -- Computational CWF sorts
    CCon : Set
    CSub : CCon → CCon → Set
    CTm : CCon → Set


module CTT-InSorts (Sorts : CTT-Sorts) where
  open CTT-Sorts Sorts

  variable  
    CΓ CΓ' CΔ CΔ' : CCon
    Ca Ca' Cb Cb' : CTm _
    Cσ Cσ' Cσ'' : CSub _ _
    

  record CTT-Ctors : Set1 where
    field 
      ∙ : CCon
      _, : CCon → CCon

      id : CSub CΓ CΓ
      _∘_ : CSub CΓ CΓ' → CSub CΔ CΓ → CSub CΔ CΓ'
      id∘ : id ∘ Cσ ≡ Cσ
      ∘id : Cσ ∘ id ≡ Cσ
      ∘assoc : (Cσ ∘ Cσ') ∘ Cσ'' ≡ Cσ ∘ (Cσ' ∘ Cσ'')

      ε : CSub CΓ ∙
      εη : Cσ ≡ ε
      
      p : CSub (CΓ ,) CΓ
      q : CTm (CΓ ,)
      _[_] : CTm CΔ → (Cσ : CSub CΓ CΔ) → CTm CΓ
      _,_ : (Cσ : CSub CΓ CΔ) → CTm CΓ → CSub CΓ (CΔ ,)
      p∘, : p ∘ (Cσ , Ca) ≡ Cσ
      p,q : (p {CΓ} , q) ≡ id
      ,∘ : (Cσ , Ca) ∘ Cσ' ≡ ((Cσ ∘ Cσ') , (Ca [ Cσ' ]))

      lam : CTm (CΓ ,) → CTm CΓ
      app : CTm CΓ → CTm (CΓ ,)

      [id] : Ca [ id ] ≡ Ca
      [∘] : Ca [ Cσ ∘ Cσ' ] ≡ (Ca [ Cσ ]) [ Cσ ]
      q[,] : q [ Cσ , Ca ] ≡ Ca
