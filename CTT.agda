{-# OPTIONS --prop --rewriting #-}
module CTT where

open import Utils

-- Computational CWF

-- Model

record Sorts : Set1 where
  field
    CCon : Set
    CSub : CCon → CCon → Set
    CTm : CCon → Set

module InSorts (sorts : Sorts) where
  open Sorts sorts

  variable  
    CΓ CΓ' CΔ CΔ' : CCon
    Ca Ca' Cb Cb' : CTm _
    Cσ Cσ' Cσ'' : CSub _ _

  record Ctors : Set1 where
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

    _⁺ : CSub CΓ CΔ → CSub (CΓ ,) (CΔ ,)
    _⁺ Cσ = (Cσ ∘ p) , q 
    
    field
      lam : CTm (CΓ ,) → CTm CΓ
      app : CTm CΓ → CTm (CΓ ,)

      [id] : Ca [ id ] ≡ Ca
      [∘] : Ca [ Cσ ∘ Cσ' ] ≡ (Ca [ Cσ ]) [ Cσ ]
      q[,] : q [ Cσ , Ca ] ≡ Ca
      
      lam[] : (lam Ca) [ Cσ ] ≡ lam (Ca [ Cσ ⁺ ])

      Πη : lam (app Ca) ≡ Ca 
      Πβ : app (lam Ca) ≡ Ca
      
record Model : Set1 where
  field
    s : Sorts
  open InSorts s
  field
    c : Ctors
  
      
-- Displayed model

module _ (sorts : Sorts) (ctors : InSorts.Ctors sorts) where
  open Sorts sorts
  open InSorts sorts

  record Sortsᴰ : Set1 where
    field
      CConᴰ : CCon → Set
      CSubᴰ : ∀ {CΓ CΔ} → CConᴰ CΓ → CConᴰ CΔ → CSub CΓ CΔ → Set
      CTmᴰ :  ∀ {CΓ} → CConᴰ CΓ → CTm CΓ → Set 

  open Ctors ctors
  module InSortsᴰ (sortsᴰ : Sortsᴰ) where
    open Sortsᴰ sortsᴰ

    variable  
      CΓᴰ CΓᴰ' CΔᴰ : CConᴰ _
      Caᴰ Caᴰ' Cbᴰ Cbᴰ' : CTmᴰ _ _
      Cσᴰ Cσᴰ' Cσᴰ'' : CSubᴰ _ _ _

    infix 4 _≡[_]CSub_
    _≡[_]CSub_ : CSubᴰ CΓᴰ CΓᴰ' Cσ → Cσ ≡ Cσ' → CSubᴰ CΓᴰ CΓᴰ' Cσ' → Prop
    x ≡[ p ]CSub y = x ≡[ cong (CSubᴰ _ _) p ] y

    infix 4 _≡[_]CTm_
    _≡[_]CTm_ : CTmᴰ CΓᴰ Ca → Ca ≡ Ca' → CTmᴰ CΓᴰ Ca' → Prop
    x ≡[ p ]CTm y = x ≡[ cong (CTmᴰ _) p ] y
    
    record Ctorsᴰ : Set1 where
      field 
        ∙ : CConᴰ ∙
        _, : CConᴰ CΓ → CConᴰ (CΓ ,)

        id : CSubᴰ CΓᴰ CΓᴰ id
        _∘_ : CSubᴰ CΓᴰ CΓᴰ' Cσ → CSubᴰ CΔᴰ CΓᴰ Cσ' → CSubᴰ CΔᴰ CΓᴰ' (Cσ ∘ Cσ')
        id∘ : id ∘ Cσᴰ ≡[ id∘ ]CSub Cσᴰ
        ∘id : Cσᴰ ∘ id ≡[ ∘id ]CSub Cσᴰ
        ∘assoc : (Cσᴰ ∘ Cσᴰ') ∘ Cσᴰ'' ≡[ ∘assoc ]CSub Cσᴰ ∘ (Cσᴰ' ∘ Cσᴰ'')

        ε : CSubᴰ CΓᴰ ∙ ε
        εη : Cσᴰ ≡[ εη ]CSub ε
        
        p : CSubᴰ (CΓᴰ ,) CΓᴰ p
        q : CTmᴰ (CΓᴰ ,) q
        _[_] : CTmᴰ CΔᴰ Ca → (Cσᴰ : CSubᴰ CΓᴰ CΔᴰ Cσ) → CTmᴰ CΓᴰ (Ca [ Cσ ])
        _,_ : (Cσᴰ : CSubᴰ CΓᴰ CΔᴰ Cσ) → CTmᴰ CΓᴰ Ca → CSubᴰ CΓᴰ (CΔᴰ ,) (Cσ , Ca)
        p∘, : p ∘ (Cσᴰ , Caᴰ) ≡[ p∘, ]CSub Cσᴰ
        p,q : (p {CΓᴰ = CΓᴰ} , q) ≡[ p,q ]CSub id
        ,∘ : (Cσᴰ , Caᴰ) ∘ Cσᴰ' ≡[ ,∘ ]CSub ((Cσᴰ ∘ Cσᴰ') , (Caᴰ [ Cσᴰ' ]))

        lam : CTmᴰ (CΓᴰ ,) Ca → CTmᴰ CΓᴰ (lam Ca)
        app : CTmᴰ CΓᴰ Ca → CTmᴰ (CΓᴰ ,) (app Ca)

        [id] : Caᴰ [ id ] ≡[ [id] ]CTm Caᴰ
        -- [∘] : Ca [ Cσ ∘ Cσ' ] ≡ (Ca [ Cσ ]) [ Cσ ]
        -- q[,] : q [ Cσ , Ca ] ≡ Ca
      
        -- lam[] : (lam Ca) [ Cσ ] ≡ lam (Ca [ Cσ ⁺ ])

        -- Πη : lam (app Ca) ≡ Ca 
        -- Πβ : app (lam Ca) ≡ Ca
      
record Modelᴰ (m : Model) : Set1 where
  open Model m
  field
    sᴰ : Sortsᴰ s c
  open InSorts s
  field
    cᴰ : InSortsᴰ.Ctorsᴰ s c sᴰ
        
        
-- Should be postulates
record Section {m} (mᴰ : Modelᴰ m) : Set1 where
  open Model m
  open Modelᴰ mᴰ


-- Syntax

postulate
  syn : Model
  elim : (m : Modelᴰ syn) → Section m