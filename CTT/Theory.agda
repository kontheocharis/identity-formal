module CTT.Theory where

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
      _▷ : CCon → CCon

      id : CSub CΓ CΓ
      _∘_ : CSub CΓ CΓ' → CSub CΔ CΓ → CSub CΔ CΓ'
      id∘ : id ∘ Cσ ＝ Cσ
      ∘id : Cσ ∘ id ＝ Cσ
      ∘assoc : (Cσ ∘ Cσ') ∘ Cσ'' ＝ Cσ ∘ (Cσ' ∘ Cσ'')

      ε : CSub CΓ ∙
      εη : Cσ ＝ ε
      
      p : CSub (CΓ ▷) CΓ
      _[_] : CTm CΔ → (Cσ : CSub CΓ CΔ) → CTm CΓ
      q : CTm (CΓ ▷)
      _,_ : (Cσ : CSub CΓ CΔ) → CTm CΓ → CSub CΓ (CΔ ▷)
      p∘, : p ∘ (Cσ , Ca) ＝ Cσ
      p,q : (p {CΓ} , q) ＝ id
      ,∘ : (Cσ , Ca) ∘ Cσ' ＝ ((Cσ ∘ Cσ') , (Ca [ Cσ' ]))

    _⁺ : CSub CΓ CΔ → CSub (CΓ ▷) (CΔ ▷)
    _⁺ Cσ = (Cσ ∘ p) , q 
    
    <_> : CTm CΓ → CSub CΓ (CΓ ▷)
    < t > = id , (t [ id ])
    
    field
      lam : CTm (CΓ ▷) → CTm CΓ

      app : CTm CΓ → CTm (CΓ ▷)

      [id] : Ca [ id ] ＝ Ca
      [∘] : Ca [ Cσ ∘ Cσ' ] ＝ (Ca [ Cσ ]) [ Cσ' ]
      q[,] : q [ Cσ , Ca ] ＝ Ca
      
      lam[] : (lam Ca) [ Cσ ] ＝ lam (Ca [ Cσ ⁺ ])

      Πη : lam (app Ca) ＝ Ca 
      -- Πβ : app (lam Ca) ＝ Ca
      
record Model : Set1 where
  field
    s : Sorts
  open Sorts s public
  open InSorts s public
  field
    c : Ctors
  open Ctors c public
  
      
-- Displayed model

module _ (sorts : Sorts) (ctors : InSorts.Ctors sorts) where
  open Sorts sorts
  open InSorts sorts

  record Sortsᴰ : Set2 where
    field
      CConᴰ : CCon → Set1
      CSubᴰ : ∀ {CΓ CΔ} → CConᴰ CΓ → CConᴰ CΔ → CSub CΓ CΔ → Set
      CTmᴰ :  ∀ {CΓ} → CConᴰ CΓ → CTm CΓ → Set 

  open Ctors ctors
  module InSortsᴰ (sortsᴰ : Sortsᴰ) where
    open Sortsᴰ sortsᴰ

    variable  
      CΓᴰ CΓᴰ' CΔᴰ : CConᴰ _
      Caᴰ Caᴰ' Cbᴰ Cbᴰ' : CTmᴰ _ _
      Cσᴰ Cσᴰ' Cσᴰ'' : CSubᴰ _ _ _

    infix 4 _＝[_]CSub_
    _＝[_]CSub_ : CSubᴰ CΓᴰ CΓᴰ' Cσ → Cσ ＝ Cσ' → CSubᴰ CΓᴰ CΓᴰ' Cσ' → Prop
    x ＝[ p ]CSub y = x ＝[ cong (CSubᴰ _ _) p ] y

    infix 4 _＝[_]CTm_
    _＝[_]CTm_ : CTmᴰ CΓᴰ Ca → Ca ＝ Ca' → CTmᴰ CΓᴰ Ca' → Prop
    x ＝[ p ]CTm y = x ＝[ cong (CTmᴰ _) p ] y
    
    record Ctorsᴰ : Set2 where
      field 
        ∙ᴰ : CConᴰ ∙
        _▷ᴰ : CConᴰ CΓ → CConᴰ (CΓ ▷)

        idᴰ : CSubᴰ CΓᴰ CΓᴰ id
        _∘ᴰ_ : CSubᴰ CΓᴰ CΓᴰ' Cσ → CSubᴰ CΔᴰ CΓᴰ Cσ' → CSubᴰ CΔᴰ CΓᴰ' (Cσ ∘ Cσ')
        id∘ᴰ : idᴰ ∘ᴰ Cσᴰ ＝[ id∘ ]CSub Cσᴰ
        ∘idᴰ : Cσᴰ ∘ᴰ idᴰ ＝[ ∘id ]CSub Cσᴰ
        ∘assocᴰ : (Cσᴰ ∘ᴰ Cσᴰ') ∘ᴰ Cσᴰ'' ＝[ ∘assoc ]CSub Cσᴰ ∘ᴰ (Cσᴰ' ∘ᴰ Cσᴰ'')

        εᴰ : CSubᴰ CΓᴰ ∙ᴰ ε
        εηᴰ : Cσᴰ ＝[ εη ]CSub εᴰ
        
        pᴰ : CSubᴰ (CΓᴰ ▷ᴰ) CΓᴰ p
        _[_]ᴰ : CTmᴰ CΔᴰ Ca → (Cσᴰ : CSubᴰ CΓᴰ CΔᴰ Cσ) → CTmᴰ CΓᴰ (Ca [ Cσ ])
        qᴰ : CTmᴰ (CΓᴰ ▷ᴰ) q
        _,ᴰ_ : (Cσᴰ : CSubᴰ CΓᴰ CΔᴰ Cσ) → CTmᴰ CΓᴰ Ca → CSubᴰ CΓᴰ (CΔᴰ ▷ᴰ) (Cσ , Ca)
        p∘,ᴰ : pᴰ ∘ᴰ (Cσᴰ ,ᴰ Caᴰ) ＝[ p∘, ]CSub Cσᴰ
        p,qᴰ : (pᴰ {CΓᴰ = CΓᴰ} ,ᴰ qᴰ) ＝[ p,q ]CSub idᴰ
        ,∘ᴰ : (Cσᴰ ,ᴰ Caᴰ) ∘ᴰ Cσᴰ' ＝[ ,∘ ]CSub ((Cσᴰ ∘ᴰ Cσᴰ') ,ᴰ (Caᴰ [ Cσᴰ' ]ᴰ))

      _⁺ᴰ : CSubᴰ CΓᴰ CΔᴰ Cσ → CSubᴰ (CΓᴰ ▷ᴰ) (CΔᴰ ▷ᴰ) (Cσ ⁺)
      _⁺ᴰ Cσᴰ = (Cσᴰ ∘ᴰ pᴰ) ,ᴰ qᴰ 
    
      field
        lamᴰ : CTmᴰ (CΓᴰ ▷ᴰ) Ca → CTmᴰ CΓᴰ (lam Ca)
        appᴰ : CTmᴰ CΓᴰ Ca → CTmᴰ (CΓᴰ ▷ᴰ) (app Ca)

        [id]ᴰ : Caᴰ [ idᴰ ]ᴰ ＝[ [id] ]CTm Caᴰ
        [∘]ᴰ : Caᴰ [ Cσᴰ ∘ᴰ Cσᴰ' ]ᴰ ＝[ [∘] ]CTm (Caᴰ [ Cσᴰ ]ᴰ) [ Cσᴰ ]ᴰ
        q[,]ᴰ : qᴰ [ Cσᴰ ,ᴰ Caᴰ ]ᴰ ＝[ q[,] ]CTm Caᴰ
      
        lam[]ᴰ : (lamᴰ Caᴰ) [ Cσᴰ ]ᴰ ＝[ lam[] ]CTm lamᴰ (Caᴰ [ Cσᴰ ⁺ᴰ ]ᴰ)

        Πηᴰ : lamᴰ (appᴰ Caᴰ) ＝[ Πη ]CTm Caᴰ
        -- Πβᴰ : appᴰ (lamᴰ Caᴰ) ＝[ Πβ ]CTm Caᴰ
      
record Modelᴰ (m : Model) : Set2 where
  open Model m
  field
    sᴰ : Sortsᴰ s c
  open Sortsᴰ sᴰ public 
  open InSortsᴰ s c sᴰ public 
  field
    cᴰ : InSortsᴰ.Ctorsᴰ s c sᴰ
  open InSortsᴰ.Ctorsᴰ cᴰ public
        


-- Syntax

postulate
  syn : Model
        
-- Induction

module Ind (mᴰ : Modelᴰ syn) where
  open Model syn
  open Modelᴰ mᴰ

  postulate
    ∃!Con : (CΓ : CCon) → CConᴰ CΓ
    ∃!Sub : (Cσ : CSub CΓ CΔ) → CSubᴰ (∃!Con CΓ) (∃!Con CΔ) Cσ
    ∃!Tm : (Ca : CTm CΓ) → CTmᴰ (∃!Con CΓ) Ca
    
    ∃!∙ : ∃!Con ∙ ＝ ∙ᴰ
    {-# REWRITE ∃!∙ #-}

    ∃!, : ∃!Con (CΓ ▷) ＝ (∃!Con CΓ) ▷ᴰ
    {-# REWRITE ∃!, #-}

    ∃!id : ∃!Sub {CΓ} id ＝ idᴰ
    {-# REWRITE ∃!id #-}

    ∃!∘ : ∃!Sub (Cσ ∘ Cσ') ＝ ∃!Sub Cσ ∘ᴰ ∃!Sub Cσ'  
    {-# REWRITE ∃!∘ #-}

    ∃!ε : ∃!Sub {CΓ} ε ＝ εᴰ
    {-# REWRITE ∃!ε #-}

    ∃!p : ∃!Sub (p {CΓ}) ＝ pᴰ
    {-# REWRITE ∃!p #-}

    ∃![] : ∃!Tm (Ca [ Cσ ]) ＝ (∃!Tm Ca) [ ∃!Sub Cσ ]ᴰ
    {-# REWRITE ∃![] #-}

    ∃!q : ∃!Tm (q {CΓ}) ＝ qᴰ
    {-# REWRITE ∃!q #-}

    ∃!lam : ∃!Tm (lam Ca) ＝ lamᴰ (∃!Tm Ca)
    {-# REWRITE ∃!lam #-}

    ∃!app : ∃!Tm (app Ca) ＝ appᴰ (∃!Tm Ca)
    {-# REWRITE ∃!app #-}