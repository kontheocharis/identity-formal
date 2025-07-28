{-# OPTIONS --prop --rewriting #-}
module LTT.Theory where

open import Utils

-- Logical LWF

-- Model

record Sorts : Set1 where
  field
    LCon : Set
    LSub : LCon → LCon → Set
    LTy : LCon → Set
    LTm : ∀ LΓ → LTy LΓ → Set

module InSorts (sorts : Sorts) where
  open Sorts sorts

  variable  
    LΓ LΓ' LΔ LΔ' : LCon
    LA LA' LB LB' : LTy _
    La La' Lb Lb' : LTm _ _
    Lσ Lσ' Lσ'' : LSub _ _
    
  Lcoe : LA ＝ LB → LTm LΓ LA → LTm LΓ LB
  Lcoe p t = coe (cong (LTm _) p) t

  infix 4 _＝[_]T_
  _＝[_]T_ : LTm LΓ LA → LA ＝ LA' → LTm LΓ LA' → Prop
  x ＝[ p ]T y = x ＝[ cong (LTm _) p ] y

  record Ctors : Set1 where
    field 
      ∙ : LCon
      _▷_ : ∀ LΓ → LTy LΓ → LCon

      id : LSub LΓ LΓ
      _∘_ : LSub LΓ LΓ' → LSub LΔ LΓ → LSub LΔ LΓ'
      id∘ : id ∘ Lσ ＝ Lσ
      ∘id : Lσ ∘ id ＝ Lσ
      ∘assoc : (Lσ ∘ Lσ') ∘ Lσ'' ＝ Lσ ∘ (Lσ' ∘ Lσ'')

      _[_] : LTy LΔ → LSub LΓ LΔ → LTy LΓ
      _[_]t : LTm LΔ LA → (Lσ : LSub LΓ LΔ) → LTm LΓ (LA [ Lσ ])
      [id] : LA [ id ] ＝ LA
      [∘] : LA [ Lσ ∘ Lσ' ] ＝ (LA [ Lσ ]) [ Lσ' ]
      [id]t : La [ id ]t ＝[ [id] ]T La
      [∘]t : La [ Lσ ∘ Lσ' ]t ＝[ [∘] ]T (La [ Lσ ]t) [ Lσ' ]t

      p : LSub (LΓ ▷ LA) LΓ
      q : LTm (LΓ ▷ LA) (LA [ p ])
      _,_ : (Lσ : LSub LΓ LΔ) → LTm LΓ (LA [ Lσ ]) → LSub LΓ (LΔ ▷ LA)
      p∘, : p ∘ (Lσ , La) ＝ Lσ
      p,q : (p {LΓ} {LA} , q) ＝ id
      ,∘ : (Lσ , La) ∘ Lσ' ＝ ((Lσ ∘ Lσ') , (Lcoe (sym [∘]) (La [ Lσ' ]t)))
      q[,] : q [ Lσ , La ]t ＝[ trs (sym [∘]) (cong (LA [_]) p∘,) ]T La

      ε : LSub LΓ ∙
      εη : Lσ ＝ ε
      
    _⁺ : (Lσ : LSub LΓ LΔ) → LSub (LΓ ▷ (LA [ Lσ ])) (LΔ ▷ LA)
    _⁺ Lσ = (Lσ ∘ p) , (Lcoe (sym [∘]) q)
    
    field
      U : LTy LΓ
      El : LTm LΓ U → LTy LΓ
      Π : (LA : LTy LΓ) → LTy (LΓ ▷ LA) → LTy LΓ
      Π-I : (LA : LTy LΓ) → LTy (LΓ ▷ LA) → LTy LΓ
      Π-ID : (LA : LTy LΓ) → LTy (LΓ ▷ LA) → LTy LΓ
      
      U[] : U [ Lσ ] ＝ U
      El[] : (El La) [ Lσ ] ＝ El (Lcoe U[] (La [ Lσ ]t))
      Π[] : (Π LA LB) [ Lσ ] ＝ Π (LA [ Lσ ]) (LB [ Lσ ⁺ ])
      Π-I[] : (Π-I LA LB) [ Lσ ] ＝ Π-I (LA [ Lσ ]) (LB [ Lσ ⁺ ])
      Π-ID[] : (Π-ID LA LB) [ Lσ ] ＝ Π-ID (LA [ Lσ ]) (LB [ Lσ ⁺ ])
    
      lam : LTm (LΓ ▷ LA) LB → LTm LΓ (Π LA LB)
      app : LTm LΓ (Π LA LB) → LTm (LΓ ▷ LA) LB

      lam-I : LTm (LΓ ▷ LA) LB → LTm LΓ (Π-I LA LB)
      app-I : LTm LΓ (Π-I LA LB) → LTm (LΓ ▷ LA) LB

      lam-ID : LTm (LΓ ▷ LA) LB → LTm LΓ (Π-ID LA LB)
      app-ID : LTm LΓ (Π-ID LA LB) → LTm (LΓ ▷ LA) LB
      
      lam[] : (lam La) [ Lσ ]t ＝[ Π[] ]T lam (La [ Lσ ⁺ ]t)
      lam-I[] : (lam-I La) [ Lσ ]t ＝[ Π-I[] ]T lam-I (La [ Lσ ⁺ ]t)
      lam-ID[] : (lam-ID La) [ Lσ ]t ＝[ Π-ID[] ]T lam-ID (La [ Lσ ⁺ ]t)

      Πη : lam (app La) ＝ La 
      Πβ : app (lam La) ＝ La
      
      Π-Iη : lam-I (app-I La) ＝ La 
      Π-Iβ : app-I (lam-I La) ＝ La

      Π-IDη : lam-ID (app-ID La) ＝ La 
      Π-IDβ : app-ID (lam-ID La) ＝ La

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

  record Sortsᴰ : Set1 where
    field
      LConᴰ : LCon → Set
      LSubᴰ : ∀ {LΓ LΔ} → LConᴰ LΓ → LConᴰ LΔ → LSub LΓ LΔ → Set
      LTyᴰ : ∀ {LΓ} → LConᴰ LΓ → LTy LΓ → Set
      LTmᴰ : ∀ {LΓ LA} → (LΓᴰ : LConᴰ LΓ) → LTyᴰ LΓᴰ LA → LTm LΓ LA → Set

  open Ctors ctors
  module InSortsᴰ (sortsᴰ : Sortsᴰ) where
    open Sortsᴰ sortsᴰ

    variable  
      LΓᴰ LΓᴰ' LΔᴰ : LConᴰ _
      LAᴰ LAᴰ' LBᴰ LBᴰ' : LTyᴰ _ _
      Laᴰ Laᴰ' Lbᴰ Lbᴰ' : LTmᴰ _ _ _
      Lσᴰ Lσᴰ' Lσᴰ'' : LSubᴰ _ _ _

    infix 4 _＝[_]LSub_
    _＝[_]LSub_ : LSubᴰ LΓᴰ LΓᴰ' Lσ → Lσ ＝ Lσ' → LSubᴰ LΓᴰ LΓᴰ' Lσ' → Prop
    x ＝[ p ]LSub y = x ＝[ cong (LSubᴰ _ _) p ] y

    infix 4 _＝[_]LTy_
    _＝[_]LTy_ : LTyᴰ LΓᴰ LA → LA ＝ LA' → LTyᴰ LΓᴰ LA' → Prop
    x ＝[ p ]LTy y = x ＝[ cong (LTyᴰ _) p ] y
    
    Lcoeᴰ : {La : LTm LΓ LA}
      → {La' : LTm LΓ LA'}
      → (p : LA ＝ LA')
      → LAᴰ ＝[ p ]LTy LAᴰ'
      → La ＝[ p ]T La'
      → LTmᴰ LΓᴰ LAᴰ La
      → LTmᴰ LΓᴰ LAᴰ' La'
    Lcoeᴰ p q r t = {!   !}

    infix 4 _＝[_][_][_]LTm_
    _＝[_][_][_]LTm_ : {La : LTm LΓ LA}
      → {La' : LTm LΓ LA'}
      → LTmᴰ LΓᴰ LAᴰ La
      → (p : LA ＝ LA')
      → LAᴰ ＝[ p ]LTy LAᴰ'
      → La ＝[ p ]T La'
      → LTmᴰ LΓᴰ LAᴰ' La'
      → Prop
    x ＝[ q ][ p ][ r ]LTm y = x ＝[ {!  cong2 ? ?  !} ] y
    
    record Ctorsᴰ : Set1 where
      field 
        ∙ᴰ : LConᴰ ∙
        _▷ᴰ_ : (LΓᴰ : LConᴰ LΓ) → LTyᴰ LΓᴰ LA → LConᴰ (LΓ ▷ LA)

        idᴰ : LSubᴰ LΓᴰ LΓᴰ id
        _∘ᴰ_ : LSubᴰ LΓᴰ LΓᴰ' Lσ → LSubᴰ LΔᴰ LΓᴰ Lσ' → LSubᴰ LΔᴰ LΓᴰ' (Lσ ∘ Lσ')
        id∘ᴰ : idᴰ ∘ᴰ Lσᴰ ＝[ id∘ ]LSub Lσᴰ
        ∘idᴰ : Lσᴰ ∘ᴰ idᴰ ＝[ ∘id ]LSub Lσᴰ
        ∘assocᴰ : (Lσᴰ ∘ᴰ Lσᴰ') ∘ᴰ Lσᴰ'' ＝[ ∘assoc ]LSub Lσᴰ ∘ᴰ (Lσᴰ' ∘ᴰ Lσᴰ'')

        _[_]ᴰ : LTyᴰ LΔᴰ LA → (Lσᴰ : LSubᴰ LΓᴰ LΔᴰ Lσ) → LTyᴰ LΓᴰ (LA [ Lσ ])
        _[_]tᴰ : LTmᴰ LΔᴰ LAᴰ La → (Lσᴰ : LSubᴰ LΓᴰ LΔᴰ Lσ) → LTmᴰ LΓᴰ (LAᴰ [ Lσᴰ ]ᴰ) (La [ Lσ ]t)
        [id]ᴰ : LAᴰ [ idᴰ ]ᴰ ＝[ [id] ]LTy LAᴰ
        [∘]ᴰ : LAᴰ [ Lσᴰ ∘ᴰ Lσᴰ' ]ᴰ ＝[ [∘] ]LTy (LAᴰ [ Lσᴰ ]ᴰ) [ Lσᴰ' ]ᴰ
        [id]tᴰ : Laᴰ [ idᴰ ]tᴰ ＝[ [id] ][ [id]ᴰ ][ [id]t ]LTm Laᴰ
        [∘]tᴰ : Laᴰ [ Lσᴰ ∘ᴰ Lσᴰ' ]tᴰ ＝[ [∘] ][ [∘]ᴰ ][ [∘]t ]LTm (Laᴰ [ Lσᴰ ]tᴰ) [ Lσᴰ' ]tᴰ

        pᴰ : LSubᴰ (LΓᴰ ▷ᴰ LAᴰ) LΓᴰ p
        qᴰ : LTmᴰ (LΓᴰ ▷ᴰ LAᴰ) (LAᴰ [ pᴰ ]ᴰ) q
        _,ᴰ_ : (Lσᴰ : LSubᴰ LΓᴰ LΔᴰ Lσ) → LTmᴰ LΓᴰ (LAᴰ [ Lσᴰ ]ᴰ) La → LSubᴰ LΓᴰ (LΔᴰ ▷ᴰ LAᴰ) (Lσ , La)
        p∘,ᴰ : pᴰ ∘ᴰ (Lσᴰ ,ᴰ Laᴰ) ＝[ p∘, ]LSub Lσᴰ
        p,qᴰ : (pᴰ {LΓᴰ = LΓᴰ} {LAᴰ = LAᴰ} ,ᴰ qᴰ) ＝[ p,q ]LSub idᴰ
        ,∘ᴰ : (Lσᴰ ,ᴰ Laᴰ) ∘ᴰ Lσᴰ' ＝[ ,∘ ]LSub ((Lσᴰ ∘ᴰ Lσᴰ') ,ᴰ (Lcoeᴰ (sym [∘]) (hsym {!  [∘]ᴰ !}) refl (Laᴰ [ Lσᴰ' ]tᴰ)))
        q[,]ᴰ : qᴰ [ Lσᴰ ,ᴰ Laᴰ ]tᴰ ＝[ trs (sym [∘]) (cong (LA [_]) p∘,) ][ {!   !} ][ q[,] ]LTm Laᴰ

        εᴰ : LSubᴰ LΓᴰ ∙ᴰ ε
        εηᴰ : Lσᴰ ＝[ εη ]LSub εᴰ
        
      _⁺ᴰ : (Lσᴰ : LSubᴰ LΓᴰ LΔᴰ Lσ) → LSubᴰ (LΓᴰ ▷ᴰ (LAᴰ [ Lσᴰ ]ᴰ)) (LΔᴰ ▷ᴰ LAᴰ) (Lσ ⁺)
      _⁺ᴰ Lσᴰ = (Lσᴰ ∘ᴰ pᴰ) ,ᴰ (Lcoeᴰ (sym [∘]) {!   !} ({!   !} [∘]ᴰ) qᴰ)
    
      field
        Uᴰ : LTyᴰ LΓᴰ U
        Elᴰ : LTmᴰ LΓᴰ Uᴰ La → LTyᴰ LΓᴰ (El La)
        Πᴰ : (LAᴰ : LTyᴰ LΓᴰ LA) → LTyᴰ (LΓᴰ ▷ᴰ LAᴰ) LB → LTyᴰ LΓᴰ (Π LA LB)
        Π-Iᴰ : (LAᴰ : LTyᴰ LΓᴰ LA) → LTyᴰ (LΓᴰ ▷ᴰ LAᴰ) LB → LTyᴰ LΓᴰ (Π-I LA LB)
        Π-IDᴰ : (LAᴰ : LTyᴰ LΓᴰ LA) → LTyᴰ (LΓᴰ ▷ᴰ LAᴰ) LB → LTyᴰ LΓᴰ (Π-ID LA LB)
        
        U[]ᴰ : Uᴰ [ Lσᴰ ]ᴰ ＝[ U[] ]LTy Uᴰ
        El[]ᴰ : (Elᴰ Laᴰ) [ Lσᴰ ]ᴰ ＝[ El[] ]LTy Elᴰ (Lcoeᴰ U[] U[]ᴰ refl (Laᴰ [ Lσᴰ ]tᴰ))
        Π[]ᴰ : (Πᴰ LAᴰ LBᴰ) [ Lσᴰ ]ᴰ ＝[ Π[] ]LTy Πᴰ (LAᴰ [ Lσᴰ ]ᴰ) (LBᴰ [ Lσᴰ ⁺ᴰ ]ᴰ)
        Π-I[]ᴰ : (Π-Iᴰ LAᴰ LBᴰ) [ Lσᴰ ]ᴰ ＝[ Π-I[] ]LTy Π-Iᴰ (LAᴰ [ Lσᴰ ]ᴰ) (LBᴰ [ Lσᴰ ⁺ᴰ ]ᴰ)
        Π-ID[]ᴰ : (Π-IDᴰ LAᴰ LBᴰ) [ Lσᴰ ]ᴰ ＝[ Π-ID[] ]LTy Π-IDᴰ (LAᴰ [ Lσᴰ ]ᴰ) (LBᴰ [ Lσᴰ ⁺ᴰ ]ᴰ)
    
        lamᴰ : LTmᴰ (LΓᴰ ▷ᴰ LAᴰ) LBᴰ La → LTmᴰ LΓᴰ (Πᴰ LAᴰ LBᴰ) (lam La)
        appᴰ : LTmᴰ LΓᴰ (Πᴰ LAᴰ LBᴰ) La → LTmᴰ (LΓᴰ ▷ᴰ LAᴰ) LBᴰ (app La)

        lam-Iᴰ : LTmᴰ (LΓᴰ ▷ᴰ LAᴰ) LBᴰ La → LTmᴰ LΓᴰ (Π-Iᴰ LAᴰ LBᴰ) (lam-I La)
        app-Iᴰ : LTmᴰ LΓᴰ (Π-Iᴰ LAᴰ LBᴰ) La → LTmᴰ (LΓᴰ ▷ᴰ LAᴰ) LBᴰ (app-I La)

        lam-IDᴰ : LTmᴰ (LΓᴰ ▷ᴰ LAᴰ) LBᴰ La → LTmᴰ LΓᴰ (Π-IDᴰ LAᴰ LBᴰ) (lam-ID La)
        app-IDᴰ : LTmᴰ LΓᴰ (Π-IDᴰ LAᴰ LBᴰ) La → LTmᴰ (LΓᴰ ▷ᴰ LAᴰ) LBᴰ (app-ID La)
        
        lam[]ᴰ : (lamᴰ Laᴰ) [ Lσᴰ ]tᴰ ＝[ Π[] ][ Π[]ᴰ ][ lam[] ]LTm lamᴰ (Laᴰ [ Lσᴰ ⁺ᴰ ]tᴰ)
        lam-I[]ᴰ : (lam-Iᴰ Laᴰ) [ Lσᴰ ]tᴰ ＝[ Π-I[] ][ Π-I[]ᴰ ][ lam-I[] ]LTm lam-Iᴰ (Laᴰ [ Lσᴰ ⁺ᴰ ]tᴰ)
        lam-ID[]ᴰ : (lam-IDᴰ Laᴰ) [ Lσᴰ ]tᴰ ＝[ Π-ID[] ][ Π-ID[]ᴰ ][ lam-ID[] ]LTm lam-IDᴰ (Laᴰ [ Lσᴰ ⁺ᴰ ]tᴰ)

        Πηᴰ : lamᴰ (appᴰ Laᴰ) ＝[ refl ][ refl ][ Πη ]LTm Laᴰ
        Πβᴰ : appᴰ (lamᴰ Laᴰ) ＝[ refl ][ refl ][ Πβ ]LTm Laᴰ
        
        Π-Iηᴰ : lam-Iᴰ (app-Iᴰ Laᴰ) ＝[ refl ][ refl ][ Π-Iη ]LTm Laᴰ
        Π-Iβᴰ : app-Iᴰ (lam-Iᴰ Laᴰ) ＝[ refl ][ refl ][ Π-Iβ ]LTm Laᴰ

        Π-IDηᴰ : lam-IDᴰ (app-IDᴰ Laᴰ) ＝[ refl ][ refl ][ Π-IDη ]LTm Laᴰ
        Π-IDβᴰ : app-IDᴰ (lam-IDᴰ Laᴰ) ＝[ refl ][ refl ][ Π-IDβ ]LTm Laᴰ
      
record Modelᴰ (m : Model) : Set1 where
  open Model m
  field
    sᴰ : Sortsᴰ s c
  open Sortsᴰ sᴰ public 
  open InSortsᴰ s c sᴰ public 
  field
    cᴰ : InSortsᴰ.Ctorsᴰ s c sᴰ
  open InSortsᴰ.Ctorsᴰ cᴰ public
        

-- -- Syntax

postulate
  syn : Model
        
-- Induction

module Ind (mᴰ : Modelᴰ syn) where
  open Model syn
  open Modelᴰ mᴰ

  postulate
    ∃!Con : (LΓ : LCon) → LConᴰ LΓ
    ∃!Sub : (Lσ : LSub LΓ LΔ) → LSubᴰ (∃!Con LΓ) (∃!Con LΔ) Lσ
    ∃!Ty : (LA : LTy LΓ) → LTyᴰ (∃!Con LΓ) LA
    ∃!Tm : (La : LTm LΓ LA) → LTmᴰ (∃!Con LΓ) (∃!Ty LA) La
    
    ∃!∙ : ∃!Con ∙ ＝ ∙ᴰ
    {-# REWRITE ∃!∙ #-}

    ∃!▷ : ∃!Con (LΓ ▷ LA) ＝ (∃!Con LΓ) ▷ᴰ (∃!Ty LA)
    {-# REWRITE ∃!▷ #-}

    ∃!id : ∃!Sub {LΓ} id ＝ idᴰ
    {-# REWRITE ∃!id #-}

    ∃!∘ : ∃!Sub (Lσ ∘ Lσ') ＝ ∃!Sub Lσ ∘ᴰ ∃!Sub Lσ'  
    {-# REWRITE ∃!∘ #-}

    ∃![] : ∃!Ty (LA [ Lσ ]) ＝ (∃!Ty LA) [ ∃!Sub Lσ ]ᴰ
    {-# REWRITE ∃![] #-}

    ∃![]t : ∃!Tm (La [ Lσ ]t) ＝ (∃!Tm La) [ ∃!Sub Lσ ]tᴰ
    {-# REWRITE ∃![]t #-}

    ∃!p : ∃!Sub (p {LΓ} {LA}) ＝ pᴰ
    {-# REWRITE ∃!p #-}

    ∃!q : ∃!Tm (q {LΓ} {LA}) ＝ qᴰ
    {-# REWRITE ∃!q #-}

    ∃!, : ∃!Sub (Lσ , La) ＝ (∃!Sub Lσ) ,ᴰ (∃!Tm La)
    {-# REWRITE ∃!, #-}

    ∃!ε : ∃!Sub {LΓ} ε ＝ εᴰ
    {-# REWRITE ∃!ε #-}

    ∃!U : ∃!Ty (U {LΓ}) ＝ Uᴰ
    {-# REWRITE ∃!U #-}

    ∃!El : ∃!Ty (El La) ＝ Elᴰ (∃!Tm La)
    {-# REWRITE ∃!El #-}

    ∃!Π : ∃!Ty (Π LA LB) ＝ Πᴰ (∃!Ty LA) (∃!Ty LB)
    {-# REWRITE ∃!Π #-}

    ∃!Π-I : ∃!Ty (Π-I LA LB) ＝ Π-Iᴰ (∃!Ty LA) (∃!Ty LB)
    {-# REWRITE ∃!Π-I #-}

    ∃!Π-ID : ∃!Ty (Π-ID LA LB) ＝ Π-IDᴰ (∃!Ty LA) (∃!Ty LB)
    {-# REWRITE ∃!Π-ID #-}

    ∃!lam : ∃!Tm (lam La) ＝ lamᴰ (∃!Tm La)
    {-# REWRITE ∃!lam #-}

    ∃!app : ∃!Tm (app La) ＝ appᴰ (∃!Tm La)
    {-# REWRITE ∃!app #-}

    ∃!lam-I : ∃!Tm (lam-I La) ＝ lam-Iᴰ (∃!Tm La)
    {-# REWRITE ∃!lam-I #-}

    ∃!app-I : ∃!Tm (app-I La) ＝ app-Iᴰ (∃!Tm La)
    {-# REWRITE ∃!app-I #-}

    ∃!lam-ID : ∃!Tm (lam-ID La) ＝ lam-IDᴰ (∃!Tm La)
    {-# REWRITE ∃!lam-ID #-}

    ∃!app-ID : ∃!Tm (app-ID La) ＝ app-IDᴰ (∃!Tm La)
    {-# REWRITE ∃!app-ID #-}
