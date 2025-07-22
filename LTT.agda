{-# OPTIONS --prop --rewriting #-}
module LTT where

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
    
  Lcoe : LA ≡ LB → LTm LΓ LA → LTm LΓ LB
  Lcoe p t = coe (cong (LTm _) p) t

  infix 4 _≡[_]T_
  _≡[_]T_ : LTm LΓ LA → LA ≡ LA' → LTm LΓ LA' → Prop
  x ≡[ p ]T y = x ≡[ cong (LTm _) p ] y

  record Ctors : Set1 where
    field 
      ∙ : LCon
      _▷_ : ∀ LΓ → LTy LΓ → LCon

      id : LSub LΓ LΓ
      _∘_ : LSub LΓ LΓ' → LSub LΔ LΓ → LSub LΔ LΓ'
      id∘ : id ∘ Lσ ≡ Lσ
      ∘id : Lσ ∘ id ≡ Lσ
      ∘assoc : (Lσ ∘ Lσ') ∘ Lσ'' ≡ Lσ ∘ (Lσ' ∘ Lσ'')

      _[_] : LTy LΔ → LSub LΓ LΔ → LTy LΓ
      _[_]t : LTm LΔ LA → (Lσ : LSub LΓ LΔ) → LTm LΓ (LA [ Lσ ])
      [id] : LA [ id ] ≡ LA
      [∘] : LA [ Lσ ∘ Lσ' ] ≡ (LA [ Lσ ]) [ Lσ' ]
      [id]t : La [ id ]t ≡[ [id] ]T La
      [∘]t : La [ Lσ ∘ Lσ' ]t ≡[ [∘] ]T (La [ Lσ ]t) [ Lσ' ]t

      p : LSub (LΓ ▷ LA) LΓ
      q : LTm (LΓ ▷ LA) (LA [ p ])
      _,_ : (Lσ : LSub LΓ LΔ) → LTm LΓ (LA [ Lσ ]) → LSub LΓ (LΔ ▷ LA)
      p∘, : p ∘ (Lσ , La) ≡ Lσ
      p,q : (p {LΓ} {LA} , q) ≡ id
      ,∘ : (Lσ , La) ∘ Lσ' ≡ ((Lσ ∘ Lσ') , (Lcoe (sym [∘]) (La [ Lσ' ]t)))
      q[,] : q [ Lσ , La ]t ≡[ trs (sym [∘]) (cong (LA [_]) p∘,) ]T La

      ε : LSub LΓ ∙
      εη : Lσ ≡ ε
      
    _⁺ : (Lσ : LSub LΓ LΔ) → LSub (LΓ ▷ (LA [ Lσ ])) (LΔ ▷ LA)
    _⁺ Lσ = (Lσ ∘ p) , (Lcoe (sym [∘]) q)
    
    field
      U : LTy LΓ
      El : LTm LΓ U → LTy LΓ
      Π : (LA : LTy LΓ) → LTy (LΓ ▷ LA) → LTy LΓ
      Π-I : (LA : LTy LΓ) → LTy (LΓ ▷ LA) → LTy LΓ
      Π-ID : (LA : LTy LΓ) → LTy (LΓ ▷ LA) → LTy LΓ
      
      U[] : U [ Lσ ] ≡ U
      El[] : (El La) [ Lσ ] ≡ El (Lcoe U[] (La [ Lσ ]t))
      Π[] : (Π LA LB) [ Lσ ] ≡ Π (LA [ Lσ ]) (LB [ Lσ ⁺ ])
      Π-I[] : (Π-I LA LB) [ Lσ ] ≡ Π-I (LA [ Lσ ]) (LB [ Lσ ⁺ ])
      Π-ID[] : (Π-ID LA LB) [ Lσ ] ≡ Π-ID (LA [ Lσ ]) (LB [ Lσ ⁺ ])
    
      lam : LTm (LΓ ▷ LA) LB → LTm LΓ (Π LA LB)
      app : LTm LΓ (Π LA LB) → LTm (LΓ ▷ LA) LB

      lam-I : LTm (LΓ ▷ LA) LB → LTm LΓ (Π-I LA LB)
      app-I : LTm LΓ (Π-I LA LB) → LTm (LΓ ▷ LA) LB

      lam-ID : LTm (LΓ ▷ LA) LB → LTm LΓ (Π-ID LA LB)
      app-ID : LTm LΓ (Π-ID LA LB) → LTm (LΓ ▷ LA) LB
      
      lam[] : (lam La) [ Lσ ]t ≡[ Π[] ]T lam (La [ Lσ ⁺ ]t)
      lam-I[] : (lam-I La) [ Lσ ]t ≡[ Π-I[] ]T lam-I (La [ Lσ ⁺ ]t)
      lam-ID[] : (lam-ID La) [ Lσ ]t ≡[ Π-ID[] ]T lam-ID (La [ Lσ ⁺ ]t)

      Πη : lam (app La) ≡ La 
      Πβ : app (lam La) ≡ La
      
      Π-Iη : lam-I (app-I La) ≡ La 
      Π-Iβ : app-I (lam-I La) ≡ La

      Π-IDη : lam-ID (app-ID La) ≡ La 
      Π-IDβ : app-ID (lam-ID La) ≡ La

-- record Model : Set1 where
--   field
--     s : Sorts
--   open Sorts s public
--   open InSorts s public
--   field
--     c : Ctors
--   open Ctors c public
  
      
-- -- Displayed model

-- -- module _ (sorts : Sorts) (ctors : InSorts.Ctors sorts) where
-- --   open Sorts sorts
-- --   open InSorts sorts

-- --   record Sortsᴰ : Set1 where
-- --     field
-- --       LConᴰ : LCon → Set
-- --       LSubᴰ : ∀ {LΓ LΔ} → LConᴰ LΓ → LConᴰ LΔ → LSub LΓ LΔ → Set
-- --       LTmᴰ :  ∀ {LΓ} → LConᴰ LΓ → LTm LΓ → Set 

-- --   open Ctors ctors
-- --   module InSortsᴰ (sortsᴰ : Sortsᴰ) where
-- --     open Sortsᴰ sortsᴰ

-- --     variable  
-- --       LΓᴰ LΓᴰ' LΔᴰ : LConᴰ _
-- --       Laᴰ Laᴰ' Lbᴰ Lbᴰ' : LTmᴰ _ _
-- --       Lσᴰ Lσᴰ' Lσᴰ'' : LSubᴰ _ _ _

-- --     infix 4 _≡[_]LSub_
-- --     _≡[_]LSub_ : LSubᴰ LΓᴰ LΓᴰ' Lσ → Lσ ≡ Lσ' → LSubᴰ LΓᴰ LΓᴰ' Lσ' → Prop
-- --     x ≡[ p ]LSub y = x ≡[ cong (LSubᴰ _ _) p ] y

-- --     infix 4 _≡[_]LTm_
-- --     _≡[_]LTm_ : LTmᴰ LΓᴰ La → La ≡ La' → LTmᴰ LΓᴰ La' → Prop
-- --     x ≡[ p ]LTm y = x ≡[ cong (LTmᴰ _) p ] y
    
-- --     record Ctorsᴰ : Set1 where
-- --       field 
-- --         ∙ᴰ : LConᴰ ∙
-- --         _,ᴰ : LConᴰ LΓ → LConᴰ (LΓ ,)

-- --         idᴰ : LSubᴰ LΓᴰ LΓᴰ id
-- --         _∘ᴰ_ : LSubᴰ LΓᴰ LΓᴰ' Lσ → LSubᴰ LΔᴰ LΓᴰ Lσ' → LSubᴰ LΔᴰ LΓᴰ' (Lσ ∘ Lσ')
-- --         id∘ᴰ : idᴰ ∘ᴰ Lσᴰ ≡[ id∘ ]LSub Lσᴰ
-- --         ∘idᴰ : Lσᴰ ∘ᴰ idᴰ ≡[ ∘id ]LSub Lσᴰ
-- --         ∘assocᴰ : (Lσᴰ ∘ᴰ Lσᴰ') ∘ᴰ Lσᴰ'' ≡[ ∘assoc ]LSub Lσᴰ ∘ᴰ (Lσᴰ' ∘ᴰ Lσᴰ'')

-- --         εᴰ : LSubᴰ LΓᴰ ∙ᴰ ε
-- --         εηᴰ : Lσᴰ ≡[ εη ]LSub εᴰ
        
-- --         pᴰ : LSubᴰ (LΓᴰ ,ᴰ) LΓᴰ p
-- --         qᴰ : LTmᴰ (LΓᴰ ,ᴰ) q
-- --         _[_]ᴰ : LTmᴰ LΔᴰ La → (Lσᴰ : LSubᴰ LΓᴰ LΔᴰ Lσ) → LTmᴰ LΓᴰ (La [ Lσ ])
-- --         _,ᴰ_ : (Lσᴰ : LSubᴰ LΓᴰ LΔᴰ Lσ) → LTmᴰ LΓᴰ La → LSubᴰ LΓᴰ (LΔᴰ ,ᴰ) (Lσ , La)
-- --         p∘,ᴰ : pᴰ ∘ᴰ (Lσᴰ ,ᴰ Laᴰ) ≡[ p∘, ]LSub Lσᴰ
-- --         p,qᴰ : (pᴰ {LΓᴰ = LΓᴰ} ,ᴰ qᴰ) ≡[ p,q ]LSub idᴰ
-- --         ,∘ᴰ : (Lσᴰ ,ᴰ Laᴰ) ∘ᴰ Lσᴰ' ≡[ ,∘ ]LSub ((Lσᴰ ∘ᴰ Lσᴰ') ,ᴰ (Laᴰ [ Lσᴰ' ]ᴰ))

-- --       _⁺ᴰ : LSubᴰ LΓᴰ LΔᴰ Lσ → LSubᴰ (LΓᴰ ,ᴰ) (LΔᴰ ,ᴰ) (Lσ ⁺)
-- --       _⁺ᴰ Lσᴰ = (Lσᴰ ∘ᴰ pᴰ) ,ᴰ qᴰ 
    
-- --       field
-- --         lamᴰ : LTmᴰ (LΓᴰ ,ᴰ) La → LTmᴰ LΓᴰ (lam La)
-- --         appᴰ : LTmᴰ LΓᴰ La → LTmᴰ (LΓᴰ ,ᴰ) (app La)

-- --         [id]ᴰ : Laᴰ [ idᴰ ]ᴰ ≡[ [id] ]LTm Laᴰ
-- --         [∘]ᴰ : Laᴰ [ Lσᴰ ∘ᴰ Lσᴰ' ]ᴰ ≡[ [∘] ]LTm (Laᴰ [ Lσᴰ ]ᴰ) [ Lσᴰ ]ᴰ
-- --         q[,]ᴰ : qᴰ [ Lσᴰ ,ᴰ Laᴰ ]ᴰ ≡[ q[,] ]LTm Laᴰ
      
-- --         lam[]ᴰ : (lamᴰ Laᴰ) [ Lσᴰ ]ᴰ ≡[ lam[] ]LTm lamᴰ (Laᴰ [ Lσᴰ ⁺ᴰ ]ᴰ)

-- --         Πηᴰ : lamᴰ (appᴰ Laᴰ) ≡[ Πη ]LTm Laᴰ
-- --         Πβᴰ : appᴰ (lamᴰ Laᴰ) ≡[ Πβ ]LTm Laᴰ
      
-- -- record Modelᴰ (m : Model) : Set1 where
-- --   open Model m
-- --   field
-- --     sᴰ : Sortsᴰ s c
-- --   open Sortsᴰ sᴰ public 
-- --   open InSortsᴰ s c sᴰ public 
-- --   field
-- --     cᴰ : InSortsᴰ.Ctorsᴰ s c sᴰ
-- --   open InSortsᴰ.Ctorsᴰ cᴰ public
        

-- -- -- Syntax

-- -- postulate
-- --   syn : Model
        
-- -- -- Induction

-- -- module Ind (mᴰ : Modelᴰ syn) where
-- --   open Model syn
-- --   open Modelᴰ mᴰ

-- --   postulate
-- --     ∃!Con : (LΓ : LCon) → LConᴰ LΓ
-- --     ∃!Sub : (Lσ : LSub LΓ LΔ) → LSubᴰ (∃!Con LΓ) (∃!Con LΔ) Lσ
-- --     ∃!Tm : (La : LTm LΓ) → LTmᴰ (∃!Con LΓ) La
    
-- --     ∃!∙ : ∃!Con ∙ ≡ ∙ᴰ
-- --     {-# REWRITE ∃!∙ #-}

-- --     ∃!, : ∃!Con (LΓ ,) ≡ (∃!Con LΓ) ,ᴰ
-- --     {-# REWRITE ∃!, #-}

-- --     ∃!id : ∃!Sub {LΓ} id ≡ idᴰ
-- --     {-# REWRITE ∃!id #-}

-- --     ∃!∘ : ∃!Sub (Lσ ∘ Lσ') ≡ ∃!Sub Lσ ∘ᴰ ∃!Sub Lσ'  
-- --     {-# REWRITE ∃!∘ #-}

-- --     ∃!ε : ∃!Sub {LΓ} ε ≡ εᴰ
-- --     {-# REWRITE ∃!ε #-}

-- --     ∃!p : ∃!Sub (p {LΓ}) ≡ pᴰ
-- --     {-# REWRITE ∃!p #-}

-- --     ∃!q : ∃!Tm (q {LΓ}) ≡ qᴰ
-- --     {-# REWRITE ∃!q #-}

-- --     ∃![] : ∃!Tm (La [ Lσ ]) ≡ (∃!Tm La) [ ∃!Sub Lσ ]ᴰ
-- --     {-# REWRITE ∃![] #-}

-- --     ∃!lam : ∃!Tm (lam La) ≡ lamᴰ (∃!Tm La)
-- --     {-# REWRITE ∃!lam #-}

-- --     ∃!app : ∃!Tm (app La) ≡ appᴰ (∃!Tm La)
-- --     {-# REWRITE ∃!app #-}