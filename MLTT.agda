{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
  using (_≡_; isSet; transport; cong; sym; transp; i0; i1; PathP; I)
  renaming (_∙_ to _■_)

-- CWF sorts
data Con : Set
data Ty : Con → Set
data Sub : Con → Con → Set
data Tm : ∀ Γ → Ty Γ → Set

variable  
  Γ Γ' Δ Δ' : Con
  A A' B B' : Ty _
  a a' b b' : Tm _ _
  σ σ' σ'' : Sub _ _

-- CWF constructors and equations

coe : A ≡ B → Tm Γ A → Tm Γ B

PathP-syntax : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
PathP-syntax = PathP

syntax PathP-syntax A a b = a ≡[ A ] b

data Con where
  ∙ : Con
  _,_ : ∀ Γ → Ty Γ → Con

_[_]T : Ty Δ → Sub Γ Δ → Ty Γ
_[_]t : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)

id' : Sub Γ Γ
_∘'_ : Sub Γ Γ' → Sub Δ Γ → Sub Δ Γ'
[∘]' : (A [ σ ]T) [ σ' ]T ≡ A [ σ ∘' σ' ]T
p' : Sub (Γ , A) Γ
q' : Tm (Γ , A) (A [ p' ]T)
  
data Sub where
  Sub-isSet : isSet (Sub Δ Γ)

  id : Sub Γ Γ
  _∘_ : Sub Γ Γ' → Sub Δ Γ → Sub Δ Γ'
  ∘assoc : σ ∘ (σ' ∘ σ'') ≡ (σ ∘ σ') ∘ σ''
  ∘id : σ ∘ id ≡ σ
  id∘ : id ∘ σ ≡ σ

  p : Sub (Γ , A) Γ
  _,_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ , A)
  ,∘ : (σ , a) ∘ σ' ≡ ((σ ∘' σ') , (coe [∘]' (a [ σ' ]t)))
  p∘, : p ∘ (σ , a) ≡ σ
  p,q : (p' {A = A} , q') ≡ id

  ε : Sub Γ ∙
  ε∘ : ε ∘ σ ≡ ε
  id-ε : id ≡ ε
  
↑ : (σ : Sub Γ Δ) → Sub (Γ , (A [ σ ]T)) (Δ , A)
↑ σ = (σ ∘' p') , coe [∘]' q'

id' = id
_∘'_ = _∘_
p' = p
  
data Ty where
  Ty-isSet : isSet (Ty Γ)

  _[_] : Ty Δ → Sub Γ Δ → Ty Γ
  [id] : A [ id ]T ≡ A
  [∘] : A [ σ ]T [ σ' ]T ≡ A [ σ ∘ σ' ]T

  U : Ty Γ
  U[] : U [ σ ]T ≡ U

  El : Tm Γ U → Ty Γ
  El[] : (El a) [ σ ]T ≡ El (coe U[] (a [ σ ]t))

  Π : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  Π[] : (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ ↑ σ ]T)
  
_[_]T = _[_]
[∘]' = [∘]

data Tm where
  Tm-isSet : isSet (Tm Γ A)
  
  coerce : A ≡ B → Tm Γ A → Tm Γ B

  _[_] : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
  [id] : coe [id] (a [ id ]t) ≡ a
  [∘] : coe [∘] (a [ σ ]t [ σ' ]t) ≡ a [ σ ∘ σ' ]t

  q : Tm (Γ , A) (A [ p ])
  q[,] : coe ([∘] ■ λ i → A [ p∘, {a = a} i ]) (q {A = A} [ σ , a ]) ≡ a
  
  lam : Tm (Γ , A) B → Tm Γ (Π A B)
  app : Tm Γ (Π A B) → Tm (Γ , A) B 
  lam[] : coe Π[] ((lam a) [ σ ]) ≡ lam (a [ ↑ σ ])
  
_[_]t = _[_]
q' = q

coe = coerce