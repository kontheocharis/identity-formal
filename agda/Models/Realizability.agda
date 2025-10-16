module Models.Realizability where

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Induction renaming (rec to recursion)
open import Data.Fin using (Fin; suc) renaming (zero to f0)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; [_]; []; _∷_; lookup; map; tabulate; head)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst; sym)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

open import Model
open import Realizability
open import Utils

record PCA+ (A : PCA) : Set1 where
  open Realizability.Relations A
  field
    ZERO : ∣ A ∣
    SUCC : ∣ A ∣
    REC : ∣ A ∣

module OverPCA+ (A : PCA) (A+ : PCA+ A) where
  open Realizability.Relations A public
  open PCA+ A+
  
  -- record SubCᴿ (ΓCᴿ : ℕ) (ΔCᴿ : ℕ) : Set1 where
  --   field
  --     ∣_∣ : ∣ A ∣^ ΓCᴿ → Set
  --     real : (a : ∣ A ∣^ ΓCᴿ) → ∣_∣ a → ∣ A ∣^ 1
  
  record TmCᴿ (ΓCᴿ : ℕ) : Set1 where
    field
      ∣_∣ : Set
      real : (a : ∣ A ∣^ ΓCᴿ) → ∣_∣ → ∣ A ∣^ 1

  open TmCᴿ public

  record TmCᴿ≡ {ΓCᴿ : ℕ} (a : TmCᴿ ΓCᴿ) (b : TmCᴿ ΓCᴿ) : Set1 where
    field
      ∣_∣≡ : a .∣_∣ ≡ b .∣_∣
      real≡ : ∀ x pa → a .real x pa ≡ b .real x (subst (λ s → s) ∣_∣≡ pa)
      
  TmCᴿ-cong : ∀ {ΓCᴿ} {a b : TmCᴿ ΓCᴿ} → TmCᴿ≡ a b → a ≡ b

  record Conᴿ (ΓLᴿ : Set) (ΓCᴿ : ℕ) : Set1 where
    field
      ∣_∣ : ΓLᴿ → Set
      _ᴿᴿ : RRel ΓCᴿ (Σ[ γ ∈ ΓLᴿ ] ∣_∣ γ)
      total : Total _ᴿᴿ
      -- cart : ΓCᴿ -Cart _ᴿᴿ
      
  open Conᴿ

  -- record Subᴿ {ΓLᴿ ΓCᴿ ΔLᴿ ΔCᴿ}
  --   (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
  --   (Δᴿ : Conᴿ ΔLᴿ ΔCᴿ)
  --   (σLᴿ : ΓLᴿ → ΔLᴿ) : Set where
  --   field
  --     ∣_∣ : ∀ γ → ∣ Γᴿ ∣ γ → ∣ Δᴿ ∣ (σLᴿ γ)
  --     _ᵀᴿ : Tracked (λ (γ , γ') → (σLᴿ γ , ∣_∣ γ γ')) σCᴿ (Γᴿ ᴿᴿ) (λ _ → Δᴿ ᴿᴿ)

  -- open Subᴿ public

  record Tyᴿ (ΓLᴿ : Set) : Set1 where
    field
      ∣_∣ : ΓLᴿ → Set
      ∣_∣⁺ : ∀ γ → ∣_∣ γ → Set
      _ᴿᴿ : ∀ γ → RRel 1 (Σ[ t ∈ ∣_∣ γ ] ∣_∣⁺ γ t)
      total : ∀ γ  → Total (_ᴿᴿ γ)

  open Tyᴿ public

  record Tmᴿ {ΓLᴿ ΓCᴿ}
    (Γᴿ : Conᴿ ΓLᴿ ΓCᴿ)
    (Tᴿ : Tyᴿ ΓLᴿ)
    (aLᴿ : (γ : ΓLᴿ) → ∣ Tᴿ ∣ γ)
    (aCᴿ : TmCᴿ ΓCᴿ) : Set where
    field
      ∣_∣ : ∀ γ (γ' : ∣ Γᴿ ∣ γ) → ∣ Tᴿ ∣⁺ γ (aLᴿ γ)
      _ᵀᴿ : ∃Tracked (λ (γ , γ') → (aLᴿ γ , ∣_∣ γ γ')) (Γᴿ ᴿᴿ) (λ (γ , γ') → (Tᴿ ᴿᴿ) γ)


  open Tmᴿ public
  
  open TT-Logic
  open TT-Comp
  open TT
  
  is-num : ∣ A ∣^ 1 → Set
  
  recursor : ∣ A ∣^ 1 → (∣ A ∣^ 1 → ∣ A ∣^ 1) → ∣ A ∣^ 1 → ∣ A ∣^ 1
  numzero : ∣ A ∣^ 1
  numsucc : ∣ A ∣^ 1 → ∣ A ∣^ 1
  
  RC : TT-Comp
  RC .ConC = ℕ
  RC .TmC ΓC = TmCᴿ ΓC
  RC .∙C = 0
  (RC ▷C) Γ = suc Γ
  ∣ RC .qC ∣ = ⊤
  RC .qC .real (x₁ ∷ a) x = [ x₁ ] -- v f0
  ∣ RC .wkC x ∣ = ∣ x ∣
  RC .wkC x .real (x₂ ∷ a) x₁ = x .real a x₁
  ∣ RC .openC x ∣ = ∣ x ∣
  RC .openC x .real a x₁ = x .real [] x₁
  ∣ (RC [ x ]C) x₁ ∣ = ∣ x ∣ × ∣ x₁ ∣
  (RC [ x ]C) x₁ .real a (xp , x₁p) = x .real (head (x₁ .real a x₁p) ∷ a) xp
  ∣ RC .lamC x ∣ = {!   !}
  RC .lamC x .real = {!   !} -- Λ' x
  RC .appC x y = {!   !} -- x ∙' y
  RC .unit = {!   !} -- ⌜ I ⌝
  ∣ RC .zeroC ∣ = ⊤
  RC .zeroC .real a x = numzero -- ⌜ ZERO ⌝
  ∣ RC .succC n ∣ = ∣ n ∣
  RC .succC n .real = {!   !} -- ⌜ SUCC ⌝ ∙' n
  ∣ RC .recC z s n ∣ = ∣ z ∣ × ∣ s ∣ × ∣ n ∣ × (∀ γ p → is-num (n .real γ p))
  RC .recC z s n .real a (zp , sp , np , _)
    = recursor (z .real a zp) (λ s' → s .real (head s' ∷ a) sp) (n .real a np) -- ((⌜ REC ⌝ ∙' z) ∙' Λ' s) ∙' n
  RC .recC-η1 = TmCᴿ-cong (record { ∣_∣≡ = {!   !} ; real≡ = {!   !}  }) -- {!   !}
  RC .recC-β-zero = {!   !}
  RC .recC-β-succ = {!   !}
  
  nat-rec : (P : ℕ → Set) → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
  nat-rec P z s ℕ.zero = z
  nat-rec P z s (suc n) = s n (nat-rec P z s n)

  RL : TT-Logic
  RL .comp = RC
  RL .ConL = Set
  RL .SubL ΓL ΔL = ΓL → ΔL
  RL .Ty ΓL = Tyᴿ ΓL
  RL .TmL ΓL T = (γ : ΓL) → ∣ T ∣ γ
  RL .idL x = x
  (RL ∘L σ) τ x = σ (τ x)
  RL .assocL = refl
  RL .∘idL = refl
  RL .idL∘ = refl
  ∣ (RL [ T ]T) σ ∣ γ = ∣ T ∣ (σ γ)
  ∣ (RL [ T ]T) σ ∣⁺ γ = ∣ T ∣⁺ (σ γ)
  ((RL [ T ]T) σ ᴿᴿ) γ a (t , t') = a ⊩[ (T ᴿᴿ) (σ γ) ] (t , t')
  (RL [ T ]T) σ .total γ = T .total (σ γ)
  (RL [ t ]L) σ γ = t (σ γ)
  RL .[id]T = refl
  RL .[id]L = refl
  RL .[∘]T = refl
  RL .[∘]L = refl
  RL .∙L = ⊤
  RL .εL _ = tt
  RL .∃!εL σ = refl
  (RL ▷L ΓL) A = Σ[ γ ∈ ΓL ] ∣ A ∣ γ
  RL .pL (γ , a) = γ
  RL .qL  (γ , a) = a
  (RL ,L σ) a γ = σ γ , a γ
  RL .,L∘ = refl
  RL .pL,qL = refl
  RL .pL∘, = refl
  RL .qL[,] = refl
  ∣ RL .Π X Y ∣ γ = (x : ∣ X ∣ γ) → ∣ Y ∣ (γ , x)
  ∣ RL .Π X Y ∣⁺ γ f
    = Σ[ f' ∈ (∀ {x} (x' : ∣ X ∣⁺ γ x) → ∣ Y ∣⁺ (γ , x) (f x)) ]
      (∃Tracked (λ (x , x') → f x , f' x') ((X ᴿᴿ) γ) (λ (t , t') → (Y ᴿᴿ) (γ , t)))
  RL .Π X Y ᴿᴿ = {!   !}
  RL .Π X Y .total = {!   !}
  RL .Π[] = {!   !}
  RL .lamL f γ t = f (γ , t)
  RL .lamL[] = {!   !}
  RL .apL z (γ , a) = z γ a
  RL .βL t = refl
  RL .ηL t = refl
  RL .U = {!   !}
  RL .U[] = {!   !}
  RL .El = {!   !}
  RL .El[] = {!   !}
  ∣ RL .Nat ∣ γ = ℕ
  ∣ RL .Nat ∣⁺ γ x = ⊤
  (RL .Nat ᴿᴿ) γ x x₁ = {!   !}
  RL .Nat .total = {!   !}
  RL .Nat[] = {!   !}
  RL .zeroL γ = 0
  RL .zeroL[] = {!   !}
  RL .succL n γ = suc (n γ)
  RL .succL[] = {!   !}
  RL .recL P z s n γ = nat-rec (λ _ → ∣ P ∣ γ) (z γ) (λ _ k → s (γ , k)) (n γ)
  RL .recL[] = {!   !}
  RL .Spec = {!   !}
  RL .specL = {!   !}
  RL .unspecL = {!   !}
  RL .specL-unspecL = {!   !}
  RL .unspecL-specL = {!   !}

  R : TT
  -- R .logic = RL
  -- R .Con ΓL ΓC = Conᴿ ΓL ΓC
  -- R .Tm Γ A aL aC = Tmᴿ Γ A aL aC
  -- ∣ R .∙ ∣ tt = ⊤
  -- (R .∙ ᴿᴿ) [] (tt , tt) = ⊤
  -- R .∙ .total x = [] , tt
  -- ∣ (R ▷ Γ) T ∣ (γ , a) = Σ[ γ' ∈ ∣ Γ ∣ γ ] ∣ T ∣⁺ γ a
  -- ((R ▷ Γ) T ᴿᴿ) (tR ∷ γR) ((γ , t) , γ' , t')
  --   = (γR ⊩[ Γ ᴿᴿ ] (γ , γ')) × ([ tR ] ⊩[ (T ᴿᴿ) γ ] (t , t'))
  -- (R ▷ Γ) T .total ((γ , t) , (γ' , t')) with (Γ .total (γ , γ')) | (T .total γ (t , t'))
  -- ... | γTR , γTotal | (tTR ∷ []) , tTotal
  --     = tTR ∷ γTR , γTotal , tTotal
  -- ∣ (R ▷0 Γ) T ∣ (γ , t) = ∣ Γ ∣ γ
  -- ((R ▷0 Γ) T ᴿᴿ) a ((γ , t) , γ') = (Γ ᴿᴿ) a (γ , γ')
  -- (R ▷0 Γ) T .total ((γ , t) , γ') = Γ .total (γ , γ')
  -- ∣ R .q ∣ (γ , a) (γ' , a') = a'
  -- (R .q ᵀᴿ) ((γ , a) , γ' , a') (aTR ∷ γTR) (γRR , aRR) = def aTR ∷ [] , aRR
  -- ∣ (R [p]) t ∣ (γ , a) (γ' , a') = ∣ t ∣ γ γ'
  -- ((R [p]) t ᵀᴿ) ((γ , a) , γ' , a') (aTR ∷ γTR) (γRR , aRR) = {!   !} , {!   !} 
  -- R .lam = {!   !}
  -- R .app = {!   !}
  -- R .zero = {!   !}
  -- R .succ = {!   !}
  -- ∣ R .rec {P = P} {zL = zL} {sL = sL} {nL = nL} z s n ∣ γ γ'
  --   = nat-rec (λ k → ∣ P ∣⁺ γ (nat-rec (λ _ → ∣ P ∣ γ) (zL γ) (λ _ i → sL (γ , i)) k))
  --     (∣ z ∣ γ γ')
  --     (λ n₁ z₁ → ∣ s ∣ (γ , nat-rec (λ _ → ∣ P ∣ γ) (zL γ) (λ _ i → sL (γ , i)) n₁) (γ' , z₁))
  --     (nL γ)
  -- (R .rec {P = P} {zL = zL} {sL = sL} {nL = nL} z s n ᵀᴿ) (γ , γ') γTR γRR
  --   = {!   !} , {!   !}
  -- R .spec = {!   !}
  -- R .unspec = {!   !}


--   R .TT.ConL = Set
--   R .TT.ConC = ℕ
--   R .TT.Con ΓLᴿ ΓCᴿ = Conᴿ ΓLᴿ ΓCᴿ

--   R .TT.SubL ΓLᴿ ΔLᴿ = ΓLᴿ → ΔLᴿ
--   R .TT.SubC ΓCᴿ ΔCᴿ = ∣ A [ ΓCᴿ ]∣^ ΔCᴿ
--   R .TT.Sub Γᴿ Δᴿ σLᴿ σCᴿ = Subᴿ Γᴿ Δᴿ σLᴿ σCᴿ

--   R .TT.TyL ΓLᴿ = ΓLᴿ → Set
--   R .TT.TmL ΓLᴿ TLᴿ = (γ : ΓLᴿ) → TLᴿ γ

--   R .TT.TmC ΓCᴿ = ∣ A [ ΓCᴿ ]∣

--   R .TT.Ty ΓLᴿ TLᴿ = Tyᴿ ΓLᴿ TLᴿ
--   R .TT.Tm Γᴿ Tᴿ aLᴿ aCᴿ = Tmᴿ Γᴿ Tᴿ aLᴿ aCᴿ
  
--   R .TT.∙L = ⊤
--   (R TT.▷L ΓLᴿ) TLᴿ = Σ[ γ ∈ ΓLᴿ ] TLᴿ γ
  
--   R .TT.∙C = zero
--   R TT.▷C = suc
  
--   ∣ R .TT.∙ ∣ tt = ⊤
--   (R .TT.∙ ᴿᴿ) [] (tt , tt) = ⊤
--   ∣ (R TT.▷ Γᴿ) Tᴿ ∣ (γ , t) = Σ[ γ' ∈ ∣ Γᴿ ∣ γ ] ∣ Tᴿ ∣ γ t
--   ((R TT.▷ Γᴿ) Tᴿ ᴿᴿ) (tR ∷ γR) ((γ , t) , γ' , t')
--     = (γR ⊩[ Γᴿ ᴿᴿ ] (γ , γ')) × ([ tR ] ⊩[ (Tᴿ ᴿᴿ) γ ] (t , t'))
--   ∣ (R TT.▷0 Γᴿ) TLᴿ ∣ (γ , t) = ∣ Γᴿ ∣ γ
--   ((R TT.▷0 Γᴿ) TLᴿ ᴿᴿ) a ((γ , t) , γ') = (Γᴿ ᴿᴿ) a (γ , γ')
  
--   R .TT.∙ .total _ = [] , tt
--   (R TT.▷ Γ) T .total ((γ , t) , (γ' , t')) with (Γ .total (γ , γ')) | (T .total γ (t , t'))
--   ... | γTR , γTotal | (tTR ∷ []) , tTotal
--       = tTR ∷ γTR , γTotal , tTotal
--   (R TT.▷0 Γ) T .total ((γ , t) , γ') = Γ .total (γ , γ')

--   (R TT.[p*]) {ΓC = n} t = opn t
  
--   R .TT._[_]TL TLᴿ σLᴿ γ = TLᴿ (σLᴿ γ)
--   ∣ (R TT.[ Tᴿ ]T) σLᴿ ∣ γ = ∣ Tᴿ ∣ (σLᴿ γ)
--   ((R TT.[ Tᴿ ]T) σLᴿ ᴿᴿ) γ a (t , t') = a ⊩[ (Tᴿ ᴿᴿ) (σLᴿ γ) ] (t , t')
--   (R TT.[ Tᴿ ]T) σLᴿ .total γ = Tᴿ .total (σLᴿ γ)

--   R .TT._[_]L tLᴿ σLᴿ γ = tLᴿ (σLᴿ γ)
--   R .TT.idL γ = γ
--   R .TT._,L_ σLᴿ tLᴿ γ = σLᴿ γ , tLᴿ γ

--   R .TT.ΠL TLᴿ ULᴿ γ = (t : TLᴿ γ) → ULᴿ (γ , t)
--   R .TT.lamL t γ t₁ = t (γ , t₁)
--   R .TT.apL x (γ , t) = x γ t
--   R .TT.βL t = refl
--   R .TT.ηL t = refl
  
--   R .TT.lamC x = Λ' x
--   R .TT.appC x y = x ∙' y
  
--   ∣ R .TT.Π T U ∣ γ t
--     = Σ[ t' ∈ (∀ x (x' : ∣ T ∣ γ x) → ∣ U ∣ (γ , x) (t x)) ]
--         (∃Tracked (λ (x , x') → t x , t' x x') ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t)))
--   (R .TT.Π T U ᴿᴿ) γ (a ∷ []) (f , f' , (_ , p))
--     = Tracked (λ (x , x') → f x , f' x x') [ ⌜ a ⌝ ∙' v zero ] ((T ᴿᴿ) γ) (λ (t , t') → (U ᴿᴿ) (γ , t))
--   -- R .TT.Π T U .total γ (f , f' , (l , p)) = [ {!   !} ] , {!  p !}
--   -- ∣ R .TT.lam {tC = tC} record { ∣_∣ = ∣t∣ ; _ᵀᴿ = tᵀᴿ } ∣ γ γ'
--   --   = ((λ x x' → ∣t∣ (γ , x) (γ' , x')) , {!   !} )
--   --     -- (∃-rec (t ᵀᴿ) (λ a' p → a' , -- ΠAⱽ tC (a' , p .fst) ,
--   --     --   λ (t , t') a tTR → let m = p .snd ((γ , t) , γ' , t') in m a {!   !}))
--   --     -- (∃-elim (λ ex → ∃Tracked (λ (x , x') → {!   !} x , {!   !} x x') {!   !} {!   !}) (t ᵀᴿ) (λ r s → {!   !} , λ (γ , t) a tr → {!   !}))
--   -- R .TT.lam t ᵀᴿ = {!   !}
--   -- ∣ R .TT.app {tL = tL} f x ∣ γ γ' = ∣ f ∣ γ γ' .proj₁ (tL γ) (∣ x ∣ γ γ')
--   -- R .TT.app record { ∣_∣ = ∣f∣ ; _ᵀᴿ = fᵀᴿ } record { ∣_∣ = ∣x∣ ; _ᵀᴿ = xᵀᴿ } ᵀᴿ
--   --   = {!   !}
  

--   ∣ R .TT.Spec {ΓL = ΓLᴿ} T c ∣ γ t
--     = Σ[ t' ∈ (∣ T ∣ γ t) ] ([ extract c ] !⊩[ (T ᴿᴿ) γ ] (t , t'))
--   (R .TT.Spec T c ᴿᴿ) γ a (t , t' , p) = extract c ≡ just (Data.Vec.head a)
--   R .TT.Spec T c .total γ (t , t' , (c↓ ∷ []) , p) = [ _ ↓by c↓ ] , def-id c↓
--   ∣ R .TT.spec {ΓC = ΓC} {Γ = Γ} {T = T} {aC = aC} t ∣ γ γ'
--     = ∣ t ∣ γ γ' ,
--         let (γTR , γTotal) = Γ .total (γ , γ') in 
--         (t ᵀᴿ) (γ , γ') γTR γTotal
--   (R .TT.spec {ΓC = ΓC} {Γ = Γ} {aC = aC} t ᵀᴿ) (γ , γ') a p
--     with Γ .total (γ , γ')
--   ... | (γTR , γTotal) with (t ᵀᴿ) (γ , γ') γTR γTotal
--   ... | (aC↓ ∷ [] , tTotal) = aC↓ ∷ [] , def-id aC↓
--   ∣ R .TT.unspec t ∣ γ γ' = proj₁ (∣ t ∣ γ γ')
--   (R .TT.unspec {T = T} {aC = aC} t ᵀᴿ) (γ , γ') a p = ∣ t ∣ γ γ' .proj₂
  
  
-- module Results (A : PCA) where
--   open OverPCA A
--   open TT R
  
--   -- The interpretation of a term in the empty context
--   -- produces a defined element of the PCA
--   lem1 : ∀ {TL} {T : Ty ∙L TL} {c t}
--     → Tm (∙) T t c
--     → extract c ↓
--   lem1 t with el ∷ [] , tr ← (t ᵀᴿ) (tt , tt) [] tt = el

--   -- In particular, every Spec term in the empty context
--   -- is annotated by a defined element of the PCA
--   lem2 : ∀ {TL} {T : Ty ∙L TL} {c c' t}
--     → Tm (∙) (Spec T c) t c'
--     → extract c ↓
--   lem2 t = lem1 (unspec t)

--   -- The 'meaning' interpretation of a term in the empty context
--   -- is tracked by its PCA element
--   lem3 : ∀ {TL} {T : Ty ∙L TL} {c t}
--     → (t' : Tm (∙) T t c)
--     → [ extract c ↓by lem1 t' ] ⊩[ (T ᴿᴿ) tt ] (t tt , ∣ t' ∣ tt tt)
--   lem3 t' with el ∷ [] , tr ← (t' ᵀᴿ) (tt , tt) [] tt = tr

--   -- So for a Spec term in the empty context,
--   -- its annotated PCA element tracks its meaning interpretation
--   lem4 : ∀ {TL} {T : Ty ∙L TL} {c c' t}
--     → (t' : Tm (∙) (Spec T c) t c')
--     → [ extract c ↓by lem2 t' ] ⊩[ (T ᴿᴿ) tt ] (t tt , ∣ unspec t' ∣ tt tt)
--   lem4 t = lem3 (unspec t)