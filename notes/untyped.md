# Showing that optimisation rules are correct

It is not sufficient to equip OpTT with realisability semantics where the PCA is
somehow "quotiented" by the optimisation rules. For one, this is usually not
possible (for example `rec s zero succ ~> s` does not hold as an equality,
extensional/observational or otherwise, in untyped LC). Second, it doesn't
actually tell us much about the optimisation rules we have chosen. We must
somehow have criteria for admitting optimisation rules.

Let's consider OpTT (initial model) with a total model `T`, logical model `L`,
computational model `C`. `T` and `C` have no equations, `L` has the usual MLTT
equations. We also have functors `C <- T -> L` that preserve terms, types and
context structure as expected. We have a fixed PCA `A` with elements `|A|`. We
also have an interpretation of `C` in the PCA `A` which we denote
```
⟦_⟧ : ConC → ℕ
⟦_⟧ : Tm ΓC → |A|^⟦ΓC⟧
```

## Optimisation rules

Let us define an `n`-ary optimisation rule as 

```
Opt : (n : ℕ) → Set
Opt n = ∀ ΓC. (Tm ΓC)^n → (lhs : Tm ΓC) × (rhs : Tm ΓC)
```

So a function that takes `n` terms and gives the LHS and RHS of the optimisation
rule. For example,

```
nat-η : Opt 1
nat-η [s] = (rec s ze su, s)
```

However, not all values of `s` are good enough to have this optimisation rule apply
to them. For that, let's make a "typed" optimisation rule as

```
TOpt : (n : ℕ) → Set
TOpt n = (o : Opt n) × ((i : Fin n) → |A| → Prop)
```

An optimisation rule specifies for each argument, what realisers are "valid" for it. If
an argument is not tracked by a valid realiser, the optimisation rule shouldn't apply.

Finally, we have "verified" optimisation rules. These are typed optimisation rules where,
for each valid realiser of the arguments, the optimisation rule actually holds as an equality
in `A`.

```
VOpt : (n : ℕ) → Set
VOpt n = ((o, valid) : TOpt n)
       × ∀ ΓC. (args : (Tm ΓC)^n)
          → (γ : |A|^⟦ΓC⟧)
          → ((i : Fin n) → valid i ⟦args i⟧[γ])
          → ⟦(o args).lhs⟧[γ] = ⟦(o args).rhs⟧[γ]
```

> Lemma 1: `nat-η` is verified over the predicate of natural numbers, i.e. `λ a. ∃ k. a = succ^k zero` 


## Utilising optimisation rules

How can we make use of the optimisation rules we have, in the type system?

The first question we must ask ourselves is, will something bad happen if we
apply a verified optimisation rule to a subject which does *not* adhere to the
predicate?

Yes. Consider the rule

```
bad : VOpt 1
bad = (λ [s]. (s, ze) , λ a. a = zero , trivial)
```

It says "rewrite any s to zero" and only holds when "s = zero". If we apply this
without checking the domain, we can just rewrite every program to zero :D

So we must only apply optimisation rules when we *know* that the free terms
satisfy the requirements.

We can take advantage of the fact that every time we have a program in C, it originates
from a program in T. We basically need a type system! Solving this problem will require
figuring out how to "erase" dependent types while still retaining type information...


## Attempt 1: erasing dependent types to simpler types

Does erasure need to respect substitution? Normally yes, but we don't care about
any equational theory in T! Thus we might be able to get away without it..

Let's index total terms by logical terms only, and define this CwF morphism to C
explicitly.

```
-- SOGAT
TyC : U
TmC : TyC → Uᵣ

Nat : TyC
Unit : TyC
_⇒_ : TyC → TyC → TyC
* : TyC

(lam, app) : (TmC A → TmC B) ↔ TmC (A ⇒ B)
cast : (A B: TyC) → TmC A → TmC B
zero : TmC Nat
succ : TmC Nat → TmC Nat
tt : TmC Unit
rec : (A : TyC) → TmC Nat → (TmC Nat → TmC Nat) → TmC A → TmC A
```


```
|_| : T → C -- cwf morphism

|_| : ConT → ConC
|∙| = ∙
|Γ ,0 A| = |Γ|
|Γ , A| = |Γ| , *

|_| : TmT Γ A aL → (AC : TyC) × TmC |Γ| *
|q| = q
|x [p]| = |x|[p]
|lam x| = cast (* ⇒ *) * (lam |x|)
|app x y| = app (cast * (* ⇒ *) |x|) |y|
|zero| = cast Nat * zero
|succ x| = cast Nat * (succ (cast * Nat |x|))
|elim-Nat P z s n| = rec * (cast * Nat |z|) (cast * Nat |s|) |n|
```


So it seems if we have a cast operator, we can do this translation. However,
does this really help us? No.. it doesn't work

```
TyCᴿ = Asm
TmCᴿ Γ A = Γ ⇒ A

q : Γ × A ⇒ A
q (γ , a) = a

_[p] : (Γ ⇒ A) ⇒ (Γ × B ⇒ A)
(f [p]) (γ , b) = f γ

cast : (A B : Asm) ⇒ (Γ ⇒ A) ⇒ (Γ ⇒ B)
cast = ??
```


## Attempt 2: equality in the total theory only

```
TmC : Uᵣ
(lam, app) : (TmC → TmC) ↔ TmC
zero : TmC
succ : TmC → TmC
tt : TmC
rec : TmC → (TmC → TmC) → TmC → TmC
```

```
Tm : (Γ : Con ΓL ΓC) → (A : Ty ΓL) → TmL ΓL A → TmC ΓC → U

Num : (Γ : Con ΓL ΓC) → TmC ΓC → U
by-nat : Tm Γ Nat aL aC → Num Γ aC
by-fin : ∀ i. Tm Γ (Fin i) aL aC → Num Γ aC

_~>_ : (Γ : Con ΓL ΓC) → TmC ΓC → TmC ΓC → U
rec-η : Num Γ s → rec s ze su ~> s
-- + rfl,sym,trs

transp : aC ~> aC' → Tm Γ A aL aC → Tm Γ A aL aC'
```

```
TmCᴿ ΓC = |A[ΓC]|

record (A : Tyᴿ ΓL) : Set where
  |A| : |ΓL| → Set
  |A|⁺ : ∀ γ → |A| → Set
  _⊩[A γ]_ : RRel 1 (Σ (|A| γ) (|A|⁺ γ))

record (a : TmLᴿ ΓL A) : Set where
  |a| : (γ : |ΓL|) → |A| γ

record (a : Tmᴿ Γ A aL aC) : Set where
  |a|⁺ : ∀ γ (γ' : |ΓL|⁺ γ) → |A|⁺ γ (aL γ)
  TR a : ∀ γ γ'. ∀ g ⊩[Γ] (γ, γ') . aC ⋅ g ⊩[A γ] (|a| γ , |a|⁺ γ γ')
  
record (n : Num Γ aC) where
  TR n : ∀ γ γ'. ∀ g ⊩[Γ] (γ , γ') . ∃ v . aC ⋅ g ⊩[ℕ] v
  
record (p : Γ . aC ~> aC') : Set where
  eq p : ∀ γ γ' . ∀ g ⊩[Γ] (γ , γ') . (aC ⋅ g = aC' ⋅ g)
```

This seems to work... But its quite annoying because it is not trivial to decide it..

Examples:

```
last : (n : Nat) → Fin (succ n)
last zero = fzero
last (succ x) = fsucc (last x)
```

we have

```
last n = elim (λ n. Fin (succ n)) fzero (λ n ih. fsucc ih) n
```

so

```
|last| = |λ n. elim (λ n. Fin (succ n)) fzero (λ n ih. fsucc ih) n|
         = λ n. rec |fzero| |λ n ih. fsucc ih| |n|
         = λ n. rec ze (λ n ih. su ih) n
```

So if initially we had written

```
last n = transp (nat-η (by-nat n)) (elim (λ n. Fin (succ n)) fzero (λ n ih. fsucc ih) n)
```

it would typecheck because of the previous derivation, and would erase to `λ n. n`.

Questions:
- *When to insert these `transp` coercions?* Can we do it in a systematic/decidable way?
- Can `transp`, `_~>_` etc be internalised so that we can do proofs in the
  system (probably yes with 2LTT?)


### Internalising `transp`

First, let's slightly refine the type predicates. Let's instead have

```
Form : ConL → U
num : Form ΓL
fn : (A : Ty ΓL a) → Form (ΓL , A) → Form ΓL
none : Form ΓL
el : TmL ΓL U → Form ΓL

Ty : (ΓL : ConL) → Form ΓL → U
Nat : Ty ΓL num
Fin : TmL ΓL Nat → Ty ΓL num
Π : (A : Ty ΓL a) → Ty (ΓL , A) b → Ty ΓL (Π A B) (fn A b)
Unit : Ty ΓL none
U : Ty ΓL none
El : (u : TmL ΓL U) → Ty ΓL (el u)
```


Now the rules become

```
Red : (Γ : Con ΓL ΓC) → TmC ΓC → TmC ΓC → U
num-η : {A : Ty ΓL num} → Tm Γ A aL aC → Red Γ (rec aC ze su) aC
```


If we could get a decision procedure like
```
∀ a b. isContr (Red Γ a b) + (Red Γ a b → ⊥)
```
that would be really nice. (should only be for a subset of Red)

Question still remains: how to integrate Red nicely in the language.