
# Variations of 'layered' type theory for computational features

## Refresher on CwFs

A category with families is a category `C` with a terminal object, two
presheaves `Tm` and `Ty` over `C`, and a representable map of presheaves
`p : Tm → Ty`.
Representable map means that the pullback of `typeof` along any
`A : y Γ → Ty` exists and is a representable object, which we denote `y (Γ, A)` --- 'context extension'.

A strict morphism of CwFs `(C, pC) → (D, pD)` is a terminal-object-preserving
functor `F : C → D` along with two natural transformations `TmC → F* TmD` and
`TyC → F* TyD` which commute with `pC` and `F* pD`, such that context extension
is preserved `F* (y (Γ , A)) = y (F Γ , FTy A)`.

There is a category `CwF` of categories with families and strict morphisms between them.

## Layered type theories

A layered CwF is a diagram of CwFs, given by:

- A small 'index' category `I`
- A functor `T : I^op → CwF`

> This is a similar but weaker notion than that of models of 'modal type theory'
> in the sense of Gratzer et al, in the sense that we do not require modalities
> in the form of dependent right adjoints to be present.

A layered type theory is a type theory which has layered CwFs as models.

Unfortunately, nice logical frameworks such as SOGATs do not suffice to produce
all layered CwF models. It would be nice to have a generalisation of SOGATs for
this.

For an index category `I`, we have a category of models `LMod I` of layered type
theory, where the objects are `I`-diagrams of CwFs and the morphisms are
(weak?) morphisms of `I`-diagrams of CwFs.

Claim: The initial object of `LMod I` is given by `T A = C` where `C` is the
initial CwF, and `T f = id`.

## Basic examples

The basic (and least interesting) version of this is the initial layered CwF
over the interval category `0->1`: This is a model of layered type theory with
two levels. In level `0`, we have standard type theory

```
Con0 : Set
Sub0 : Con0 → Con0 → Set
Ty0 : Con0 → Set
Tm0 : ∀ Γ0 . Ty0 Γ0 → Set
...
```

and in level `1` we have type theory displayed over 'itself'

```
Con1 : Con0 → Set
Sub1 : ∀ Γ0 Δ0 . Con1 Γ0 → Con1 Δ0 → Sub0 Γ0 Δ0 → Set
Ty1 : ∀ Γ0 . Con1 Γ0 → Ty0 Γ0 → Set
Tm1 : ∀ Γ0 Γ1 . Ty1 Γ1 A0 → Tm0 Γ0 A0 → Set
...
```

where all these sets are defined quotient-inductive-inductively by all the
standard substitution calculus constructors and their displayed conterparts.
Indeed, the generalised algebraic theory defining this quotient-inductive type
*is* `0->1`-layered type theory. More generally, the theory defining the
quotient-inductive-inductive type of the free `I`-layered CwF *is* `I`-layered
type theory.

Note that this syntactic presentation as a generalised algebraic theory utilises
the 'displayed' rather than 'fibered' style, because this is is a more
structural formulation that is much more convenient to work with (at least in
proof assistants). The other alternative is to have a functor `F` between the
levels, calculating the indices of level 1. Note that the displayed style is
only really viable for index categories `I` which are *trees*, because this
allows us to take the pre-image of every CwF morphism and make a displayed CwF
out of it. For more complicated index categories we must use the fibered style.
We can go back and forth between the styles using the pre-image and total space
constructions.


## Quantitative type theory (simplified)

Certain instantiations of quantitative type theory in the sense of Atkey can be
thought of as layered type theories. Admittedly, these instantiations are very
special: they are the ones whose substitution calculus does not posess any
sub-structuctural properties. One example is QTT over the trivial semiring, but
this is not interesting because it is just MLTT. The other example is over the
semiring `{0, ω}`, which is the type theory Agda is based on, and leads to a
notion of computational irrelevance.