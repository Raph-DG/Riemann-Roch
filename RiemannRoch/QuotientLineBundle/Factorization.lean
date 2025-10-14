import Mathlib
import RiemannRoch.QuotientLineBundle.RationalDomain
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.Divisor
/-!

# Factorization of a section of 𝒪ₓ(D)

In this file, we define a factorization of a section of `𝒪ₓ(D)` into a product
`f * g` where `f` is a section of `𝒪ₓ` and `g` is a section of `𝒪ₓ(D)`, defined
such that the domain of definition of `f` is minimised.

We show the existence of such a factorization abstractly, via induction or Zorn or
something. We know we can always factorize such a thing using `f = 1`. Now, suppose
we could find some infinite descending chain `f₁, g₁`, `f₂, g₂`,... each with smaller domains
of definition. We know `d(f₁) ⊃ d(f₂) ⊃ ...` and `d(f₁) ∩ d(g₁) = d(f₂) ∩ d(g₂) = ...`
What does this tell us? Well, these chains are all bounded below by `d(f₁) ∩ d(g₁)`,
so does that give us what we want by Zorn?



The domains of definition of the `g`s must then be ascending?, since
the domain of definition of `f * g` is the domain of definition of `f` intersect the
domain of definition of `g`.
-/

#check zorn_le
#check zorn_superset_nonempty
#check IsChain

open AlgebraicGeometry Scheme

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)

def σ {D : AlgebraicCycle X} {U : X.Opens} (f : AlgebraicCycle.LineBundle.carrier D U) :
    Γ(X, U) × AlgebraicCycle.LineBundle.carrier D U := sorry

lemma σ_spec {D : AlgebraicCycle X} {U : X.Opens} [Nonempty U]
    (f : AlgebraicCycle.LineBundle.carrier D U) :
    (σ f).1 • (σ f).2 = f.1 := sorry

/-
Here we want to say something like "If we have "

lemma σ_spec' {D : AlgebraicCycle X} {U : X.Opens} [Nonempty U]
    (f : AlgebraicCycle.LineBundle.carrier D U) := sorry-/


/-
Once we have this factorisation `σ`, we define
`Γ(𝒪ₚ(D), U) := {s : Γ(𝒪ₓ(D), U) | ∀ z ∈ U, ∃ f' ∈ X.residueField p, σ(s|ᵥ).1 = ι f'}`
or something. I'm not sure if the local condition here is necessary but it seems safe.
Also, we should definitely come up with some better notation for just extracting this
factor `f`.

I suppose we could just define this to not necessarily be globally `𝒪ₓ(D)` sections but
just to be rational functions. This probably validates the local gluing stuff a bit
more. I think with that definition it will still be easy to show surjectivity I'm hoping.

So then our map will just send a section to `ι (σ(s).1) * σ(s).2` and that should work well
I'm hoping.

So we then get something like:
`Γ(𝒪ₚ(D), U) := {s : X.functionField | ∀ z ∈ U, ∃ V ∈ X.Opens, z ∈ V ∧ s ∈ Γ(𝒪ₓ(D), V)`
`∧ ∃ f' ∈ X.residueField p, σ(s|ᵥ).1 = ι f'}`
This `s|v` notation is a bit sloppy, but the intention is that it's `s` thought of as a section in
`Γ(𝒪ₓ(D), V)` (which we can do by assumption, but we don't literally have a named proof
that `s ∈ Γ(𝒪ₓ(D), V)` so we .
-/

/-
Once we have this and the associated exact sequence, we still need to show a few things. First, we
need to show that `𝒪ₚ(D) = skyscraper k` if `p` is a closed point in a variety over `k`.

We then should be well and truly ready to start defining and proving properties about cohomology.
Hopefully we should get a lot of things for free, namely the associated long exact sequence.
I think we should try and get Kenny's definition working and make some sorried proof sketch
of RR using the fact that one can compute CC on an arbitrary affine cover and that projective curves
are covered by two affine pieces (I guess we can just prove this for schemes covered by 2 affine
pieces and bob's your uncle.
-/
