# TODO

- Finish up the work on principal cycles (RiemannRoch.AlgebraicCycle.Principal.lean):
  - 1 Finish the proof that the `div` function is locally finite
  - 3 Finish the proof that the `principalCycle` function is locally finite
  - 1 Finish the proof of `div_homomorphism`

- Flesh out work on divisors (RiemannRoch.Divisor.lean):
  - 2 Develop API for the line bundle associated with a divisor
  - 2 Work out the best way to do tensor products of line bundles. There is a sketch of how to do
    this in a low tech way in the file, but it may be better to wait for more general machinery.
  -

- Cech cohomology (RiemannRoch.CechCohomology.lean)
  - Currently, all that is in the Cech Cohomology file is a sorried definition of the
    Euler characteristic. Kenny Lau et al are developing Cech cohomology in line with Joel's
    blueprint https://github.com/leanprover-community/mathlib4/compare/master...cech-experiment, so
    we should probably not develop too much more of this on our own.
  - 2 Try to state some properties of the Euler characteristic (like how it's additive on short
    exact sequences).

- Big picture (RiemannRoch.RiemannRoch.lean)
  - 2 We now have a statement for Riemann Roch, but it would be good to have a proof skeleton
  - For this, we need
