# TODO

- Finish up the work on principal cycles (RiemannRoch.AlgebraicCycle.Principal.lean):
  - 1 Finish the proof that the `div` function is locally finite ✓

  - 3 Finish the proof that the `principalCycle` function is locally finite

  - 1 Finish the proof of `div_homomorphism` ✓

  - 2 PR principal divisors stuff

  - 3 Get rational equivalence stuff done

- Flesh out work on divisors (RiemannRoch.Divisor.lean):
  - 1 Construct the presheaf of modules associated to a divisor

  - 1 Show this is a sheaf by appealing to the fact that it is a subpresheaf of K

  - 2 Finish the proof that our tensor product construction gives the expected result on line
      line bundles (I.e. that O(D + D') = O(D) \tensor O(D')).

  - 2 Write the general definition of the tensor product of subpresheaves of K.
    - Note that I think it's important here to continue working with integral schemes, and hence
      for K to be a constant sheaf on the nose. This is because the definition I have in mind
      is that sections s of F \tensor G are locally given by products of sections sf of F and
      sections sg of G, where sf*sg is taken literally to be the product of the underlying rational
      functions.

      Maybe we should define a kind of sheaf that is of the form
      L(U) = {s : X.functionField | P U s} for some predicate P (that may depend on the open U).
      Then we define the notion of tensor product on sheaves of this form using the definition
      we have come up with already. Is it then the case that if L and L' are sheaves of this form,
      then their tensor product in this sense is a sheaf? I think that should definitely be the
      case.

      So we have a couple of questions. What conditions do we want on P, and should we write a
      library talking about these things as sheaves of rings or as sheaves of modules?

      Well, we probably want sheaves of modules, because ultimately we want this notion to come
      with the right kind of morphisms.

      I also want to know if this family of sheaves is closed under taking quotients. I.e. is
      O_D such a sheaf? Well, again being very simple minded, this is precisely the regular
      functions which vanish at D, i.e. which have (f) = D in some U or something.

      For this to work and be actually useful, we're going to need to define the quotient of such
      sheaves in some concrete way then show that whatever construction we come up with has some
      nice exact sequence associated to it.

      Ok, at this point I thought the kinds of sheaves we were defining should have been closed 
      under quotients. This seems unlikely to me, like demanding that quotients be subrings. This 
      presents a slight problem, because I'd really like to be able to twist exact sequences by the
      tensor product operation we're trying to define.

      So maybe this class of sheaves is not big enough unfortunately. 

      Do we strictly need a tensor product operation? We only need that 
      0 -> O(D - D') -> O(D) -> O_D' -> 0 for effective D'. This may be provable without a tensor
      product directly. 


      Here is an attempt:-

      - f : O(D - D') -> O(D)
        f_U (h) = h (since h + D - D' \geq 0, so h + D \geq D', and D' \geq 0 by assumption)
        
        For O_D', I suppose we have at our disposal some quotient map q : O/I -> O_D'
        g : O(D) -> O_D'
        g_U (h) = ?? Again is seems like we need that damn tensor product.


      Maybe we really do want to define tensoring not with respect to 



      

      Again, I'm inclined to just try the old "sheafification by putting the word locally
      everywhere" trick and see if that gets us anywhere.

      I.e. If I guess q implies p, 
      F_p \quotient F_q (U) = {s : X.functionField | p \and \not q} or something.

      Does this work for the only example we care about, O and O(-D)?

      O \quotient O(-D) (U) = {s : X.functionField | true and s \neq 0 \implies \not s vanishes on D}

      I'm not so sure about that. If D is 0, then we have that the functions that are defined at
      0 are the functions which don't vanish at 0. But this does not equate the functions
      1 and 1+x, even though they should be equal here. Indeed, if we want this to work with just
      conditions. 

      What should O \quotient O(-0) be? It should be precisely those functions which vanish at 0.
      So 

      Ok, let's work backwards, let's try and construct it directly:
    
      O \quotient O(-D) (U) := {s : X.functionField | s /= 0 -> }


After the above work we should have working notion of what it means to take a tensor product of line
bundles, and the way we've done it should be incredibly useful for real applications.


- Cech cohomology (RiemannRoch.CechCohomology.lean)
  - 2 Using Kenny's definition, state and sorry that Cech cohomology can be computed wrt a
    single affine open cover on a separated scheme
  -
  - 2 Try to state some properties of the Euler characteristic (like how it's additive on short
    exact sequences).



- Big picture (RiemannRoch.RiemannRoch.lean)
  - 2 We now have a statement for Riemann Roch, but it would be good to have a proof skeleton
  -
