import Mathlib
import RiemannRoch.SheafOfModules.Subsheaf

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits


section Kenny
variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
  (F : Cᵒᵖ ⥤ AddCommGrp.{u₂}) (X : C) (J : Type u₂) (f : J → C) (φ : (j : J) → f j ⟶ X)

variable [∀ (n : ℕ), HasWidePullback (Arrow.mk (FormalCoproduct.homOfPiHom X f φ)).right
  (fun _ : Fin (n + 1) => (Arrow.mk (FormalCoproduct.homOfPiHom X f φ)).left)
  fun _ => (Arrow.mk (FormalCoproduct.homOfPiHom X f φ)).hom]
#check FormalCoproduct.homOfPiHom X f φ
#check Arrow.cechNerve (.mk <| FormalCoproduct.homOfPiHom X f φ)

#check Arrow.cechNerve (.mk <| FormalCoproduct.homOfPiHom X f φ)

#check (simplicialCosimplicialEquiv _).functor.obj
  (Opposite.op <| Arrow.cechNerve (.mk <| FormalCoproduct.homOfPiHom X f φ))

#check (FormalCoproduct.evalOp _ _).obj F

#check ((simplicialCosimplicialEquiv _).functor.obj
    (Opposite.op <| Arrow.cechNerve (.mk <| FormalCoproduct.homOfPiHom X f φ))) ⋙
  ((FormalCoproduct.evalOp _ _).obj F)

#check AlgebraicTopology.AlternatingCofaceMapComplex.obj
  (((simplicialCosimplicialEquiv _).functor.obj
      (Opposite.op <| Arrow.cechNerve (.mk <| FormalCoproduct.homOfPiHom X f φ))) ⋙
    ((FormalCoproduct.evalOp _ _).obj F))


noncomputable
def kennyCechComplex := (AlgebraicTopology.AlternatingCofaceMapComplex.obj
  (((simplicialCosimplicialEquiv _).functor.obj
      (Opposite.op <| Arrow.cechNerve (.mk <| FormalCoproduct.homOfPiHom X f φ))) ⋙
    ((FormalCoproduct.evalOp _ _).obj F)))

noncomputable
def kennyCech := (AlgebraicTopology.AlternatingCofaceMapComplex.obj
  (((simplicialCosimplicialEquiv _).functor.obj
      (Opposite.op <| Arrow.cechNerve (.mk <| FormalCoproduct.homOfPiHom X f φ))) ⋙
    ((FormalCoproduct.evalOp _ _).obj F))).homology
end Kenny

open AlgebraicGeometry SheafOfModules

universe u
instance {X : Scheme.{u}} : ∀ (X_1 : TopologicalSpace.Opens ↥X),
    ((Opens.grothendieckTopology ↥X).over X_1).WEqualsLocallyBijective AddCommGrp := sorry

variable {X : Scheme.{u}} (F : X.Modules) [IsQuasicoherent F]
    {k : Type u} [Field k] [X.CanonicallyOver (Spec (.of k))]
    [IsSeparated (X ↘ (Spec (.of k)))]
    [QuasiCompact (X ↘ (Spec (.of k)))]
    (𝒰 𝒰' : Scheme.AffineOpenCover.{u} X)

def f : 𝒰.J → (TopologicalSpace.Opens X) := (fun (j : 𝒰.J) ↦ ⟨Set.range (𝒰.map j).base, IsOpenImmersion.isOpen_range (𝒰.map j)⟩)

noncomputable
def φ (j : 𝒰.J) : f 𝒰 j ⟶ ⊤ := (f 𝒰 j).leTop

/-
Some category nonsense, once I understand what this is saying I don't think it will have an
mathematical content
-/
instance : ∀ (n : ℕ),
    HasWidePullback (Arrow.mk (FormalCoproduct.homOfPiHom ⊤ (f 𝒰) (φ 𝒰))).right
      (fun x : Fin ( n+ 1) ↦ (Arrow.mk (FormalCoproduct.homOfPiHom ⊤ (f 𝒰) (φ 𝒰))).left) fun x ↦
      (Arrow.mk (FormalCoproduct.homOfPiHom ⊤ (f 𝒰) (φ 𝒰))).hom := by sorry





noncomputable
def cechCohomology := kennyCech F.val.presheaf ⊤ 𝒰.J (f 𝒰) (φ 𝒰)

/-
We should first write some basic API about Cech cohomology.

Namely, we should probably have some very concrete description of what Cech cohomology
looks like in terms of a more down to Earth definition.
-/


/-
Our first lemma should be that the zeroth Cech cohomology computes Γₘ(F, U).

Proof: cechCohomology F 𝒰 0 is simply given by a sum of sections on each 𝒰ᵢ which
agree on overlaps, which is precisely what it means to be a global section of
F by the sheaf property.
-/
lemma basic : cechCohomology F 𝒰 0 = .of Γₘ(F, ⊤) := by
  simp [cechCohomology, kennyCech]

  sorry


/-
We also want to show that higher Cech cohomology of an affine scheme vanishes (here with respect
to some fixed affine cover).
-/

/-
Cech cohomology of an affine scheme is trivial.

To show this, we need some tricks, I think this should be our first project after the line bundle
stuff is done.
-/
lemma cechCohomologyAffine {R : CommRingCat} (hX : X = Spec R) : ∀ i ≥ 1,
  cechCohomology F 𝒰 i = .of PUnit := sorry

/--
On a quasicompact separated scheme, Cech cohmomology is invariant with respect to which affine
cover it is computed on.

Note some things. First, we should be working with finite covers (of course, this is essentially
the same by quasicompactness).

The precise statement we should show is that given finite affine covers `𝒰` and `𝒱` with
`𝒰 ≤ 𝒱`, the natural map `H^i_{𝒱}(X, F) → H^i_{𝒰}(X, F)` is an isomorphism.

Hence, we should first construct this map (I think this should be in the Cech nerve library already)

Proof:

Note that since `𝒰` and `𝒱` are finite, it suffices to prove the case where `|𝒱| = |𝒰| + 1`, i.e.
we're going to prove this using `𝒰` extended by some affine open `U₀`.

This reduces by Vakil to showing that H^i(U₀, F) is 0.
-/
lemma cechInvariant (i : ℕ) : cechCohomology F 𝒰 i = cechCohomology F 𝒰' i := sorry
