import Mathlib.Order.KrullDimension
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Order.Hom.Basic
import Mathlib.AlgebraicGeometry.Properties
import RiemannRoch.ModuleLength
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

variable (Y : AlgebraicGeometry.Scheme)
#check Y.carrier


open AlgebraicGeometry
open CategoryTheory
open Opposite.op

noncomputable
def dimension (X : Scheme) : WithBot ℕ∞ := topologicalKrullDim X.carrier

/-
Suppose f an isomorphism of preorders.

Then, f.hom ≫ f.inv = ₁ & f.inv ≫ f.hom = ₁,
& we also know f.hom & f.inv are monotone

Suppose a < b

WTS: f.hom a < f.hom b

Well, we know there are some ya, yb ∈ Y s.t.
f.inv ya = a & f.inv yb = b

So, f.hom (f.inv ya) < f.hom (f.inv yb)
WTS: ya < yb

hmm, not so helpful, we can't use that a < b here

But we can use this to show f.inv strictmono ↔ f.hom strictmono

Ok, know f.hom a ≤ f.hom b & a < b, so we just need to show ¬ f.hom b ≤ f.hom a

Ok, so suppose f.hom b ≤ f.hom a.

Then, b ≤ a by monotonicity of f.inv

But that means a < b & b ≤ a, which is a contradiction.

-/

lemma Bijection_Nonempty_Preimage {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ q : Y, (f ⁻¹' {q}).Nonempty := by {
  intro q
  obtain ⟨m, pf⟩ := h.2 q
  use m
  exact pf
}

lemma Bijection_Preimage_Singleton {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ q : Y, ∃ l ∈ f ⁻¹' {q}, ∀ n ∈ f ⁻¹' {q}, n = l := by {
  intro q
  obtain ⟨elpiq, wit⟩  := Bijection_Nonempty_Preimage f h q
  use elpiq
  constructor
  exact wit
  intro n ninpi
  let fseq : f n = f elpiq := by {
    rw[ninpi]
    rw[wit]
  }
  exact h.1 fseq
}

#check lt_iff_le_not_le
theorem krullDimIsomInvariant (X : Type _) (Y : Type _)
[Preorder X] [Preorder Y] (f : X ≃o Y) : krullDim X = krullDim Y := by{
  simp[krullDim]
  apply le_antisymm
  apply iSup_le
  intro s
  have r : StrictMono f := by {
    rw[StrictMono]
    intro a b c
    rw[lt_iff_le_not_le]
    constructor
    simp
    exact le_of_lt c
    intro r
    have l : b ≤ a := by exact (OrderEmbedding.le_iff_le (RelIso.toRelEmbedding f)).mp r
    rw[lt_iff_le_not_le] at c
    exact c.2 l
    }
  have eq : (s.map f r).length = s.length := LTSeries.map_length s f r
  rw[←eq]
  exact le_iSup_iff.mpr fun b a ↦ a (s.map (⇑f) r)
  apply iSup_le
  intro s
  have r : StrictMono f.symm := by {
    rw[StrictMono]
    intro a b c
    rw[lt_iff_le_not_le]
    constructor
    simp
    exact le_of_lt c
    intro r
    have l : b ≤ a := by exact (OrderEmbedding.le_iff_le (RelIso.toRelEmbedding f.symm)).mp r
    rw[lt_iff_le_not_le] at c
    exact c.2 l
  }
  have eq : (s.map f.symm r).length = s.length := LTSeries.map_length s f.symm r
  rw[←eq]
  exact le_iSup_iff.mpr fun b a ↦ a (s.map (⇑f.symm) r)
}


theorem topologicalKrullDimIsomInvariant (X : Type _) (Y : Type _)
 [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
 (h : IsHomeomorph f) : topologicalKrullDim X = topologicalKrullDim Y := by
  simp[topologicalKrullDim]
  let g : TopologicalSpace.IrreducibleCloseds X ≃o TopologicalSpace.IrreducibleCloseds Y := {
    toFun := fun u ↦ {
      carrier := f '' u
      is_irreducible' := by {
        simp[IsIrreducible,IsPreirreducible]
        constructor
        exact u.is_irreducible'.1
        intro u1 v opu1 opv nontrivintu1 nontrivintv
        let oppreu1 := h.continuous.isOpen_preimage u1 opu1
        let opprev := h.continuous.isOpen_preimage v opv
        exact u.is_irreducible'.2 (f ⁻¹' u1) (f ⁻¹' v) oppreu1 opprev nontrivintu1 nontrivintv
      }
      is_closed' := by {
        let k : IsClosedMap f := IsHomeomorph.isClosedMap h
        exact k u u.is_closed'
      }
    }
    invFun := fun v ↦ {
      carrier := f ⁻¹' v
      is_irreducible' := by {
        simp[IsIrreducible,IsPreirreducible]
        constructor
        let p := v.is_irreducible'.1
        obtain ⟨elemofv,pf⟩ := p
        obtain ⟨q, pf2⟩ := h.bijective.2 elemofv
        use q
        simp
        rw[pf2]
        exact pf
        intro u1 u2 opu1 opu2 nontrivintu1 nontrivintu2
        let opimu1 := (IsHomeomorph.isOpenMap h) u1 opu1
        let opimu2 := (IsHomeomorph.isOpenMap h) u2 opu2
        let nontrivintimu1 : (v.carrier ∩ f '' u1).Nonempty := by {
          obtain ⟨l, p⟩ := nontrivintu1
          use f l
          refine Set.mem_preimage.mp ?h.a
          simp
          simp at p
          constructor
          exact p.1
          use l
          exact ⟨p.2, rfl⟩
        }
        let nontrivintimu2 : (v.carrier ∩ f '' u2).Nonempty := by {
          obtain ⟨l, p⟩ := nontrivintu2
          use f l
          refine Set.mem_preimage.mp ?h.b
          simp
          simp at p
          constructor
          exact p.1
          use l
          exact ⟨p.2, rfl⟩
        }
        let m := v.is_irreducible'.2 (f '' u1) (f '' u2) opimu1 opimu2 nontrivintimu1 nontrivintimu2
        obtain ⟨r, p⟩ := m
        let pir := f ⁻¹' {r}
        /-
        let j := (Equiv.ofBijective f h.bijective).symm.bijective.2
        -/
        let j := h.bijective.2 r
        let nepir : pir.Nonempty := by {
          obtain ⟨a, far⟩ := j
          use a
          exact far
        }
        obtain ⟨elem, pf⟩ := nepir
        use elem
        simp
        constructor
        let felem : f elem = r := pf
        rw[felem]
        exact p.1
        constructor
        obtain ⟨ru1, w⟩  := p.2.1
        obtain ⟨elem', sameaselem⟩ := Bijection_Preimage_Singleton f h.bijective r
        rw[sameaselem.2 elem pf]
        let alpf := w.1
        let ru1inpi : ru1 ∈ f ⁻¹' {r} := Set.mem_of_mem_inter_right w
        rw[sameaselem.2 ru1 ru1inpi] at alpf
        exact alpf
        obtain ⟨ru2, w⟩  := p.2.2
        obtain ⟨elem', sameaselem⟩ := Bijection_Preimage_Singleton f h.bijective r
        rw[sameaselem.2 elem pf]
        let alpf := w.1
        let ru1inpi : ru2 ∈ f ⁻¹' {r} := Set.mem_of_mem_inter_right w
        rw[sameaselem.2 ru2 ru1inpi] at alpf
        exact alpf
      }
      is_closed' := {
        isOpen_compl := by {
          let o := v.is_closed'.isOpen_compl
          let m := h.continuous.isOpen_preimage v.carrierᶜ o
          exact m
        }
      }
    }
    left_inv := by {
      intro ⟨u, isired, iscl⟩
      simp
      rw[Set.preimage_eq_iff_eq_image]
      exact h.bijective
    }
    right_inv := by {
      intro ⟨u, isired, iscl⟩
      simp
      rw[← Set.eq_preimage_iff_image_eq]
      exact h.bijective
    }
    map_rel_iff' := by {
      intro ⟨u1, ired1, cl1⟩ ⟨u2, ired2, cl2⟩
      simp[LE.le, Membership.mem]
      constructor
      intro a b c
      let test : f b ∈ f '' u1 := Set.mem_image_of_mem f c
      let puf := a test
      let nex : ∀ uel, f uel ∈ (f '' u2) → uel ∈ u2 := by {
        sorry
      }
      exact nex b puf
      sorry
    }
  }
  exact
    krullDimIsomInvariant (TopologicalSpace.IrreducibleCloseds X)
      (TopologicalSpace.IrreducibleCloseds Y) g

def ClosedImmersionsTargettingX (X : Scheme) := Σ (Y : Scheme), Σ (f : Y ⟶ X), Inhabited (IsClosedImmersion f)

instance closedImmersionsTargettingXSetoid (X : Scheme) : Setoid (ClosedImmersionsTargettingX X) where
  r := fun ⟨y1, f1, _⟩ ⟨y2, f2, _⟩ ↦ (∃ (h : y1 ≅ y2), f1 = h.hom ≫ f2)
  iseqv := {
    refl := by {
      intro ⟨y1, f1, im1⟩
      use Iso.refl y1
      rfl
    }
    symm := by {
      intro ⟨y1, f1, im1⟩ ⟨y2, f2, im2⟩
      simp
      intro i eq
      use i.symm
      rw[eq]
      simp
    }
    trans := by {
      intro ⟨y1, f1, im1⟩ ⟨y2, f2, im2⟩ ⟨y3, f3, im3⟩
      simp
      intro y1iy2 eq1 y2iy3 eq2
      use y1iy2 ≪≫ y2iy3
      simp
      rw[←eq2]
      exact eq1
    }
  }

def ClosedSubscheme (X : Scheme) := Quotient (closedImmersionsTargettingXSetoid X)


def SubschemeDimension {X : Scheme} (Y : ClosedSubscheme X) : WithBot ℕ∞ := sorry
/-
Note this is of course not the real definition of the codimension
-/
noncomputable
def coDimension {X : Scheme} (Y : ClosedSubscheme X) : WithBot ℕ∞ := sorry /- dimension X - (SubschemeDimension Y) -/



/-
Note I just wanted to get this to compile, this really should be integral
closed subschemes.
-/
def PrimeWeilDivisor (X : Scheme) := Σ (l : ClosedSubscheme X), Inhabited (coDimension l = 1)

def WeilDivisor (X : Scheme) := FreeAbelianGroup (PrimeWeilDivisor X)


/-
An attempt at defining the sheaf of rational functions via the presheaf of
total quotient rings. Running into some typing issues with sheafification.
-/
def RatPreSheaf (X : Scheme) : TopCat.Presheaf Type X.carrier := {
  obj := fun U ↦ FractionRing (X.presheaf.obj U)
  map := by {
    sorry
  }
}


def FieldOfFractionsOfScheme (X : Scheme) [IsIntegral X] : CommRingCat := sorry

/-
Order of vanishing of an element f of the function field of X at a point x. Defined as the
length of the module O_x / f
-/
def OrderOfRat {X : Scheme} [IsIntegral X] (f : FieldOfFractionsOfScheme X) (x : PrimeWeilDivisor X) : ℕ := sorry



/-
Sum over all codimension 1 varieties of the zero locus, commmonly denoted (f). This is well defined
because the number of points where f is 0 or infinity is a proper closed subset, and assuming X is Noetherian a
proper closed subset is a union of a finite number of irreducible closed subsets.

Probably best to actually define this as the sum of that decomposition explicitly rather than attempting to take
an infinite sum and proving that along most prime divisors our function has neither a zero nor a pole
-/
def PrincipalWeilDivisor {X : Scheme} [IsIntegral X] (f : FieldOfFractionsOfScheme X) : WeilDivisor X := sorry

structure IsPrincipal {X : Scheme} [IsIntegral X] (D : WeilDivisor X) where
  f : FieldOfFractionsOfScheme X
  eq : D = (PrincipalWeilDivisor f)