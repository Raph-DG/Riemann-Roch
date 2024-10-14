/-
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
import RiemannRoch.Proper
import RiemannRoch.InvertibleSheaf
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.UniqueFactorizationDomain
-/
import Mathlib
import RiemannRoch.ModuleLength
import RiemannRoch.Proper
import RiemannRoch.InvertibleSheaf

variable (Y : AlgebraicGeometry.Scheme)
#check Y.carrier


open AlgebraicGeometry
open CategoryTheory
open SheafOfModules
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

lemma Bijection_Preimage_Inverse_Of_Image {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ (u : Set X), f ⁻¹' (f '' u) = u := by
  exact fun u ↦ Eq.symm ((fun hf ↦ (Set.eq_preimage_iff_image_eq hf).mpr) h rfl)

lemma Bijection_Image_Inverse_Of_Preimage {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ (u : Set Y), f '' (f ⁻¹' u) = u := by
  exact fun u ↦ Eq.symm ((fun hf ↦ (Set.preimage_eq_iff_eq_image hf).mp) h rfl)

#check lt_iff_le_not_le





/-
IN LIBRARY ALREADY: krullDim_eq_of_orderIso f
-/
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


def TopologicalSpace_Induced_Map_On_Irreducible_Closeds {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (cont : Continuous f) (closed : IsClosedMap f) : TopologicalSpace.IrreducibleCloseds X → TopologicalSpace.IrreducibleCloseds Y := fun u ↦ {
      carrier := f '' u
      is_irreducible' := by {
        simp[IsIrreducible,IsPreirreducible]
        constructor
        · exact u.is_irreducible'.1
        · intro u1 v opu1 opv nontrivintu1 nontrivintv
          let oppreu1 := cont.isOpen_preimage u1 opu1
          let opprev := cont.isOpen_preimage v opv
          exact u.is_irreducible'.2 (f ⁻¹' u1) (f ⁻¹' v) oppreu1 opprev nontrivintu1 nontrivintv
      }
      is_closed' := by exact closed u u.is_closed'
    }

lemma Injective_Maps_Induce_StrictMono_Of_Image {X Y : Type _} {U V : Set X} (f : X → Y) (inj : Function.Injective f) : U ⊂ V → f '' (U) ⊂ f '' (V) := by
  intro UlV
  let nonstrict : (f '' U ⊆ f '' V) := by {
    simp
    rw[Function.Injective.preimage_image]
    exact subset_of_ssubset UlV
    exact inj
  }
  let noneq : (f '' U ≠ f '' V) := by {
    simp only [ne_eq]
    intro eq
    obtain ⟨elemOnlyInV, pf⟩ := Set.exists_of_ssubset UlV
    let elemOnlyInVInImageOfU : f elemOnlyInV ∈ f '' U := by {
      let obfact : f elemOnlyInV ∈ f '' V := by {
        simp only [Set.mem_image]
        use elemOnlyInV
        exact And.symm (And.imp_left (fun a ↦ rfl) (id (And.symm pf)))
      }
      rw[eq]
      exact obfact
    }
    obtain ⟨elemOfU, pfofU⟩ := elemOnlyInVInImageOfU
    let cont : elemOfU = elemOnlyInV := inj pfofU.2
    rw[←cont] at pf
    exact pf.2 pfofU.1
  }
  exact HasSubset.Subset.ssubset_of_ne nonstrict noneq

theorem TopologicalSpace_Induced_Map_On_Irreducible_Closeds_Injective_StrictMono {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (cont : Continuous f) (closed : IsClosedMap f) (inj : Function.Injective f) : StrictMono (TopologicalSpace_Induced_Map_On_Irreducible_Closeds f cont closed) := by
  intro U V
  exact Injective_Maps_Induce_StrictMono_Of_Image f inj

/-
theorem topologicalKrullDim_le_of_closed_injection {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (cont : Continuous f) (closed : IsClosedMap f) (inj : Function.Injective f) : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  krullDim_le_of_strictMono f (TopologicalSpace_Induced_Map_On_Irreducible_Closeds_Injective_StrictMono f cont closed)
-/
/-krullDim_le_of_strictMono-/



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
        · exact u.is_irreducible'.1
        · intro u1 v opu1 opv nontrivintu1 nontrivintv
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
        · let p := v.is_irreducible'.1
          obtain ⟨elemofv,pf⟩ := p
          obtain ⟨q, pf2⟩ := h.bijective.2 elemofv
          use q
          simp
          rw[pf2]
          exact pf
        · intro u1 u2 opu1 opu2 nontrivintu1 nontrivintu2
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
          · let felem : f elem = r := pf
            rw[felem]
            exact p.1
          constructor
          · obtain ⟨ru1, w⟩  := p.2.1
            obtain ⟨elem', sameaselem⟩ := Bijection_Preimage_Singleton f h.bijective r
            rw[sameaselem.2 elem pf]
            let alpf := w.1
            let ru1inpi : ru1 ∈ f ⁻¹' {r} := Set.mem_of_mem_inter_right w
            rw[sameaselem.2 ru1 ru1inpi] at alpf
            exact alpf
          · obtain ⟨ru2, w⟩  := p.2.2
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
        intro uel
        rw[← Set.mem_preimage]
        rw[Bijection_Preimage_Inverse_Of_Image]
        exact fun a ↦ a
        exact h.bijective
      }
      exact nex b puf
      intro a b c
      let test1 : u1 ⊆ u2 := a


      let test : f ⁻¹' {b} ⊆ u1 := by {
        let lp := Bijection_Preimage_Inverse_Of_Image f h.bijective u1
        rw[← lp]
        let fact : {b} ⊆ f '' u1 := Set.singleton_subset_iff.mpr c
        intro k
        intro l
        exact fact l
      }

      let obfact : b ∈ f '' (f ⁻¹' {b}) := by {
        rw[Bijection_Image_Inverse_Of_Preimage]
        · exact rfl
        · exact h.bijective
      }

      let finvb : ∃ x : X, f ⁻¹' {b} = {x} := by {
        let y := Bijection_Preimage_Singleton f h.bijective b
        obtain ⟨x, px⟩ := y
        use x
        exact Set.eq_singleton_iff_unique_mem.mpr px
      }
      obtain ⟨x, px⟩ := finvb
      use x
      let obfact2 : x ∈ f ⁻¹' {b} := by {
        rw[px]
        exact rfl
      }
      constructor
      exact test1 (test obfact2)
      exact obfact2
    }
  }
  exact krullDim_eq_of_orderIso g

structure ClosedImmersionOver (X : Scheme) :=
  source : Scheme
  embedding : source ⟶ X
  immersion : IsClosedImmersion embedding

def IsSubschemeMorphism {X : Scheme} {Z : ClosedImmersionOver X} {Y : ClosedImmersionOver X} (f : Y.source ⟶ Z.source) : Prop :=
  Y.embedding = f ≫ Z.embedding

def existsIsoOfClosedSubscheme (X : Scheme)
  (Y : ClosedImmersionOver X) (Z : ClosedImmersionOver X) : Prop
  :=  ∃ (h : Y.source ≅ Z.source), IsSubschemeMorphism h.hom

instance closedImmersionTargettingSchemeSetoid (X : Scheme) : Setoid (ClosedImmersionOver X) where
  r := existsIsoOfClosedSubscheme X
  iseqv := {
    refl := by {
      intro cl
      use Iso.refl cl.source
      rfl
    }
    symm := by {
      intro Y Z
      simp[existsIsoOfClosedSubscheme, IsSubschemeMorphism]
      intro i eq
      use i.symm
      rw[eq]
      simp
    }
    trans := by {
      intro ⟨y1, f1, im1⟩ ⟨y2, f2, im2⟩ ⟨y3, f3, im3⟩
      simp[existsIsoOfClosedSubscheme, IsSubschemeMorphism]
      intro y1iy2 eq1 y2iy3 eq2
      use y1iy2 ≪≫ y2iy3
      simp
      rw[←eq2]
      exact eq1
    }
  }

def ClosedSubscheme (X : Scheme) := Quotient (closedImmersionTargettingSchemeSetoid X)




def SubschemeDimension {X : Scheme} (Y : ClosedSubscheme X) : WithBot ℕ∞ := by
  sorry
  -- apply Quotient.lift
/-
Note this is of course not the real definition of the codimension
-/
noncomputable
def coDimension {X : Scheme} (Y : ClosedSubscheme X) : WithBot ℕ∞ := sorry /- dimension X - (SubschemeDimension Y) -/



/-
Note I just wanted to get this to compile, this really should be integral
closed subschemes.
-/
structure PrimeWeilDivisor (X : Scheme) where
 subscheme : ClosedSubscheme X
 codim : coDimension subscheme = 1
 /-integral : IsIntegral subscheme-/

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


axiom LinearEquivalentWeil (X : Scheme) : WeilDivisor X → WeilDivisor X → Prop

def LineBundleOfDivisor {X : Scheme} (D : WeilDivisor X) : SheafOfModules X.ringCatSheaf := {
  val := sorry /-TopCat.Presheaf CommRingCat X.carrier-/
  isSheaf := sorry
}

/-
instance LineBundleIsQCoh {X : Scheme} (D : WeilDivisor X) : IsQuasicoherent (LineBundleOfDivisor D) := sorry
-/
instance divisorClassSetoid (X : Scheme) : Setoid (WeilDivisor X) where
  r := LinearEquivalentWeil X
  iseqv := sorry

def WeilDivisorClassGroup (X : Scheme) := Quotient (divisorClassSetoid X)

def ZeroDivisor (X : Scheme) : WeilDivisor X := sorry

axiom WeilDivisorClassGroupInstance (X : Scheme) : CommGroup (WeilDivisorClassGroup X)

attribute [instance] WeilDivisorClassGroupInstance




class IsLocallyUFD (X : Scheme) : Prop where
  domain : ∀ (x : X), IsDomain (X.presheaf.stalk x)
  ufm : ∀ (x : X), UniqueFactorizationMonoid (X.presheaf.stalk x)


/-
Isomorphism between Cl(X) and Pic(X) for an Integral Noetheian scheme whose local rings are all unique
factorisation domains. The definition of this will almost certainly go via Cartier divisors,
-/

def LineBundleDivisorEquivalence (X : Scheme) [IsIntegral X] [IsNoetherian X] [IsLocallyUFD X] : WeilDivisorClassGroup X ≃* PicardGroup X := sorry

def DegreeOfWeilDivisor {X : Scheme} (D : WeilDivisor X) : ℤ := sorry
