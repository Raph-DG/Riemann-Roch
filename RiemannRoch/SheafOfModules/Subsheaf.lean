import Mathlib

open CategoryTheory

open AlgebraicGeometry Scheme Opposite TopCat TopologicalSpace

variable {X : Scheme} (F : X.Modules) (P : {U : X.Opens} → F.val.obj (op U) → Prop)

macro:max "Γₘ("F:term","U:term")" : term =>
  `((SheafOfModules.val $F).obj (op $U))

structure LinearLocalPredicate (F : X.Modules) where
    P : {U : X.Opens} → Γₘ(F, U) → Prop
    zero {U : X.Opens} : P (0 : Γₘ(F, U))
    add {U : X.Opens} {f g : Γₘ(F, U)} (hf : P f) (hg : P g) : P (f + g)
    smul {U : X.Opens} (a : Γ(X, U)) {f : Γₘ(F, U)} (hf : P f) : P (a • f)
    res {U V : X.Opens} (k : V ≤ U) (f : Γₘ(F, U)) (hf : P f) :
      P (F.val.presheaf.map (homOfLE k).op f)
    local_prop {U : X.Opens} (f : Γₘ(F, U)) :
      (∀ x ∈ U, ∃ (V : X.Opens) (k : V ≤ U) (_ : x ∈ V), P <| F.val.presheaf.map (homOfLE k).op f)
      → P f

section LinearLocalPredicate

def submodule (F : X.Modules) (Fp : LinearLocalPredicate F) (U : X.Opens) :
    Submodule Γ(X, U) Γₘ(F, U) where
  carrier := Fp.P
  add_mem' hf hg := Fp.add hf hg
  zero_mem' := Fp.zero
  smul_mem' := Fp.smul

set_option synthInstance.maxHeartbeats 0
noncomputable
def presheaf (F : X.Modules) (Fp : LinearLocalPredicate F) : PresheafOfModules X.ringCatSheaf.val where
  obj U := ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) (submodule F Fp (unop U))
  map := by
    intro U V l
    apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
                (RingCat.Hom.hom (X.ringCatSheaf.val.map l))).obj
                (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) ↥(submodule F Fp (unop V))))
    exact {
      toFun x := ⟨F.val.presheaf.map l x.1, Fp.res (le_of_op_hom l) x x.2⟩
      map_add' := by aesop
      map_smul' := by
        intro a x
        simp_all only [sheafCompose_obj_val, Functor.comp_obj,
          CommRingCat.forgetToRingCat_obj, Functor.comp_map,
          CommRingCat.forgetToRingCat_map_hom, op_unop, PresheafOfModules.presheaf_obj_coe,
          SetLike.val_smul,
          RingHom.id_apply]
        apply Subtype.ext

        sorry
    }

/--
The presheaf of modules constructed from a linear local predicate is a sheaf. This follows
essentially the same construction as the proof of the sheaf condition in the case of
`TopCat.subpresheafToTypes.isSheaf`.
-/
lemma isSheaf (F : X.Modules) (Fp : LinearLocalPredicate F) :
    Presheaf.IsSheaf (presheaf F Fp).presheaf := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf sf_comp
  -- We show the sheaf condition in terms of unique gluing.
  -- First we obtain a family of sections for the underlying sheaf of functions,
  -- by forgetting that the predicate holds
  let sf' (i : ι) : ToType <| F.val.obj (op (U i)) := (sf i).val
  -- Since our original family is compatible, this one is as well
  have sf'_comp : Presheaf.IsCompatible (C := Ab) F.val.presheaf U sf' := fun i j ↦
      congr_arg Subtype.val (sf_comp i j)
  -- So, we can obtain a unique gluing
  obtain ⟨gl, gl_spec, gl_uniq⟩ := TopCat.Sheaf.existsUnique_gluing
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) U sf' (by exact sf'_comp)
  refine ⟨⟨gl, ?_⟩, ?_, ?_⟩
  · -- Our first goal is to show that this chosen gluing satisfies the
    -- predicate. Of course, we use locality of the predicate.
    apply Fp.local_prop
    intro x mem
    -- Once we're at a particular point `x`, we can select some open set `x ∈ U i`.
    choose i hi using Opens.mem_iSup.mp mem
    -- We claim that the predicate holds in `U i`
    use U i, leOfHom (Opens.leSupr U i), hi
    -- This follows, since our original family `sf` satisfies the predicate
    convert (sf i).property using 1
    exact gl_spec i
  -- It remains to show that the chosen lift is really a gluing for the subsheaf and
  -- that it is unique. Both of which follow immediately from the corresponding facts
  -- in the sheaf of functions without the local predicate.
  · exact fun i ↦ Subtype.ext (gl_spec i)
  · intro gl' hgl'
    refine Subtype.ext ?_
    exact gl_uniq gl'.1 fun i ↦ congr_arg Subtype.val (hgl' i)

noncomputable
def sheaf (F : X.Modules) (Fp : LinearLocalPredicate F) : X.Modules where
  val := presheaf F Fp
  isSheaf := isSheaf F Fp

end LinearLocalPredicate
