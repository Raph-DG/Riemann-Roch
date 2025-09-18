import Mathlib

/-!
In this file we wish to show that
-/
open Topology TopologicalSpace
variable {X : Type*} [TopologicalSpace X] (W V : Set X) [QuasiSober W] (hV : IsClosed V)

lemma QuasiSober.quasiSober_inter (hV : IsClosed V) : QuasiSober (W ∩ V : Set X) := by
  have : W ∩ V ⊆ W := Set.inter_subset_left
  have : IsClosedEmbedding <| Set.inclusion this := by
    refine IsClosedEmbedding.inclusion this ?_
    rw [isClosed_induced_iff]
    use V
    refine ⟨hV, ?_⟩
    exact Eq.symm (Subtype.preimage_coe_self_inter W V)
  exact Topology.IsClosedEmbedding.quasiSober this

def inter_homeo_preimage_val : ↑(W ∩ V) ≃ₜ ↑(Subtype.val (p := W) ⁻¹' V) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨⟨x, hx.1⟩, hx.2⟩
  invFun := fun ⟨⟨x, hx1⟩, hx2⟩ ↦ ⟨x, ⟨hx1, hx2⟩⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  continuous_toFun := by continuity
  continuous_invFun := by continuity

omit [QuasiSober ↑W] in
lemma NoetherianSpace.noetherian_inter [ntW : NoetherianSpace W] :
    NoetherianSpace <| (W ∩ V : Set X) := by
  have := @NoetherianSpace.set _ _ ntW (Subtype.val (p := W) ⁻¹' V)
  convert this
  apply TopologicalSpace.noetherianSpace_iff_of_homeomorph
  exact inter_homeo_preimage_val W V

/-
lemma sdfjn : QuasiSober (Subtype.val (p := W) ⁻¹' V) := by
  have : IsClosedEmbedding <| Subtype.restrict
    (Subtype.val (p := W) ⁻¹' V) (Subtype.val (p := W)) := by

    simp [Subtype.restrict_def]

    --#check @Subtype.val (Subtype W) (Subtype.val ⁻¹' V)
    rw [@Function.comp_def]
    rw [← @Function.Embedding.coe_subtype]

    sorry

  exact Topology.IsClosedEmbedding.quasiSober this-/
