import Mathlib
--import Plausible

open AlgebraicGeometry CategoryTheory Limits

universe u
variable {A : Type*} [Category A] {X : Scheme.{u}}

namespace AlgebraicGeometry
namespace Scheme

variable (X) in
def OpenCover' := {U : Set X.Opens // sSup U = ⊤}

lemma elemOfSup {A : Type*} {x : A} {U : Set A} {F : Set (Set A)}
  (conj : U ∈ F ∧ x ∈ U) : x ∈ sSup F := by
  use U

lemma dumbGarbage {A : Type*} {x : A} {P : Prop} {U V : Set A} (xInV : x ∈ V) (weird : ⋃ (p : P), U = V)
  : U = V := by
  aesop




open Classical in
instance : Preorder X.OpenCover' where
  le 𝒰 𝒱 := ∀ V ∈ 𝒱.val, ∃ 𝒰' ⊆ 𝒰.val, sSup 𝒰' = V
  le_refl := by
    intro 𝒰 V hV
    use {V}
    simpa
  le_trans := by
    rintro 𝒰 𝒱 𝒲 h1 h2 W hW
    obtain ⟨𝒱', h𝒱', rfl⟩ := h2 W hW
    choose 𝒰' h using h1
    --use ⨆ (V ∈ 𝒱.val), U' V ?
    use ⨆ (V : X.Opens) (p : V ∈ 𝒱'), 𝒰' V (h𝒱' p)
    constructor
    aesop
    ext x
    simp
    constructor
    rintro ⟨U, hU, xinU⟩
    obtain ⟨V', hV'⟩ := hU
    obtain ⟨y, hy⟩ := hV'
    use V'
    constructor
    assumption
    let o := (h V' (h𝒱' y)).2
    have l : x ∈ sSup (𝒰' V' (h𝒱' ((Iff.of_eq (Eq.refl (V' ∈ 𝒱'))).mpr y))) := by
      use U
      aesop
    rw[o] at l
    assumption

    rintro ⟨V', v⟩
    --use 𝒰' V' (h𝒱' v.1)
    let t := (h V' (h𝒱' v.1)).2
    let v2 := v.2
    rw[← t] at v2
    obtain ⟨r, hr⟩ := v2
    obtain ⟨guy, hguy⟩ := hr.1
    use guy
    constructor
    use V'
    use v.1
    aesop
    simp at hguy
    let test3 := dumbGarbage hr.2 hguy
    show x ∈ (guy : Set X)
    rw[test3]
    exact hr.2


















    --let un := ⋃ (V ∈ 𝒱.val), h1 V _




    --let test := Set.image (fun V ↦ choose h1 V) 𝒱'



#synth Category X.OpenCover'



instance : HasFiniteLimits X.OpenCover' := sorry

instance : HasFiniteLimits (Scheme.OpenCover.{u} X) := sorry
