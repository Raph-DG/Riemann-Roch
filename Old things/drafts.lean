open Topology IrreducibleCloseds Set in
lemma coheight_eq_of_isOpenEmbedding' {U X : Type*} [TopologicalSpace U] [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [QuasiSober U] [T0Space U]
    {Z : IrreducibleCloseds U} (f : U → X) (hf : Continuous f) (hf' : IsOpenEmbedding f)
    : Order.coheight (map' f hf Z) = Order.coheight Z := by
  rw[← Order.coheight_orderIso (map'OrderIso f hf hf') Z]
  let g : {V : IrreducibleCloseds X | f ⁻¹' ↑V ≠ ∅} ↪o
      IrreducibleCloseds X :=
    OrderEmbedding.subtype {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅}
  let a := (map'OrderIso f hf hf') Z
  have : ∀ p : LTSeries (IrreducibleCloseds X), p.head = g a →
         ∃ p' : LTSeries ({V : IrreducibleCloseds X | f ⁻¹' ↑V ≠ ∅}),
           p'.head = a ∧ p = p'.map g (OrderEmbedding.strictMono g) := fun p hp ↦ by
    let p' : LTSeries {V : IrreducibleCloseds X | f ⁻¹' ↑V ≠ ∅} := {
      length := p.length
      toFun i := {
        val := p i
        property := by
          suffices  ¬ f ⁻¹' a = ∅ by
            rw[← Ne, ← nonempty_iff_ne_empty] at this
            exact nonempty_iff_ne_empty.mp <|
              Nonempty.mono (fun _ b ↦ (hp ▸ LTSeries.head_le p i) b) this
          exact a.2
      }
      step := p.step
    }
    exact ⟨p', SetCoe.ext hp, rfl⟩
  have := Order.coheight_eq_of_strictMono g (fun _ _ a ↦ a)
     ((map'OrderIso f hf hf') Z) this
  convert this.symm


/-

  rw [← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm (f x),
      ← Order.coheight_orderIso (irreducibleSetEquivPoints (α := U)).symm x,
      ← Order.coheight_orderIso (map'OrderIso f hf hf') ((irreducibleSetEquivPoints (α := U)).symm x)]

  simp [map'OrderIso]
  have := (coheight_eq_of_isOpenEmbedding' f hf hf' (Z := irreducibleSetEquivPoints.symm x))
  convert this


  have : (irreducibleSetEquivPoints.symm x) = (irreducibleSetEquivPoints.invFun x) := rfl
  have : (irreducibleSetEquivPoints.symm (f x)) = (irreducibleSetEquivPoints.invFun (f x)) := rfl
  rw[this]
  have := map'_point_closure f hf (x := x)
  rw [← this]
  simp
  --rw[map'_point_closure f hf]
  have := (coheight_eq_of_isOpenEmbedding' f hf hf' (Z := irreducibleSetEquivPoints.symm x))
  rw [this]
  simp [map']
  sorry

  /-
  It seems like we need some lemma relating map' and irreducibleSetEquivPoints
  -/
  #check coheight_eq_of_isOpenEmbedding' f hf hf'

    --exact (coheight_eq_of_isOpenEmbedding' f hf hf')
-/
--← Order.coheight_orderIso (map'OrderIso f hf hf') ((irreducibleSetEquivPoints (α := U)).symm x)]

/-
/-rw [← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm (f.base x),
      ← Order.coheight_orderIso (irreducibleSetEquivPoints (α := U)).symm x,
      ← Order.coheight_orderIso
      (map'OrderIso f.base (Scheme.Hom.continuous f) k.base_open)
      ((irreducibleSetEquivPoints (α := U)).symm x)]
  let g : {V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' ↑V ≠ ∅} ↪o
      IrreducibleCloseds X :=
    OrderEmbedding.subtype {V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' V ≠ ∅}
  let a := (map'OrderIso f.base (Scheme.Hom.continuous f) f.isOpenEmbedding)
      (irreducibleSetEquivPoints.symm x)
  have : ∀ p : LTSeries (IrreducibleCloseds X), p.head = g a →
         ∃ p' : LTSeries ({V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' ↑V ≠ ∅}),
           p'.head = a ∧ p = p'.map g (OrderEmbedding.strictMono g) := fun p hp ↦ by
    let p' : LTSeries {V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' ↑V ≠ ∅} := {
      length := p.length
      toFun i := {
        val := p i
        property := by
          suffices  ¬⇑(ConcreteCategory.hom f.base) ⁻¹' a = ∅ by
            rw[← Ne, ← nonempty_iff_ne_empty] at this
            exact nonempty_iff_ne_empty.mp <|
              Nonempty.mono (fun _ b ↦ (hp ▸ LTSeries.head_le p i) b) this
          exact a.2
      }
      step := p.step
    }
    exact ⟨p', SetCoe.ext hp, rfl⟩
  have := Order.coheight_eq_of_strictMono g (fun _ _ a ↦ a)
     ((map'OrderIso f.base (Scheme.Hom.continuous f) k.base_open)
     (irreducibleSetEquivPoints.symm x)) this
  convert this.symm
  simp only [irreducibleSetEquivPoints, ne_eq, coe_setOf, mem_setOf_eq, map'OrderIso,
    RelIso.coe_fn_mk, Equiv.ofBijective_apply, map']
  suffices closure {f.base x} = closure ((f.base) '' (closure {x})) from
    IrreducibleCloseds.ext_iff.mpr this
  simp [closure_image_closure (Scheme.Hom.continuous f)]-/


 /-by
  refine ⟨Equiv.ofBijective (map' f h) (map'_bijective_of_openEmbedding f h h2), ?_⟩
  have := map'_mono f h
  refine fun a b ↦ ⟨fun h ↦ ?_, fun a_1 ↦ (map'_mono f h) a_1⟩
  · have eq : f ⁻¹' closure (f '' a.carrier) ≤ f ⁻¹' closure (f '' b.carrier) := fun _ b ↦ h b
    have (c : IrreducibleCloseds U) : c.carrier = f ⁻¹' (closure (f '' c.carrier)) := by
      suffices closure c.carrier = f ⁻¹' (closure (f '' c.carrier)) by
        nth_rewrite 1 [← IsClosed.closure_eq c.3]
        exact this
      exact Topology.IsEmbedding.closure_eq_preimage_closure_image h2.isEmbedding c
    rwa [← this a, ← this b] at eq-/
-/


open Topology IrreducibleCloseds
lemma map'_point_closure {U X : Type*} [TopologicalSpace U] [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [QuasiSober U] [T0Space U]
    {x : U} (f : U → X) (hf : Continuous f) :
    map' f hf (irreducibleSetEquivPoints.invFun x) = (irreducibleSetEquivPoints.invFun (f x)) := by
  simp [map', irreducibleSetEquivPoints, closure_image_closure hf, Set.image_singleton]

/-
#check IrreducibleCloseds
open Topology IrreducibleCloseds Set in
lemma coheight_eq_of_isOpenEmbedding {U X : Type*} [TopologicalSpace U] [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [QuasiSober U] [T0Space U]
    {x : U} (f : U → X) (hf : Continuous f) (hf' : IsOpenEmbedding f)
    : Order.coheight (f x) = Order.coheight x := by
  rw [← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm (f x),
      ← Order.coheight_orderIso (irreducibleSetEquivPoints (α := U)).symm x,
      ← Order.coheight_orderIso (map'OrderIso f hf hf')
        ((irreducibleSetEquivPoints (α := U)).symm x)]
  let g : {V : IrreducibleCloseds X | f ⁻¹' ↑V ≠ ∅} ↪o
      IrreducibleCloseds X :=
    OrderEmbedding.subtype {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅}
  let a := (map'OrderIso f hf hf')
      (irreducibleSetEquivPoints.symm x)
  have : ∀ p : LTSeries (IrreducibleCloseds X), p.head = g a →
         ∃ p' : LTSeries ({V : IrreducibleCloseds X | f ⁻¹' ↑V ≠ ∅}),
           p'.head = a ∧ p = p'.map g (OrderEmbedding.strictMono g) := fun p hp ↦ by
    let p' : LTSeries {V : IrreducibleCloseds X | f ⁻¹' ↑V ≠ ∅} := {
      length := p.length
      toFun i := {
        val := p i
        property := by
          suffices  ¬ f ⁻¹' a = ∅ by
            rw[← Ne, ← nonempty_iff_ne_empty] at this
            exact nonempty_iff_ne_empty.mp <|
              Nonempty.mono (fun _ b ↦ (hp ▸ LTSeries.head_le p i) b) this
          exact a.2
      }
      step := p.step
    }
    exact ⟨p', SetCoe.ext hp, rfl⟩
  have := Order.coheight_eq_of_strictMono g (fun _ _ a ↦ a)
     ((map'OrderIso f hf hf')
     (irreducibleSetEquivPoints.symm x)) this
  convert this.symm
  simp only [irreducibleSetEquivPoints, ne_eq, coe_setOf, mem_setOf_eq, map'OrderIso,
    RelIso.coe_fn_mk, Equiv.ofBijective_apply, map']
  suffices closure {f x} = closure (f '' (closure {x})) from
    IrreducibleCloseds.ext_iff.mpr this
  simp [closure_image_closure hf]

#find_home coheight_eq_of_isOpenEmbedding

--attribute [local instance] specializationOrder
-/


--rw [LocallyFiniteSupport.iff_support_locally_finite]

/-structure LocallyFiniteSupport [Zero Y] (f : X → Y) : Prop where
  support_locally_finite' : ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)-/
/-
lemma LocallyFiniteSupport.support_locally_finite [Zero Y] (f : X → Y) (hf : LocallyFiniteSupport f) :
    ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := support_locally_finite'-/
/-
lemma LocallyFiniteSupport.iff_support_locally_finite [Zero Y] (f : X → Y) :
    LocallyFiniteSupport f ↔ ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := sorry
  --⟨fun p ↦ p, fun p ↦ p⟩-/
