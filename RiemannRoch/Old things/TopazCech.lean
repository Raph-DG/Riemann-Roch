import Mathlib

open AlgebraicGeometry CategoryTheory Limits

universe u
variable {A : Type*} [Category A] {X : Scheme.{u}}

instance : HasFiniteLimits (Scheme.OpenCover.{u} X) := sorry

structure OpenOver (X : Scheme) where
  dom : Scheme
  f : dom ⟶ X
  isOpen : IsOpenImmersion f := by infer_instance

instance (f : OpenOver X) : IsOpenImmersion f.f := f.isOpen

instance : Category (OpenOver X) :=
  InducedCategory.category fun f => Over.mk f.f

def OpenOver.toOpens (X : Scheme) : OpenOver X ⥤ TopologicalSpace.Opens X where
  obj f := f.f.opensRange
  map e := LE.le.hom <| sorry

def TopCat.Presheaf.openImmersionFunctor (F : TopCat.Presheaf A X) :
    (OpenOver X)ᵒᵖ ⥤ A :=
  (OpenOver.toOpens X).op ⋙ F

def AlgebraicGeometry.Scheme.OpenCover.toOpenOver (U : Scheme.OpenCover.{u} X) (j : U.J) :
    OpenOver X where
    f := U.map j
    dom := U.obj j


def Scheme.OpenCover.mapToOpenOver {U V : Scheme.OpenCover.{u} X} (e : U ⟶ V) (j : U.J) :
    U.toOpenOver j ⟶ V.toOpenOver (e.idx j) where
  left := e.app _
  right := 𝟙 _
  w := e.w _

noncomputable
def Scheme.OpenCover.inducedFunctor [HasProducts A] (F : TopCat.Presheaf A X) :
    (Scheme.OpenCover.{u} X)ᵒᵖ ⥤ A where
  obj U := piObj fun j : U.unop.J => F.obj <| .op <|
    (OpenOver.toOpens X).obj <| U.unop.toOpenOver j
  map := fun {U V} f => Pi.lift fun j =>
    Pi.π _ (f.unop.idx j) ≫ F.map (Quiver.Hom.op <| (OpenOver.toOpens X).map <|
      Scheme.OpenCover.mapToOpenOver f.unop _)
  map_id := sorry
  map_comp := sorry

noncomputable
def Scheme.OpenCover.cechComplex [HasProducts A] [Preadditive A]
    (U : Scheme.OpenCover.{u} X) (F : TopCat.Presheaf A X) : CochainComplex A ℕ :=
  let e : U ⟶ ⊤_ _ := terminal.from U
  let e := Arrow.mk e
  let e := e.cechNerve
  let e : CosimplicialObject _ := e.rightOp ⋙ Scheme.OpenCover.inducedFunctor F
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj e
