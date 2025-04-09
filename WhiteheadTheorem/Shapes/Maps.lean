import Mathlib.Topology.UnitInterval
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Category.TopCat.Basic
-- import Mathlib.Topology.Category.TopCat.Limits.Basic

open scoped Topology unitInterval CategoryTheory


namespace unitInterval

instance continuousMul : ContinuousMul I where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact Continuous.mul
      (continuous_induced_dom.comp continuous_fst)
      (continuous_induced_dom.comp continuous_snd)

end unitInterval


namespace ContinuousMap

lemma mulRight_one (X : Type*) [TopologicalSpace X]
    [mulOne : MulOneClass X] [ContinuousMul X] :
    ContinuousMap.mulRight 1 = ContinuousMap.id X := by
  ext x
  simp only [coe_mulRight, id_apply]
  exact mulOne.mul_one x

lemma mulRight_zero (X : Type*) [TopologicalSpace X]
    [mulOne : MulZeroClass X] [ContinuousMul X] :
    ContinuousMap.mulRight 0 = ContinuousMap.const X 0 := by
  ext x
  simp only [coe_mulRight, id_apply]
  exact mulOne.mul_zero x

lemma prodMap_id_id (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    ContinuousMap.prodMap (ContinuousMap.id X) (ContinuousMap.id Y) = ContinuousMap.id _ :=
  rfl

end ContinuousMap



namespace TopCat

-- /-- The cylinder whose base is `A` -/
-- abbrev Cyl (A : TopCat.{u}) : TopCat.{u} := TopCat.of (A × I)

namespace Cyl

/-- The inclusion map a ↦ ⟨a, 0⟩ from `A` to the cylinder whose base is `A` -/
abbrev i₀ (A : TopCat.{u}) : A ⟶ TopCat.of (A × I) :=
  ofHom
    { toFun a := ⟨a, 0⟩
      continuous_toFun := continuous_id.prodMk continuous_const }

/-- The inclusion map a ↦ ⟨a, 1⟩ from `A` to the cylinder whose base is `A` -/
abbrev i₁ (A : TopCat.{u}) : A ⟶ TopCat.of (A × I) :=
  ofHom
    { toFun a := ⟨a, 1⟩
      continuous_toFun := continuous_id.prodMk continuous_const }

/-- The retraction from a cylinder to its base -/
abbrev r₀ (A : TopCat.{u}) : TopCat.of (A × I) ⟶ A :=
  ofHom
    { toFun := fun ⟨a, _⟩ ↦ a
      continuous_toFun := continuous_fst }

@[simp]
lemma i₀_r₀_eq_id {A : TopCat.{u}} : i₀ A ≫ r₀ A = 𝟙 _ := rfl

@[simp]
lemma i₁_r₀_eq_id {A : TopCat.{u}} : i₁ A ≫ r₀ A = 𝟙 _ := rfl

end Cyl


-- /-- The space of paths in `Y` -/
-- abbrev PathSpace (Y : TopCat.{u}) : TopCat.{u} := TopCat.of C(I, Y)

namespace PathSpace

/-- Given a path, return its starting point (value at 0).
The continuity of this function, through typeclass resolution,
implicitly relies on the fact that `I` is locally compact.-/
abbrev eval₀ (Y : TopCat.{u}) : TopCat.of C(I, Y) ⟶ Y :=
  ofHom
    { toFun f := f 0
      continuous_toFun := Continuous.eval continuous_id continuous_const }

/-- Given a morphism `f : X ⟶ Y`, return a morphism `X ⟶ TopCat.of C(I, Y)`
that sends each point `x : X` to the constant path at `f x : Y`. -/
abbrev homToConstPaths {X Y : TopCat.{u}} (f : X ⟶ Y) : X ⟶ TopCat.of C(I, Y) :=
  ofHom <| ContinuousMap.curry
    { toFun := fun ⟨x, _⟩ ↦ f x
      continuous_toFun := by fun_prop }

end PathSpace

end TopCat
