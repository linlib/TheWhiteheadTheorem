-- import WhiteheadTheorem.Shapes.Cube
import WhiteheadTheorem.CWComplex.Basic
import Mathlib.CategoryTheory.Comma.Arrow

/-!
For every CW-complex `X`, this file constructsa relative CW-complex `X.IProd`
homeomorphic to `I × X`, where `I` is the unit interval.
The $(-1)$-skeleton of `X.IProd` is homeomorphic to `{0, 1} × X`.
-/


open CategoryTheory unitInterval TopCat
-- open scoped Topology Topology.Homotopy  -- `∂I^1` and `I^ Fin 1`

abbrev unitInterval.zeroOneIncl : C(({0, 1} : Set ℝ), I) where
  toFun x := ⟨x, by
    obtain ⟨val, property⟩ := x
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    cases property with
    | inl h0 => subst h0; simp only [le_refl, zero_le_one, and_self]
    | inr h1 => subst h1; simp only [zero_le_one, le_refl, and_self] ⟩
  continuous_toFun := by fun_prop


universe u

variable (X : CWComplex.{u})


namespace CWComplex

/-- The inclusion map from `{0, 1} × X` to `I × X` -/
abbrev zeroOneProdInclIProd :
    TopCat.of (({0, 1} : Set ℝ) × X.toTopCat) ⟶ TopCat.of (I × X.toTopCat) :=
  ofHom <| unitInterval.zeroOneIncl.prodMap (ContinuousMap.id _)

def IProd (X : CWComplex.{u}) : RelCWComplex := sorry


namespace IProd

def arrowIso :
    Arrow.mk (X.IProd.skInclusion 0) ≅ Arrow.mk X.zeroOneProdInclIProd :=
  sorry

end IProd


end CWComplex
