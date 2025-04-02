import Mathlib.Topology.UnitInterval
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Category.TopCat.Basic
-- import Mathlib.Topology.Category.TopCat.Limits.Basic

open scoped Topology unitInterval


/-- the inclusion map a ↦ ⟨a, 0⟩ -/
abbrev TopCat.inclZero (A : TopCat.{u}) : A ⟶ TopCat.of (A × I) := ofHom
  { toFun a := ⟨a, 0⟩
    continuous_toFun := continuous_id.prodMk continuous_const }

/-- Given a path, return its starting point (value at 0).
The continuity of this function, through typeclass resolution,
implicitly relies on the fact that `I` is locally compact.-/
abbrev TopCat.pathStart (Y : TopCat.{u}) : TopCat.of C(I, Y) ⟶ Y := ofHom
  { toFun f := f 0
    continuous_toFun := Continuous.eval continuous_id continuous_const }
