import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2


namespace TopCat

/-- The `n`-disk is the set of points in ℝⁿ whose norm is at most `1`,
endowed with the subspace topology. -/
noncomputable def disk (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The boundary of the `n`-disk. -/
noncomputable def diskBoundary (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The `n`-sphere is the set of points in ℝⁿ⁺¹ whose norm equals `1`,
endowed with the subspace topology. -/
noncomputable def sphere (n : ℕ) : TopCat.{u} :=
  diskBoundary (n + 1)

/-- `𝔻 n` denotes the `n`-disk. -/
scoped prefix:arg "𝔻 " => disk

/-- `∂𝔻 n` denotes the boundary of the `n`-disk. -/
scoped prefix:arg "∂𝔻 " => diskBoundary

/-- `𝕊 n` denotes the `n`-sphere. -/
scoped prefix:arg "𝕊 " => sphere

/-- The inclusion `∂𝔻 n ⟶ 𝔻 n` of the boundary of the `n`-disk. -/
def diskBoundaryInclusion (n : ℕ) : diskBoundary.{u} n ⟶ disk.{u} n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }

instance isEmpty_diskBoundary_zero : IsEmpty (diskBoundary.{u} 0) := by
  unfold diskBoundary
  simp_all only [isEmpty_ulift, Set.isEmpty_coe_sort]
  apply Set.subset_empty_iff.mp
  intro x hx
  have u : Unique <| EuclideanSpace ℝ (Fin 0) := by infer_instance
  have x0' := (u.uniq x).trans (u.uniq 0).symm
  have x0 : ‖x‖ = 0 := by rw [x0', norm_zero]
  have x1 : ‖x‖ = 1 := by convert mem_sphere_iff_norm.mp hx; rw [sub_zero]
  have : (1 : ℝ) = (0 : ℝ) := x1.symm.trans x0
  exfalso
  exact (by norm_num : (1 : ℝ) ≠ (0 : ℝ)) this

end TopCat
