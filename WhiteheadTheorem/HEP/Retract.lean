import WhiteheadTheorem.HEP.Cube
import WhiteheadTheorem.Shapes.Cube
import Mathlib.Analysis.Convex.Basic


open TopCat
open scoped Topology unitInterval
open scoped Topology.Homotopy


/-- A strong deformation retraction from `X` to its subset `A` -/
structure StrongDeformRetr (X : Type*) [TopologicalSpace X] (A : Set X) where
  /-- The retraction map -/
  r : C(X, X)
  -- /-- `r` is a retraction, i.e., the restriction of `r` to `A` is the identity map.
  -- (This can be inferred from the relative homotopy `H`.) -/
  -- r_restrict : ∀ a ∈ A, r a = a
  /-- `r` sends all of `X` into `A` -/
  r_range : Set.range r ⊆ A
  /-- A homotopy `H` rel `A`, where `H₀` is the identity map on `X`, and `H₁ = r`. -/
  H : (ContinuousMap.id X).HomotopyRel r A


namespace Cube

lemma splitAtLastFinComm_inclToBotFace_eq {n : ℕ} :   -- (I^ Fin n) ↦ (I^ Fin n) × I
    splitAtLastFinComm ∘ inclToBotFace = fun x : (I^ Fin n) ↦ (x, 0) := by
  ext x i
  repeat {simp [splitAtLastFinComm, splitAtLastFin, inclToBotFace]}

/-- `(y₀, y₁, …, yₙ₋₁, yₙ) ↦ (y₀, y₁, …, yₙ₋₁)` -/
def discardLastFin {n : ℕ} : (I^ Fin (n + 1)) → (I^ Fin n) :=
  fun y ↦ fun i ↦ y ⟨i.val, i.prop.trans (by omega : n < n + 1)⟩

lemma inclToBotFace_discardLastFin_mem_boundary {n : ℕ} (y : I^ Fin (n + 1)) :
    inclToBotFace (discardLastFin y) ∈ ∂I^(n+1) := by
  use Fin.last n; left; simp [inclToBotFace]

/-- `(y₀, y₁, …, yₙ₋₁, yₙ) ↦ (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0)` does nothing if `yₙ = 0`. -/
lemma inclToBotFace_discardLastFin_eq_of {n : ℕ} (y : I^ Fin (n + 1))
    (hz : y (Fin.last n) = 0) : inclToBotFace (discardLastFin y) = y := by
  ext i; simp [discardLastFin, inclToBotFace]
  split_ifs with hi; rw [hi, hz]; simp [homeoNeqLastFin, discardLastFin]

lemma inclToBoundaryJarBot_discardLastFin_eq_of {n : ℕ} (y : I^ Fin (n + 1))
    (hz : y (Fin.last n) = 0) : inclToBoundaryJarBot (discardLastFin y) = y := by
  ext i; simp [discardLastFin, inclToBoundaryJarBot, inclToBotFace]
  split_ifs with hi; rw [hi, hz]; simp [homeoNeqLastFin, discardLastFin]

------------------

lemma splitAtLastFinComm_inclToSides_eq {n : ℕ} :   -- (∂I^n) × I ↦ (I^ Fin n) × I
    splitAtLastFinComm ∘ inclToSides = Prod.map (boundaryInclusion n) id := by
  ext ⟨y, t⟩ i
  repeat { simp [splitAtLastFinComm, splitAtLastFin, boundaryInclusion,
    inclToSides, inclToBoundaryJarSides] }

/-- Project the $(n+1)$-dimensional cube to its boundary `∂I^(n+1)`.
This fixes every point on the boundary, and maps other points to the default value `0`.
This (non-continuous) function is convenient for diagram-chasing when applying
the homotopy extension property in `retrToBoundaryJar`.
This function is `noncomputable` due to `Real.decidableEq`. -/
noncomputable def projToBoundary {n : ℕ} : (I^ Fin (n + 1)) → ∂I^(n+1) := fun y ↦
  let _ : Decidable (y ∈ ∂I^(n+1)) := by
    simp only [Cube.boundary, Set.mem_setOf_eq]
    infer_instance
  if _ : y ∈ ∂I^(n+1)
    then ⟨y, ‹_›⟩
    else ⟨0, ⟨0, by simp only [Pi.zero_apply, zero_ne_one, or_false]⟩⟩

/-- `projToBoundary y` does nothing if `y` is already in the boundary.  -/
lemma projToBoundary_eq_of_mem_boundary {n : ℕ} (y : I^ Fin (n + 1))
    (hy: y ∈ ∂I^(n+1)) : projToBoundary y = y := by
  simp only [projToBoundary, hy, ↓reduceDIte]

/-- Project the $(n+2)$-dimensional cube to its sides `(∂I^(n+1)) × I`
(the closure of the complement of the top and bottom faces of the boundary).
Since `∂I^0 = ∅`, the cube shoule be at least 2-dimensional. -/
noncomputable def projToSides {n : ℕ} : (I^ Fin (n + 1 + 1)) → (∂I^(n+1)) × I :=
  (Prod.map projToBoundary id) ∘ splitAtLastFinComm

lemma inclToSides_projToSides_eq_of {n : ℕ} (y : I^ Fin (n + 1 + 1))
    (hs : (splitAtLastFin y).snd ∈ ∂I^(n+1)) :
    inclToSides (projToSides y) = y := by
  simp [projToSides, Prod.map]
  rw [splitAtLastFin_snd_eq] at hs
  have : projToBoundary (splitAtLastFinComm y).1 = ⟨(splitAtLastFinComm y).1, ‹_›⟩ :=
    Subtype.eq_iff.mpr (projToBoundary_eq_of_mem_boundary _ hs)
  rw [this]
  ext i
  simp [inclToSides, inclToBoundaryJarSides, splitAtLastFinComm, splitAtLastFin]
  simp [boundaryInclusion, splitAtLastFinComm, splitAtLastFin]
  split_ifs with hi
  rw [hi]; simp only

lemma inclToBoundaryJarSides_projToSides_eq_of {n : ℕ} (y : I^ Fin (n + 1 + 1))
    (hs : (splitAtLastFin y).snd ∈ ∂I^(n+1)) :
    inclToBoundaryJarSides (projToSides y) = y := by
  simp [projToSides, Prod.map]
  rw [splitAtLastFin_snd_eq] at hs
  have : projToBoundary (splitAtLastFinComm y).1 = ⟨(splitAtLastFinComm y).1, ‹_›⟩ :=
    Subtype.eq_iff.mpr (projToBoundary_eq_of_mem_boundary _ hs)
  rw [this]
  ext i
  simp [inclToBoundaryJarSides, splitAtLastFinComm, splitAtLastFin]
  split_ifs with hi
  · rw [hi]
  · simp [boundaryInclusion]

------------------

/-- A  retraction from `I^n` to `∂I^n`. -/
noncomputable def retrToBoundaryJar (n : ℕ) :
    { r' : C(Fin (n + 1) → I, ⊔I^n + 1) // ∀ y ∈ ⊔I^(n+1), r' y = y } := by
  let f : C(I^ Fin n, ⊔I^(n + 1)) := inclToBoundaryJarBot
  let h : C((∂I^n) × I, ⊔I^(n + 1)) := inclToBoundaryJarSides
  have : f ∘ (boundaryInclusion n) = h ∘ fun x ↦ (x, 0) := by
    ext x i
    simp [boundaryInclusion, f, h, inclToBoundaryJarBot, inclToBoundaryJarSides, inclToBotFace,
          splitAtLastFinComm, splitAtLastFin]
  have hep := Cube.boundaryInclusion_hasHEP n (⊔I^(n + 1)) f h this
  let H := Classical.choose hep
  have spec : (f = H ∘ fun x ↦ (x, 0)) ∧ h = H ∘ Prod.map (boundaryInclusion n) id :=
    Classical.choose_spec hep
  let r' : C(I^ Fin (n + 1), ⊔I^(n+1)) := H.comp (toContinuousMap splitAtLastFinComm)
  exact ⟨r', fun y hy ↦ by
    by_cases hbot : y (Fin.last n) = 0
    · nth_rw 1 [← inclToBotFace_discardLastFin_eq_of y hbot]
      change (H ∘ splitAtLastFinComm ∘ inclToBotFace) _ = y
      rw [splitAtLastFinComm_inclToBotFace_eq]
      rw [← spec.left, inclToBoundaryJarBot_discardLastFin_eq_of y hbot]
    · induction n with
      | zero =>
          have : (H ∘ splitAtLastFinComm) y = ⟨y, hy⟩ := by
            rw [unique_boundaryJar_one.uniq ⟨y, hy⟩]
            rw [unique_boundaryJar_one.uniq ((H ∘ splitAtLastFinComm) y)]
          apply_fun Subtype.val at this
          exact this
      | succ n =>
          obtain hy' | hy' := splitAtLastFin_boundaryJar hy
          · exfalso; rw [splitAtLastFin_fst_eq] at hy'; exact hbot hy'
          nth_rw 1 [← inclToSides_projToSides_eq_of y hy']
          change (H ∘ splitAtLastFinComm ∘ inclToSides) _ = y
          rw [splitAtLastFinComm_inclToSides_eq]
          rw [← spec.right]
          apply inclToBoundaryJarSides_projToSides_eq_of y
          exact hy' ⟩

/-- A strong deformation retraction from `I^n` to `∂I^n`.
I'm writing down the formula for each coordinate because:
  - `failed to synthesize ContinuousSMul (↑I) (Fin (n + 1) → ↑I)`
  - Using `Convex` requires going to a subset of ℝ^(n+1) and back
    (although `Convex ℝ I` is very helpful) -/
noncomputable def strongDeformRetrToBoundaryJar (n : ℕ) :
    StrongDeformRetr (I^ Fin (n + 1)) (⊔I^(n+1)) :=
  let ⟨r', r'_restrict⟩ := retrToBoundaryJar n
  { r := (boundaryJarInclusion (n + 1)).comp r'
    r_range := fun y hy ↦ by
      simp [Set.mem_range, boundaryJarInclusion] at hy
      obtain ⟨z, hz⟩ := hy; rw [← hz]; simp only [Subtype.coe_prop]
    H :=
      { toFun := fun ⟨t, y⟩ ↦ fun i ↦
          ⟨ (σ t).val • (y i).val + t.val • ((r' y).val i).val,  -- σ t = 1 - t
            (convex_Icc _ _ : Convex ℝ I).starConvex (y i).property ((r' y).val i).property
              (unitInterval.nonneg (σ t)) (unitInterval.nonneg t)
              (by simp only [unitInterval.coe_symm_eq, sub_add_cancel]) ⟩
        continuous_toFun := by
          refine continuous_pi fun i ↦ Continuous.subtype_mk (Continuous.add ?_ ?_) _
          . apply Continuous.smul
            · exact Continuous.subtype_val <| unitInterval.continuous_symm.comp continuous_fst
            · exact Continuous.subtype_val <| (continuous_apply i).comp continuous_snd
          . apply Continuous.smul
            · exact Continuous.subtype_val continuous_fst
            · refine Continuous.subtype_val <| (continuous_apply i).comp ?_
              exact Continuous.subtype_val <| r'.continuous.comp continuous_snd
        map_zero_left y := by simp only [unitInterval.symm_zero, Set.Icc.coe_one, smul_eq_mul,
          one_mul, Set.Icc.coe_zero, zero_mul, add_zero, Subtype.coe_eta, ContinuousMap.id_apply]
        map_one_left y := by
          simp only [unitInterval.symm_one, Set.Icc.coe_zero, smul_eq_mul, zero_mul,
            Set.Icc.coe_one, one_mul, zero_add, Subtype.coe_eta, ContinuousMap.comp_apply]
          simp only [boundaryJarInclusion, ContinuousMap.coe_mk]
        prop' t y hy := by
          ext i
          simp only [unitInterval.coe_symm_eq, smul_eq_mul, ContinuousMap.coe_mk,
            ContinuousMap.id_apply]
          rw [r'_restrict y hy, sub_mul, sub_add_cancel, one_mul] }}

end Cube
