import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.ContinuousMap.Basic
-- import Mathlib.Topology.Category.TopCat.Limits.Basic


section Real.iSup
/-!
Auxiliary lemmas used in `largeCubeHomeoPDisk` and `largeCubeBoundaryHomeoPDiskBoundary`
-/

lemma Real.forall_le_of_iSup_le_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a := fun i ↦ by
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact Real.isLUB_sSup ‹_› hbdd |>.left (Set.mem_range_self i) |>.trans hf

lemma Real.range_bddAbove_of_finite_domain {ι : Type*} (f : ι → ℝ) [Finite ι] :
    BddAbove (Set.range f) := by
  cases isEmpty_or_nonempty ι
  · exact ⟨0, fun y hy ↦ (IsEmpty.exists_iff.mp hy).elim⟩
  · obtain ⟨i, hi⟩ := Finite.exists_max f
    exact ⟨f i, fun y hy ↦ by
      obtain ⟨j, hj⟩ := Set.mem_range.mp hy
      rw [← hj]; exact hi j⟩

lemma Real.forall_le_of_iSup_le_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a :=
  forall_le_of_iSup_le_of_bddAbove (range_bddAbove_of_finite_domain f) hf

lemma Real.le_iSup_of_exists_ge_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i := by
  obtain ⟨i, hi⟩ := hf
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact hi.trans <| (Real.isLUB_sSup ‹_› hbdd).left (Set.mem_range_self i)

lemma Real.le_iSup_of_exists_ge_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i :=
  le_iSup_of_exists_ge_of_bddAbove (range_bddAbove_of_finite_domain f) hf

lemma Real.exists_eq_of_iSup_eq_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hfz : ∃ i, f i ≥ 0) (hf : ⨆ i, f i = a) : ∃ i, f i = a := by
  have : Nonempty ι := nonempty_of_exists hfz
  have iSup_lt_iff : ⨆ i ∈ (Set.univ : Set ι), f i < a ↔ ∀ i ∈ Set.univ, f i < a := by
    apply Set.Finite.ciSup_lt_iff Set.finite_univ
    rw [Real.sSup_empty]   -- The supremum `sSup ∅` is defined to be 0 for `ℝ`
    simp only [Set.mem_univ, true_and]
    exact hfz
  have lt_iSup_iff : a < ⨆ i, f i ↔ ∃ i, a < f i :=
    lt_ciSup_iff (range_bddAbove_of_finite_domain f)
  by_contra nex; simp only [not_exists] at nex
  have : ∀ (i : ι), f i < a := fun i ↦ by
    obtain h | h | h := lt_trichotomy (f i) a
    · exact h
    · exfalso; exact nex i h
    · exfalso; exact ne_of_lt (lt_iSup_iff.mpr ⟨i, h⟩) hf.symm
  replace : ∀ i ∈ Set.univ, f i < a := fun i _ ↦ this i
  replace := iSup_lt_iff.mpr this
  rw [(by simp only [Set.mem_univ, ciSup_unique] : ⨆ i ∈ Set.univ, f i = ⨆ i, f i)] at this
  exact ne_of_lt this hf

end Real.iSup


/-- The result of embedding `i : Fin n` in `Fin (n+1)` is not equal to `n : Fin (n+1)` -/
lemma Fin.castSucc_ne_last {n : ℕ} (i : Fin n) : i.castSucc ≠ Fin.last n :=
  fun heq ↦ Nat.ne_of_lt i.isLt (congrArg Fin.val heq)


section GluingLemma

namespace ContinuousMap

-- #check ContinuousMap.liftCover -- gluing lemma for an open cover

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {ι : Type*} [Finite ι] (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
(hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
(hS_cover : ∀ x : α, ∃ i, x ∈ S i) (hS_closed : ∀ i, IsClosed (S i))

noncomputable def liftCoverClosed : C(α, β) :=
  have H : ⋃ i, S i = Set.univ := Set.iUnion_eq_univ_iff.2 hS_cover
  let Φ := Set.liftCover S (fun i ↦ φ i) hφ H
  ContinuousMap.mk Φ <| continuous_iff_isClosed.mpr fun Y hY ↦ by
    have : ∀ i, φ i ⁻¹' Y = S i ∩ Φ ⁻¹' Y := fun i ↦ by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, exists_and_right, exists_eq_right,
        Set.mem_inter_iff]
      conv => lhs; rhs; ext hxi; arg 2; equals Φ x => exact Eq.symm (Set.liftCover_of_mem hxi)
      tauto
    have : Φ ⁻¹' Y = ⋃ i, Subtype.val '' (φ i ⁻¹' Y) := by
      conv_rhs => ext x; arg 1; ext i; rw [this]
      conv_rhs => ext x; rw [← Set.iUnion_inter, H, Set.univ_inter]
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦
      IsClosed.trans (IsClosed.preimage (φ i).continuous hY) (hS_closed i)

theorem liftCoverClosed_coe {i : ι} (x : S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i x := by
  rw [liftCoverClosed, ContinuousMap.coe_mk, Set.liftCover_coe _]

theorem liftCoverClosed_coe' {i : ι} (x : α) (hx : x ∈ S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i ⟨x, hx⟩ := by
  rw [← liftCoverClosed_coe]

end ContinuousMap

end GluingLemma
