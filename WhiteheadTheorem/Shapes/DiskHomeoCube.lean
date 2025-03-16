-- import Mathlib.Topology.CWComplex
import WhiteheadTheorem.Auxiliary
import WhiteheadTheorem.Shapes.Disk
import WhiteheadTheorem.Shapes.Cube
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Analysis.InnerProductSpace.PiL2


open scoped Topology TopCat ENNReal

namespace TopCat

universe u v

variable (n : ℕ) (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]

/-- The unit disk in `ℝⁿ` based on the `Lᵖ` norm, where `p ≥ 1`.  -/
def pDisk (n : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : PiLp p fun (_ : Fin n) ↦ ℝ) 1

/-- The boundary of the `pDisk`.  -/
def pDiskBoundary (n : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : PiLp p fun (_ : Fin n) ↦ ℝ) 1

/-- The inclusion of the boundary of the `pDisk`. -/
def pDiskBoundaryInclusion (n : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    pDiskBoundary.{u} n p ⟶ pDisk.{u} n p :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }


namespace pDisk

-- Note: need to declare the instances manually because `pDisk` and `TopCat` are not `abbrev`s.
instance instT1Space : T1Space (pDisk n p) :=
  letI : T1Space (ULift _) := inferInstance; ‹_›
instance boundaryInstT1Space : T1Space (pDiskBoundary n p) :=
  letI : T1Space (ULift _) := inferInstance; ‹_›

noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (pDisk n p) :=
  letI : PseudoMetricSpace (ULift _) := inferInstance; ‹_›
noncomputable instance boundaryInstPseudoMetricSpace : PseudoMetricSpace (pDiskBoundary n p) :=
  letI : PseudoMetricSpace (ULift _) := inferInstance; ‹_›

lemma dist_eq (x y : pDisk n p) : dist x y = dist x.down.val y.down.val :=
  rfl

/-- Use `0` to denote the center of the disk. -/
instance : OfNat (pDisk n p) 0 where
  ofNat := ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩⟩

lemma zero_eq : 0 = (0 : pDisk n p).down.val :=
  rfl

lemma eq_zero_iff (x : pDisk n p) : x = 0 ↔ x.down.val = 0 :=
  ⟨fun h ↦ by subst h; rfl, fun h ↦ by obtain ⟨x, _⟩ := x; congr⟩

/-- Map `x` to `(‖x‖_p / ‖x‖_q) • x`.
Note that division by zero evaluates to zero (see `toQDisk_zero`). -/
noncomputable def toQDisk : pDisk n p → pDisk n q
  | ⟨x, hx⟩ => ⟨ (‖x‖ * ‖WithLp.equiv q (Fin n → ℝ) |>.symm x‖⁻¹) • x, by
      simp only [Metric.mem_closedBall, dist_zero_right] at *
      simp only [norm_smul, norm_mul, Real.norm_eq_abs, abs_norm, norm_inv]
      rw [mul_assoc]
      -- Note that the two occurrences of `‖x‖` in the goal
      -- `⊢ ‖x‖ * (‖(WithLp.equiv q (Fin n.toNat → ℝ)).symm x‖⁻¹ * ‖x‖) ≤ 1` are different.
      -- The first `‖x‖` is `@norm (PiLp p fun x => ℝ) SeminormedAddGroup.toNorm x : ℝ`
      -- The last `‖x‖` is `@norm (PiLp q fun x => ℝ) SeminormedAddGroup.toNorm x : ℝ`
      -- Hence the goal is interpreted as `‖x‖_p * (‖x‖_q⁻¹ * ‖x‖_q) ≤ 1`
      exact (mul_le_of_le_one_right (norm_nonneg _) inv_mul_le_one).trans hx ⟩

/-- `pDisk.toQDisk` maps `0` to `0`.
Note that division by zero evaluates to zero, due to `GroupWithZero.inv_zero`. -/
lemma toQDisk_zero : pDisk.toQDisk n p q 0 = 0 := by
  unfold toQDisk
  simp only [norm_zero, WithLp.equiv_symm_zero, inv_zero, mul_zero, smul_zero]
  congr

/-- The map `toQDisk` has a left inverse. -/
lemma toPDisk_comp_toQDisk x : toQDisk n q p (toQDisk n p q x) = x := by
  unfold toQDisk
  by_cases hx0 : x = 0
  · simp only [hx0, norm_zero, WithLp.equiv_symm_zero, inv_zero, mul_zero, smul_zero, eq_zero_iff]
  split; next _ y hy hfx =>
    rcases x with ⟨x, _⟩
    replace hx0 : x ≠ 0 := fun h ↦ hx0 (by congr)
    replace hfx := congrArg ULift.down hfx
    simp only [Subtype.mk.injEq] at hfx
    congr
    simp only [← hfx, WithLp.equiv_symm_smul]
    simp only [norm_smul, norm_mul, norm_norm, norm_inv, mul_inv_rev, inv_inv, smul_smul]
    rw [mul_assoc ‖x‖]
    conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
    simp only [mul_one, ← mul_assoc]
    conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)
    rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr hx0), mul_one]
    conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)
    rw [one_smul]

/-- The map `toQDisk` is continuous at `0`. -/
lemma continuousAt_toQDisk_zero : ContinuousAt (toQDisk n p q) 0 := by
  apply continuousAt_of_locally_lipschitz (_ : 0 < (1 : ℝ)) 1
  swap; norm_num
  intro ⟨x, hx⟩ h
  rw [toQDisk_zero]
  simp only [dist_eq, ← zero_eq, dist_zero_right, one_mul] at *
  simp only [toQDisk, norm_smul, norm_mul, norm_norm, norm_inv]
  by_cases hx0 : x = 0
  · simp only [hx0, norm_zero, WithLp.equiv_symm_zero, inv_zero, mul_zero, le_refl]
  rw [mul_assoc, mul_le_iff_le_one_right (norm_pos_iff.mpr hx0)]
  exact inv_mul_le_one

/-- The map `toQDisk` is continuous on `{x | x ≠ 0}`. -/
lemma continuousOn_toQDisk_nonzero : ContinuousOn (toQDisk n p q) {x | x ≠ 0} := by
  apply continuousOn_iff_continuous_restrict.mpr
  unfold Set.restrict toQDisk
  simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq]
  refine continuous_uliftUp.comp <| Continuous.subtype_mk ?_ _
  refine Continuous.smul ?_ (continuous_uliftDown.comp continuous_subtype_val).subtype_val
  apply Continuous.mul (continuous_uliftDown.comp continuous_subtype_val).subtype_val.norm
  conv_rhs => intro x; rw [inv_eq_one_div]
  apply Continuous.div continuous_const
  · apply Continuous.norm
    apply @PiLp.continuous_equiv_symm _ _ (fun _ ↦ ℝ) |>.comp -- deleting this line results in deterministic timeout
    exact continuous_uliftDown.comp continuous_subtype_val |>.subtype_val
  intro ⟨x, hx0⟩ h
  simp only [norm_eq_zero] at h
  change x.down.val = 0 at h
  rw [← eq_zero_iff] at h
  exact hx0 h

/-- The map `toQDisk` is continuous. -/
lemma continuous_toQDisk : Continuous (toQDisk n p q) :=
  continuous_iff_continuousAt.mpr fun ⟨x, hx⟩ ↦ by
    by_cases hx0 : x = 0
    · subst hx0
      exact continuousAt_toQDisk_zero n p q
    exact (continuousOn_toQDisk_nonzero n p q).continuousAt
      (IsOpen.mem_nhds (IsClosed.not isClosed_singleton) fun h ↦ by
        simp only [eq_zero_iff] at h
        exact hx0 h)

/-- `pDisk n p` (the unit disk in `ℝⁿ` based on the `Lᵖ` norm) is homeomorphic to
`pDisk n q` (the unit disk in `ℝⁿ` based on the `L^q` norm). -/
noncomputable def homeoQDisk : pDisk n p ≃ₜ pDisk n q where
  toFun := toQDisk n p q
  invFun := toQDisk n q p
  left_inv := toPDisk_comp_toQDisk n p q
  right_inv := toPDisk_comp_toQDisk n q p
  continuous_toFun := continuous_toQDisk n p q
  continuous_invFun := continuous_toQDisk n q p

noncomputable def isoQDisk : pDisk n p ≅ pDisk n q :=
  isoOfHomeo (homeoQDisk n p q)

end pDisk


namespace pDiskBoundary

instance instIsEmptyZero : IsEmpty (pDiskBoundary 0 p) where
  false := fun ⟨p, p1⟩ ↦ by
    unfold PiLp WithLp at p; simp only at p
    have p0 : p = (0 : Fin 0 → ℝ) := List.ofFn_inj.mp rfl
    -- replace p0 : ‖p‖ = 0 := by rw [p0]; rfl
    simp only [mem_sphere_iff_norm, sub_zero] at p1
    have : (1 : ℝ) = (0 : ℝ) := p1.symm.trans (by rw [p0, norm_zero])
    exact (by norm_num : (1 : ℝ) ≠ (0 : ℝ)) this

lemma neq_zero (x : pDiskBoundary n p) : x.down.val ≠ 0 := fun xz ↦ by
  have x0 : ‖x.down.val‖ = 0 := by rw [xz]; apply norm_zero
  have x1 : ‖x.down.val‖ = 1 := by
    have := x.down.property
    simp only [mem_sphere_iff_norm, sub_zero] at this; exact this
  exact (by norm_num : (0 : ℝ) ≠ 1) (x0.symm.trans x1)

noncomputable def toQDiskBoundary : pDiskBoundary.{u} n p → pDiskBoundary n q
  | ⟨x, hx⟩ => ⟨ (‖x‖ * ‖WithLp.equiv q (Fin n → ℝ) |>.symm x‖⁻¹) • x, by
      have xnz := neq_zero.{u} n p ⟨x, hx⟩
      simp only [mem_sphere_iff_norm, sub_zero] at hx ⊢
      rw [hx, one_mul, norm_smul, norm_inv, norm_norm]
      refine inv_mul_cancel₀ (norm_ne_zero_iff.mpr ?_)
      intro xz; change x = 0 at xz; exact xnz xz ⟩

/-- The map `boundaryToQDiskBoundary` has a left inverse. -/
lemma toPDiskBoundary_comp_toQDiskBoundary x :
    toQDiskBoundary n q p (toQDiskBoundary.{u, v} n p q x) = x := by
  unfold toQDiskBoundary
  split; next _ y hy hfx =>
    rcases x with ⟨x, hx⟩
    have hx0 : x ≠ 0 := neq_zero.{u} n p ⟨x, hx⟩
    replace hfx := congrArg ULift.down hfx
    simp only [Subtype.mk.injEq] at hfx
    congr
    simp only [← hfx, WithLp.equiv_symm_smul]
    simp only [norm_smul, norm_mul, norm_norm, norm_inv, mul_inv_rev, inv_inv, smul_smul]
    rw [mul_assoc ‖x‖]
    conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
    simp only [mul_one, ← mul_assoc]
    conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)
    rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr hx0), mul_one]
    conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)
    rw [one_smul]

/-- The map `boundaryToQDiskBoundary` is continuous. -/
lemma continuous_toQDiskBoundary : Continuous (toQDiskBoundary n p q) := by
  refine continuous_uliftUp.comp <| Continuous.subtype_mk ?_ _
  refine Continuous.smul ?_ (continuous_induced_dom.comp continuous_induced_dom)
  apply Continuous.mul (by simp only [norm_eq_of_mem_sphere]; exact continuous_const)
  conv_rhs => intro x; rw [inv_eq_one_div]
  apply Continuous.div continuous_const
  · apply Continuous.norm
    apply @PiLp.continuous_equiv_symm _ _ (fun _ ↦ ℝ) |>.comp
    exact Continuous.subtype_val continuous_induced_dom
  intro x h
  rw [norm_eq_zero] at h
  change x.down.val = 0 at h
  exact (neq_zero n p x) h

/-- `pDiskBounday n p` is homeomorphic to `pDiskBoundary n q`. -/
noncomputable def homeoQDiskBoundary : pDiskBoundary n p ≃ₜ pDiskBoundary n q where
  toFun := toQDiskBoundary n p q
  invFun := toQDiskBoundary n q p
  left_inv := toPDiskBoundary_comp_toQDiskBoundary n p q
  right_inv := toPDiskBoundary_comp_toQDiskBoundary n q p
  continuous_toFun := continuous_toQDiskBoundary n p q
  continuous_invFun := continuous_toQDiskBoundary n q p

noncomputable def isoQDiskBoundary : pDiskBoundary n p ≅ pDiskBoundary n q :=
  isoOfHomeo (homeoQDiskBoundary n p q)

end pDiskBoundary


/-- Homeomorphism from the pair (pDisk n p, pDiskBoundary n p)
to the pair (pDisk n q, pDiskBoundary n q) -/
noncomputable def pDiskPair.homeoQDiskPair :
    CategoryTheory.Arrow.mk (pDiskBoundaryInclusion n p) ≅
    CategoryTheory.Arrow.mk (pDiskBoundaryInclusion n q) :=
  CategoryTheory.Arrow.isoMk' _ _
    (pDiskBoundary.isoQDiskBoundary n p q) (pDisk.isoQDisk n p q) rfl


end TopCat



-- noncomputable def diskHomeoPDisk : 𝔻 n ≃ₜ pDisk n 2 where
--   toFun := id
--   -- invFun := id
--   left_inv := congrFun rfl
--   right_inv := congrFun rfl
--   -- continuous_toFun := continuous_id
--   -- continuous_invFun := continuous_id


namespace TopCat

/-- The large cube $[-1, 1]^n$ is homeomorphic to `pDisk n ∞`
(the disk in `ℝⁿ` according to the `L∞` norm). -/
def largeCubeHomeoPDisk (n : ℕ) : (Fin n → Set.Icc (-1 : ℝ) (1 : ℝ)) ≃ₜ pDisk n ∞ where
  toFun := fun x ↦ ⟨⟨fun i ↦ x i, by
    simp only [Int.toNat_ofNat, Metric.mem_closedBall, PiLp.dist_eq_iSup]
    refine Real.iSup_le ?_ (by norm_num)
    intro i
    simp only [PiLp.zero_apply, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨le_trans (by norm_num) (x i).prop.left, (x i).prop.right⟩ ⟩⟩
  invFun := fun ⟨⟨x, hx⟩⟩ i ↦ ⟨x i, by
    simp only [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_ciSup, Real.norm_eq_abs] at hx
    -- Note: Here we cannot simply use `iSup_le_iff` because `ℝ` is not a `CompleteLattice`.
    -- We cannot use `Finset.le_sup` either, because although `ℝ` is a `SemilatticeSup`,
    -- it does not have a smallest element (i.e., we do not have `[OrderBot ℝ]`).
    -- With these restrictions, `Real.sSup_def`, the supremum of a set of real numbers,
    -- is defined in mathlib to be `0` if the set is not bounded from above or is empty.
    have := Real.forall_le_of_iSup_le_of_finite_domain hx i
    exact ⟨neg_le_of_abs_le this, le_of_max_le_left this⟩ ⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    refine continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)
    exact continuous_pi fun i ↦ Continuous.subtype_val (continuous_apply i)
  continuous_invFun := continuous_pi fun i ↦
    (continuous_apply i).comp continuous_uliftDown.subtype_val |>.subtype_mk _

/-- The large cube $[-1, 1]^n$ is homeomorphic to the cube $[0, 1]^n$. -/
noncomputable def largeCubeHomeoCube (n : ℕ) :
    (Fin n → Set.Icc (-1 : ℝ) (1 : ℝ)) ≃ₜ I^ Fin n :=
  Homeomorph.piCongrRight fun _ ↦ iccHomeoI _ _ (by norm_num)

/-- The n-disk `𝔻 n` is homeomorphic to the cube $[0, 1]^n$. -/
noncomputable def diskHomeoCube (n : ℕ) : TopCat.disk.{u} n ≃ₜ (I^ Fin n) :=
  (pDisk.homeoQDisk.{u, u} n 2 ∞).trans <|
    (largeCubeHomeoPDisk n).symm.trans (largeCubeHomeoCube n)

noncomputable def largeCubeBoundaryHomeoPDiskBoundary.{u} (n : ℕ) :
    { x : Fin n → Set.Icc (-1 : ℝ) (1 : ℝ) | ∃ i, x i = (-1 : ℝ) ∨ x i = (1 : ℝ) } ≃ₜ
      pDiskBoundary n ∞ where
  toFun := fun ⟨x, hx⟩ ↦ ⟨⟨fun i ↦ x i, by
    rw [Metric.mem_sphere, PiLp.dist_eq_iSup]
    apply eq_of_le_of_le
    · refine Real.iSup_le ?_ (by norm_num : (0 : ℝ) ≤ (1 : ℝ))
      simp only [PiLp.zero_apply, dist_zero_right, Real.norm_eq_abs, ge_iff_le]
      exact fun i ↦ abs_le.mpr (x i).property
    · apply Real.le_iSup_of_exists_ge_of_finite_domain
      obtain ⟨i, hi | hi⟩ := hx
      repeat {use i; rw [hi]; simp} ⟩⟩
  invFun := fun ⟨⟨x, hx⟩⟩ ↦
    ⟨fun i ↦ ⟨x i, by
      simp only [mem_sphere_iff_norm, sub_zero, PiLp.norm_eq_ciSup, Real.norm_eq_abs] at hx
      have := Real.forall_le_of_iSup_le_of_finite_domain (le_of_eq hx) i
      exact ⟨neg_le_of_abs_le this, le_of_max_le_left this⟩ ⟩,
    by
      simp only [Set.mem_setOf_eq]
      obtain hn | hn := Nat.eq_zero_or_pos n
      · exfalso
        have : pDiskBoundary.{u} 0 ∞ := by rw [← hn]; exact ⟨x, hx⟩
        exact (pDiskBoundary.instIsEmptyZero.{u} ∞).false this
      simp only [mem_sphere_iff_norm, sub_zero, PiLp.norm_eq_ciSup, Real.norm_eq_abs] at hx
      have : ∃ i, |x i| ≥ 0 := by use ⟨0, hn⟩; simp only [ge_iff_le, abs_nonneg]
      have : ∃ i, |x i| = 1 := Real.exists_eq_of_iSup_eq_of_finite_domain this hx
      obtain ⟨i, hi⟩ := this
      exact ⟨i, Or.symm (eq_or_eq_neg_of_abs_eq hi)⟩ ⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    refine continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)
    refine continuous_pi fun i ↦ Continuous.subtype_val ?_
    exact (continuous_apply i).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i ↦ Continuous.subtype_mk ?_ _
    exact (continuous_apply i).comp continuous_uliftDown.subtype_val

noncomputable def largeCubeBoundaryHomeoCubeBoundary (n : ℕ) :
    { x : Fin n → Set.Icc (-1 : ℝ) (1 : ℝ) | ∃ i, x i = (-1 : ℝ) ∨ x i = (1 : ℝ) } ≃ₜ
      Cube.boundary (Fin n) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨fun i ↦ iccHomeoI (-1 : ℝ) (1 : ℝ) (by norm_num) (x i), by
    obtain ⟨i, hin | hip⟩ := hx
    · use i; left; apply Subtype.eq_iff.mpr; simp [hin]
    · use i; right; apply Subtype.eq_iff.mpr; simp [hip] ⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun i ↦ (iccHomeoI (-1 : ℝ) (1 : ℝ) (by norm_num)).symm (x i), by
    obtain ⟨i, hi0 | hi1⟩ := hx
    · use i; left; simp [hi0]
    · use i; right; simp [hi1] ⟩
  left_inv x := by
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Homeomorph.symm_apply_apply, Subtype.coe_eta]
  right_inv x := by
    simp only [Homeomorph.apply_symm_apply, Subtype.coe_eta]
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    apply (Homeomorph.continuous _).comp
    exact (continuous_apply i).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    apply (Homeomorph.continuous_symm _).comp
    exact (continuous_apply i).comp continuous_subtype_val

noncomputable def diskBoundaryHomeoCubeBoundary (n : ℕ) :
    TopCat.diskBoundary.{u} n ≃ₜ Cube.boundary (Fin n) :=
  (pDiskBoundary.homeoQDiskBoundary.{u, u} n 2 ∞).trans <|
    (largeCubeBoundaryHomeoPDiskBoundary.{u} n).symm.trans (largeCubeBoundaryHomeoCubeBoundary n)

--------------------------------------------------------------------------------------

open CategoryTheory  -- for the notation `≫`

noncomputable def diskIsoCube (n : ℕ) : disk n ≅ TopCat.of (I^ Fin n) :=
  isoOfHomeo (diskHomeoCube n)

noncomputable def diskBoundaryIsoCubeBoundary (n : ℕ) :
    diskBoundary n ≅ TopCat.of <| Cube.boundary (Fin n) :=
  isoOfHomeo (diskBoundaryHomeoCubeBoundary n)

noncomputable def diskPair.homeoCubePair (n : ℕ) :
    CategoryTheory.Arrow.mk (diskBoundaryInclusion n) ≅
    CategoryTheory.Arrow.mk (TopCat.ofHom (Cube.boundaryInclusion n)) :=
  CategoryTheory.Arrow.isoMk' _ _
    (diskBoundaryIsoCubeBoundary n) (diskIsoCube n) rfl

lemma diskPair.homeoCubePair_comm (n : ℕ) :
    (diskBoundaryInclusion n) ≫ (diskPair.homeoCubePair n).hom.right =
    (diskPair.homeoCubePair n).hom.left ≫ TopCat.ofHom (Cube.boundaryInclusion n) := by
  rfl

--------------------------------------------------------------------------------------

noncomputable def diskHomeoCubeULift (n : ℕ) :
    disk.{u} n ≃ₜ cube.{u} n :=
  (diskHomeoCube n).trans Homeomorph.ulift.symm

noncomputable def diskIsoCubeULift (n : ℕ) : disk.{u} n ≅ cube.{u} n :=
  isoOfHomeo (diskHomeoCubeULift n)

noncomputable def diskBoundaryHomeoCubeBoundaryULift (n : ℕ) :
    diskBoundary.{u} n ≃ₜ cubeBoundary.{u} n :=
  (TopCat.diskBoundaryHomeoCubeBoundary n).trans Homeomorph.ulift.symm

noncomputable def diskBoundaryIsoCubeBoundaryULift (n : ℕ) :
    diskBoundary.{u} n ≅ cubeBoundary.{u} n :=
  isoOfHomeo (diskBoundaryHomeoCubeBoundaryULift n)

/-- Homeomorphism from the pair (TopCat.disk.{u} n, TopCat.diskBoundary.{u} n)
to the pair (TopCat.cube.{u} n, TopCat.cubeBoundary.{u} n) -/
noncomputable def diskPair.homeoCubePairULift (n : ℕ) :
    CategoryTheory.Arrow.mk (diskBoundaryInclusion n) ≅
    CategoryTheory.Arrow.mk (cubeBoundaryInclusion n) :=
  CategoryTheory.Arrow.isoMk' _ _
    (diskBoundaryIsoCubeBoundaryULift n) (diskIsoCubeULift n) rfl

lemma diskPair.homeoCubePairULift_comm (n : ℕ) :
    (diskBoundaryInclusion.{u} n) ≫ (diskPair.homeoCubePairULift.{u} n).hom.right =
    (diskPair.homeoCubePairULift.{u} n).hom.left ≫ (cubeBoundaryInclusion.{u} n) := by
  rfl

end TopCat
