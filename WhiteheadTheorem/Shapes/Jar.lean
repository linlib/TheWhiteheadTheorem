import WhiteheadTheorem.Auxiliary
import WhiteheadTheorem.Shapes.Disk
-- import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
-- import Mathlib.CategoryTheory.LiftingProperties.Limits


-- open CategoryTheory
open TopCat
open scoped Topology unitInterval


namespace HEP

-- TODO (?): rewrite using Continuous.piecewise

abbrev Jar (n : ℕ) := 𝔻 n × I

namespace Jar

def mid (n : ℕ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≤ 1 - y / 2}
def rim (n : ℕ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≥ 1 - y / 2}

def closedCover (n : ℕ) : Fin 2 → Set (Jar n) := ![mid n, rim n]

lemma continuous_sub_div_two : Continuous fun (y : ℝ) ↦ 1 - y / 2 :=
  (continuous_sub_left _).comp <| continuous_mul_right _

lemma isClosed_mid (n : ℕ) : IsClosed (mid n) :=
  continuous_iff_isClosed.mp (continuous_uliftDown.subtype_val.norm.prodMap continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <| isClosed_le continuous_fst <|
    continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd

lemma isClosed_rim (n : ℕ) : IsClosed (rim n) :=
  continuous_iff_isClosed.mp (continuous_uliftDown.subtype_val.norm.prodMap continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≥ 1 - y / 2} <| isClosed_le
    (continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd) continuous_fst

noncomputable def midProjToFun (n : ℕ) : mid.{u} n → disk.{u} n := fun p ↦ ⟨{
  -- Note: pattern matching is done inside `toFun` to make `Continuous.subtype_mk` work
  val := match p with
    | ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩, _⟩ => (2 / (2 - y)) • x,
  property := by
    obtain ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _, _⟩ ⟩, hxy⟩ := p
    dsimp only [Int.ofNat_eq_coe, Set.coe_setOf, Set.mem_setOf_eq]
    rw [Metric.mem_closedBall]
    rw [dist_zero_right, norm_smul, norm_div, RCLike.norm_ofNat, Real.norm_eq_abs]
    have : 0 < |2 - y| := lt_of_le_of_ne (abs_nonneg _) (abs_ne_zero.mpr (by linarith)).symm
    rw [← le_div_iff₀' (div_pos (by norm_num) this), one_div, inv_div]
    nth_rw 2 [← (@abs_eq_self ℝ _ 2).mpr (by norm_num)]
    rw [← abs_div, sub_div, div_self (by norm_num), le_abs]
    exact Or.inl hxy }⟩

lemma continuous_midProjToFun (n : ℕ) : Continuous (midProjToFun.{u} n) := by
  refine continuous_uliftUp.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact continuous_smul.comp <| Continuous.prodMk
    (continuous_const.div ((continuous_sub_left _).comp <| continuous_subtype_val.comp <|
      continuous_snd.comp <| continuous_subtype_val) fun ⟨⟨ _, ⟨y, _, _⟩ ⟩, _⟩ ↦ by
        dsimp only [Function.comp_apply, ne_eq]; linarith)
    (continuous_subtype_val.comp <| continuous_uliftDown.comp <| continuous_fst.comp <|
      continuous_subtype_val)

noncomputable def midProj (n : ℕ) : C(mid n, 𝔻 n) :=
  ⟨midProjToFun n, continuous_midProjToFun n⟩

lemma rim_fst_ne_zero (n : ℕ) : ∀ p : rim n, ‖p.val.fst.down.val‖ ≠ 0 :=
  fun ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _, _⟩ ⟩, hxy⟩ ↦ by
    conv => lhs; arg 1; dsimp
    change ‖x‖ ≥ 1 - y / 2 at hxy
    linarith

noncomputable def rimProjFstToFun (n : ℕ) : rim.{u} n → diskBoundary.{u} n := fun p ↦ ⟨{
  val := match p with
    | ⟨⟨ ⟨⟨x, _⟩⟩, _ ⟩, _⟩ => (1 / ‖x‖) • x
  property := by
    obtain ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, yl, yr⟩ ⟩, hxy⟩ := p
    simp only [one_div, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
    change ‖x‖ ≥ 1 - y / 2 at hxy
    exact inv_mul_cancel₀ (by linarith) }⟩

lemma continuous_rimProjFstToFun (n : ℕ) : Continuous (rimProjFstToFun n) := by
  refine continuous_uliftUp.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact continuous_smul.comp <| Continuous.prodMk
    (Continuous.div continuous_const (continuous_norm.comp <| continuous_subtype_val.comp <|
      continuous_uliftDown.comp <| continuous_fst.comp <| continuous_subtype_val) <|
        rim_fst_ne_zero n)
    (continuous_subtype_val.comp <| continuous_uliftDown.comp <| continuous_fst.comp <|
      continuous_subtype_val)

noncomputable def rimProjFst (n : ℕ) : C(rim n, ∂𝔻 n) :=
  ⟨rimProjFstToFun n, continuous_rimProjFstToFun n⟩

noncomputable def rimProjSndToFun (n : ℕ) : rim n → I := fun p ↦ {
  val := match p with
    | ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩, _⟩ => (y - 2) / ‖x‖ + 2
  property := by
    obtain ⟨⟨ ⟨⟨x, hx⟩⟩, ⟨y, _, _⟩ ⟩, hxy⟩ := p
    simp only [Set.mem_Icc]
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    change ‖x‖ ≥ 1 - y / 2 at hxy
    have : ‖x‖ > 0 := by linarith
    constructor
    all_goals rw [← add_le_add_iff_right (-2)]
    · rw [← neg_le_neg_iff, add_neg_cancel_right, zero_add, neg_neg]
      rw [← neg_div, neg_sub, div_le_iff₀ (by assumption)]; linarith
    · rw [add_assoc, add_neg_cancel, add_zero, div_le_iff₀ (by assumption)]; linarith}

lemma continuous_rimProjSndToFun (n : ℕ) : Continuous (rimProjSndToFun n) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_add_right _).comp <| Continuous.div
    ((continuous_sub_right _).comp <| continuous_subtype_val.comp <|
      continuous_snd.comp <| continuous_subtype_val)
    (continuous_norm.comp <| continuous_subtype_val.comp <| continuous_uliftDown.comp <|
      continuous_fst.comp <| continuous_subtype_val) <| rim_fst_ne_zero n

noncomputable def rimProjSnd (n : ℕ) : C(rim n, I) :=
  ⟨rimProjSndToFun n, continuous_rimProjSndToFun n⟩

noncomputable def rimProj (n : ℕ) : C(rim n, ∂𝔻 n × I) :=
  ContinuousMap.prodMk (rimProjFst n) (rimProjSnd n)

noncomputable def proj (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (f : C(𝔻 n, Y)) (H: C(∂𝔻 n × I, Y)) : ∀ i, C(closedCover n i, Y) :=
  Fin.cons (f.comp (midProj n)) <| Fin.cons (H.comp (rimProj n)) finZeroElim

lemma proj_compatible (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (f : C(𝔻 n, Y)) (H: C(∂𝔻 n × I, Y)) (hf: f ∘ diskBoundaryInclusion n = H ∘ (·, 0)) :
    ∀ (p : Jar n) (hp0 : p ∈ closedCover n 0) (hp1 : p ∈ closedCover n 1),
    proj n f H 0 ⟨p, hp0⟩ = proj n f H 1 ⟨p, hp1⟩ :=
  fun ⟨⟨⟨x, hx⟩⟩, ⟨y, hy0, hy1⟩⟩ hp0 hp1 ↦ by
    change f (midProj n _) = H (rimProj n _)
    change ‖x‖ ≤ 1 - y / 2 at hp0
    change ‖x‖ ≥ 1 - y / 2 at hp1
    have : ‖x‖ = 1 - y / 2 := by linarith
    let q : ∂𝔻 n := ⟨ (2 / (2 - y)) • x, by
      simp only [mem_sphere_iff_norm, sub_zero, norm_smul, norm_div, RCLike.norm_ofNat,
        Real.norm_eq_abs]
      rw [this, abs_of_pos (by linarith), div_mul_eq_mul_div, div_eq_iff (by linarith)]
      rw [mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul, one_mul] ⟩
    conv in midProj n _ => equals diskBoundaryInclusion n q =>
      unfold diskBoundaryInclusion midProj midProjToFun
      simp only [Fin.isValue, ContinuousMap.coe_mk, hom_ofHom]
      congr
    conv in rimProj n _ => equals (q, 0) =>
      unfold rimProj rimProjFst rimProjFstToFun rimProjSnd rimProjSndToFun
      dsimp only [Int.ofNat_eq_coe, ContinuousMap.prod_eval, ContinuousMap.coe_mk]
      conv => rhs; change (q, ⟨0, by norm_num, by norm_num⟩)
      congr 2
      · congr 2
        rw [this, div_eq_div_iff (by linarith) (by linarith)]
        rw [one_mul, mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul]
      · rw [this, ← eq_sub_iff_add_eq, zero_sub, div_eq_iff (by linarith), mul_sub, mul_one]
        rw [mul_div, mul_div_right_comm, neg_div_self (by norm_num), ← neg_eq_neg_one_mul]
        rw [sub_neg_eq_add, add_comm]; rfl
    change (f ∘ diskBoundaryInclusion n) q = (H ∘ (·, 0)) q
    rw [hf]

lemma proj_compatible' (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (f : C(𝔻 n, Y)) (H: C(∂𝔻 n × I, Y)) (hf: f ∘ diskBoundaryInclusion n = H ∘ (·, 0)) :
    ∀ (i j) (p : Jar n) (hpi : p ∈ closedCover n i) (hpj : p ∈ closedCover n j),
    proj n f H i ⟨p, hpi⟩ = proj n f H j ⟨p, hpj⟩ := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ p hpi hpj
  interval_cases i <;> (interval_cases j <;> (try simp only [Fin.zero_eta, Fin.mk_one]))
  · exact proj_compatible n f H hf p hpi hpj
  · exact Eq.symm <| proj_compatible n f H hf p hpj hpi

lemma closedCover_is_cover (n : ℕ) : ∀ (p : Jar n), ∃ i, p ∈ closedCover n i :=
  fun ⟨⟨x, _⟩, ⟨y, _⟩⟩ ↦ by
    by_cases h : ‖x‖ ≤ 1 - y / 2
    · use 0; exact h
    · use 1; change ‖x‖ ≥ 1 - y / 2; linarith

lemma closedCover_isClosed (n : ℕ) : ∀ i, IsClosed (closedCover n i) := fun ⟨i, hi⟩ ↦ by
  interval_cases i
  exacts [isClosed_mid n, isClosed_rim n]

noncomputable def homotopyExtension (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (f : C(𝔻 n, Y)) (H: C(∂𝔻 n × I, Y))
    (hf: f ∘ diskBoundaryInclusion n = H ∘ (·, 0)) : C(Jar n, Y) :=
  ContinuousMap.liftCoverClosed (closedCover n) (proj n f H) (proj_compatible' n f H hf)
    (closedCover_is_cover n) (closedCover_isClosed n)

-- The triangle involving the bottom (i.e., `𝔻 (n + 1)`) of the jar commutes.
lemma homotopyExtension_bottom_commutes (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (f : C(𝔻 n, Y)) (H: C(∂𝔻 n × I, Y)) (hf: f ∘ diskBoundaryInclusion n = H ∘ (·, 0)) :
    ⇑f = homotopyExtension n f H hf ∘ (·, 0) := by
  ext p
  change _ = homotopyExtension n f H hf (p, 0)
  have hp : (p, 0) ∈ closedCover n 0 := by
    obtain ⟨x, hx⟩ := p
    change ‖x‖ ≤ 1 - 0 / 2
    rw [zero_div, sub_zero]
    exact mem_closedBall_zero_iff.mp hx
  conv_rhs => equals (proj n f H 0) ⟨(p, 0), hp⟩ => apply ContinuousMap.liftCoverClosed_coe'
  simp only [Int.ofNat_eq_coe, proj, TopCat.coe_of, Fin.succ_zero_eq_one, Fin.cons_zero,
    ContinuousMap.comp_apply]
  congr
  change p = midProjToFun n ⟨(p, 0), hp⟩
  obtain ⟨x, hx⟩ := p
  simp only [Int.ofNat_eq_coe, midProjToFun, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, one_smul]

-- The triangle involving the wall (i.e., `𝕊 n × I`) of the jar commutes.
lemma homotopyExtension_wall_commutes (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (f : C(𝔻 n, Y)) (H: C(∂𝔻 n × I, Y)) (hf: f ∘ diskBoundaryInclusion n = H ∘ (·, 0)) :
    ⇑H = homotopyExtension n f H hf ∘ Prod.map (diskBoundaryInclusion n) id := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  let q := diskBoundaryInclusion n ⟨x, hx⟩
  change _ = homotopyExtension n f H hf ⟨q, ⟨y, hy⟩⟩
  have hq : ⟨q, ⟨y, hy⟩⟩ ∈ closedCover n 1 := by
    change ‖x‖ ≥ 1 - y / 2
    rw [mem_sphere_zero_iff_norm.mp hx]
    obtain ⟨_, _⟩ := hy
    linarith
  conv_rhs => equals (proj n f H 1) ⟨⟨q, ⟨y, hy⟩⟩, hq⟩ => apply ContinuousMap.liftCoverClosed_coe'
  simp only [proj, Fin.succ_zero_eq_one, Fin.cons_one, Fin.cons_zero, ContinuousMap.comp_apply]
  congr
  · dsimp only [rimProjFst, diskBoundaryInclusion, ContinuousMap.coe_mk, rimProjFstToFun, one_div,
      q]
    rw [mem_sphere_zero_iff_norm.mp hx, div_one, one_smul]
  · dsimp only [diskBoundaryInclusion, q]
    rw [mem_sphere_zero_iff_norm.mp hx, div_one, sub_add_cancel]

-- def HomotopyExtensionProperty {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
--     (i : C(A, X)) : Prop :=
--   ∀ {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (H : C(A × I, Y)), f ∘ i = H ∘ (·, 0) →
--   ∃ H' : C(X × I, Y), ⇑f = ⇑H' ∘ (·, 0) ∧ ⇑H = ⇑H' ∘ Prod.map i id

-- theorem hep_sphereInclusion (n : ℕ) : HomotopyExtensionProperty (diskBoundaryInclusion.{u} n).hom :=
--   fun f H hf ↦ ⟨jarHomotopyExtension n f H hf, jarHomotopyExtension_bottom_commutes n f H hf,
--     jarHomotopyExtension_wall_commutes n f H hf⟩

end Jar

end HEP
