import WhiteheadTheorem.Compressible.Defs
import WhiteheadTheorem.Shapes.MappingCylinder
import WhiteheadTheorem.HomotopyGroup.ChangeBasePt
import WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
import WhiteheadTheorem.HEP.CubeJar
import Mathlib.Topology.Homotopy.Contractible

/-!
This file proves that if `f : C(X, Y)` is a weak homotopy equivalence,
then the inclusion map `MapCyl.domInclFromTop` from `X` to the mapping cylinder of `f`
is `n`-compressible for every natural number `n`, i.e.,
it is compressible with respect to `TopCat.diskBoundaryInclusion n : ∂𝔻 n ⟶ 𝔻 n`
for each `n`.
-/

open CategoryTheory TopCat
open scoped unitInterval ContinuousMap Topology Topology.Homotopy


section unique_pi_mapCyl

universe u

-- variable (n : ℕ) {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
-- variable (x₀ : X)
-- variable (f : C(X, Y))
variable (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (x₀ : X)

namespace HomotopyGroup

/-- If the map `πₙ(X, x₀) ⟶ πₙ(Y, f x₀)` induced by `f` is an isomorphism,
then the map `πₙ(X, x₀) ⟶ πₙ(MapCyl f, ⋯)` induced by inclusion into the mapping cylinder
is an isomorphism. -/
lemma isIso_inducedPointedHom'_mapCyl_domIncl_of_isIso
    (hf : IsIso <| inducedPointedHom' n x₀ f) :
    IsIso <| inducedPointedHom' n x₀ (MapCyl.domIncl f) := by
  have f_i_r := inducedPointedHom'_comp_isoTarget_eq_comp n x₀ (MapCyl.domIncl_retr_eq f).symm
  have iso_r : IsIso <| inducedPointedHom' n ((MapCyl.domIncl f).hom x₀) (MapCyl.retr f) := by
    apply isIso_inducedPointedHom'_of_isHomotopyEquiv
    exact MapCyl.isHomotopyEquiv_retr f
  replace f_i_r := (IsIso.comp_inv_eq _).mpr f_i_r
  rw [← f_i_r]
  infer_instance  -- `IsIso.comp_isIso` and `IsIso.inv_isIso`

/-- If the map `πₙ(X, x₀) ⟶ πₙ(Y, f x₀)` induced by `f` is an isomorphism,
then the map `πₙ(X, MapCyl.top f) ⟶ πₙ(MapCyl f, ⋯)` induced by
the inclusion `domInclFromTop f : C(top f, MapCyl f)` is an isomorphism. -/
lemma isIso_inducedPointedHom_mapCyl_domInclFromTop_of_isIso
    (hf : IsIso <| inducedPointedHom' n x₀ f) :
    IsIso <| inducedPointedHom n (MapCyl.domInclToTop f x₀) (MapCyl.domInclFromTop f) := by
  replace hf := isIso_inducedPointedHom'_mapCyl_domIncl_of_isIso _ _ _ hf
  have i_it_if := inducedPointedHom_comp_isoTarget_eq_comp n x₀
    (MapCyl.domIncl_hom_eq_domInclFromTop_comp_domInclToTop f)
  have iso_it : IsIso <| inducedPointedHom n x₀ (MapCyl.domInclToTop f) := by
    apply HomotopyGroup.isIso_inducedPointedHom'_of_isHomeomorph
    exact MapCyl.isHomeomorph_domInclToTop f
  replace i_it_if := (IsIso.inv_comp_eq _).mpr i_it_if
  rw [← i_it_if]
  infer_instance

end HomotopyGroup


namespace RelHomotopyGroup

open HomotopyGroup

lemma inducedPointedHom_subtype_val_eq_iStar
    (n : ℕ) {X : Type u} [TopologicalSpace X] (A : Set X) (a : A) :
    ⇑(inducedPointedHom n a (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))) =
      iStar n X A a :=
  rfl

-- lemma inducedPointedHom_domInclFromTop_eq_iStar :
--     ⇑(inducedPointedHom n (MapCyl.domInclToTop f x₀) (MapCyl.domInclFromTop f)) =
--     iStar n (MapCyl f) (MapCyl.top f) (MapCyl.domInclToTop f x₀) := by
--   apply inducedPointedHom_subtype_val_eq_iStar

/-- If the map `πₙ(X, x₀) ⟶ πₙ(Y, f x₀)` induced by `f` is an isomorphism,
then the map `iStar : πₙ(X, MapCyl.top f) → πₙ(MapCyl f, ⋯)` is bijective. -/
lemma bijective_iStar_mapCyl_of_isIso
    (hf : IsIso <| inducedPointedHom' n x₀ f) :
    Function.Bijective <| iStar n (MapCyl f) (MapCyl.top f) (MapCyl.domInclToTop f x₀) := by
  rw [← inducedPointedHom_subtype_val_eq_iStar]
  apply (Pointed.isIso_iff_bijective _).mp
  apply isIso_inducedPointedHom_mapCyl_domInclFromTop_of_isIso
  exact hf

/-- If `f` is a weak homotopy equivalence, then the relative homotopy group
`π﹍ n (MapCyl f) (MapCyl.top f) (MapCyl.domInclToTop f x₀)` is zero for all `n ≥ 1` and `x`. -/
theorem unique_pi_mapCyl_of_isWeakHomotopyEquiv (hf : IsWeakHomotopyEquiv f.hom) :
    Nonempty <| Unique <| π﹍ (n + 1) (MapCyl f) (MapCyl.top f) (MapCyl.domInclToTop f x₀) := by
  replace hf := isIso_inducedPointedHom_of_isWeakHomotopyEquiv hf
  exact ExactSeq.unique_mid_of_five
    (iStar (n + 1) _ _ _)
    (jStar (n + 1) _ _ _)
    (bd     n      _ _ _)
    (iStar  n      _ _ _)
    (bijective_iStar_mapCyl_of_isIso _ _ _ (hf (n + 1) _)).surjective
    (bijective_iStar_mapCyl_of_isIso _ _ _ (hf  n      _)).injective
    (isExactAt_iStar_jStar n _ _ _)
    (isExactAt_jStar_bd    n _ _ _)
    (isExactAt_bd_iStar    n _ _ _)

end RelHomotopyGroup

end unique_pi_mapCyl



namespace Cube

variable {n : ℕ} (X : Type u) [TopologicalSpace X] (A : Set X)

/-- A continuous map from the `n`-dimensional cube to `X` is called a map of pairs to `(X, A)`
if it sends the boundary `∂I^n` into `A`. -/
abbrev IsMapOfPairs (f : C(I^ Fin n, X)) : Prop := ∀ y ∈ ∂I^n, f y ∈ A

/-- For `n ≥ 1`, if `f` is a continuous map of pairs from `(I^ Fin n, ∂I^n)` to `(X, A)`,
then it is as a map of pairs homotopic to a `RelGenLoop`. -/
lemma exists_relGenLoop_homotopicWith_isMapOfPairs
    (f : C(I^ Fin (n + 1), X)) (hf : IsMapOfPairs X A f) :
    ∃ a : A, ∃ g : RelGenLoop (n + 1) X A a, f.HomotopicWith g fun h ↦ IsMapOfPairs X A h := by
  let fb : C(∂I^(n + 1), A) := ⟨fun y ↦ ⟨f y, hf y y.property⟩, by fun_prop⟩
  let fj : C(⊔I^(n + 1), A) := fb.comp <| boundaryJarInclusionToBoundary (n + 1)
  obtain ⟨y₀, Hfj⟩ := contractible_iff_id_nullhomotopic (⊔I^(n + 1)) |>.mp
    instContractibleSpaceBoundaryJar
  replace Hfj := Hfj.some.hcomp (ContinuousMap.Homotopy.refl fj)
  simp only [ContinuousMap.comp_id, ContinuousMap.comp_const] at Hfj
  let a₀ : A := ⟨fj y₀, by
    change f y₀ ∈ A
    apply hf
    exact Cube.boundaryJar_subset_boundary _ y₀.property ⟩
  use a₀
  let fb' : C(∂𝕀 (n + 1), A) := fb.comp ⟨ULift.down.{u}, continuous_uliftDown⟩
  let Hfj' : C((⊔𝕀 (n + 1)) × I, A) := Hfj.toContinuousMap.argSwap.comp <|
    ContinuousMap.prodMap ⟨ULift.down.{u}, continuous_uliftDown⟩ (ContinuousMap.id _)
  have : ⇑fb' ∘ (cubeBoundaryJarInclusionToBoundary (n + 1)).hom = ⇑Hfj' ∘ fun x ↦ (x, 0) := by
    unfold cubeBoundaryJarInclusionToBoundary boundaryJarInclusionToBoundary
    ext y
    simp only [ContinuousMap.coe_mk, hom_ofHom, Function.comp_apply]
    unfold fb' fb Hfj' ContinuousMap.argSwap
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.comp_assoc,
      ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
      ContinuousMap.prodSwap_apply, ContinuousMap.Homotopy.coe_toContinuousMap,
      ContinuousMap.Homotopy.apply_zero]
    rfl
  obtain ⟨H1, H1prop⟩ := cubeBoundaryJarInclusionToBoundary_hasHEP n A fb' Hfj' this
  -- `fb : C(∂I^(n + 1), X)` is homotopic through `H1` to a map that sends `⊔I^(n + 1)` to `a₀`.
  let f' : C(𝕀 (n + 1), X) := f.comp ⟨ULift.down.{u}, continuous_uliftDown⟩
  let H1' : C((∂𝕀 (n + 1)) × I, X) := ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ H1
  have := cubeBoundaryInclusion_hasHEP (n + 1) X f'
  replace : ⇑f' ∘ (cubeBoundaryInclusion (n + 1)).hom = ⇑H1' ∘ fun x ↦ (x, 0) := by
    unfold cubeBoundaryInclusion f' H1'
    ext ⟨y, hy⟩
    simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, hom_ofHom, Function.comp_apply]
    change f y = _
    have := congr_fun H1prop.left ⟨⟨y, hy⟩⟩
    simp only [Function.comp_apply] at this
    rw [← this]
    rfl
  obtain ⟨H2, H2prop⟩ := cubeBoundaryInclusion_hasHEP (n + 1) X f' H1' this
  -- `f : C(I^ Fin (n + 1), X)` is homotopic through `H2` to a map that
  -- sends `∂I^(n + 1)` to `A` and `⊔I^(n + 1)` to `a₀`.
  let g : C(I^ Fin (n + 1), X) := ⟨fun y ↦ H2 ⟨⟨y⟩, 1⟩, by fun_prop⟩
  have gprop : g ∈ RelGenLoop (n + 1) X A a₀ := by
    unfold g
    constructor
    · intro y hy
      simp only [ContinuousMap.coe_mk]
      have := congr_fun H2prop.right ⟨⟨y, hy⟩, 1⟩
      simp only [cubeBoundaryInclusion, hom_ofHom, Function.comp_apply, Prod.map_apply,
        id_eq] at this
      change _ = H2 ({ down := y }, 1) at this
      rw [← this]
      unfold H1'
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Subtype.coe_prop]
    · intro y hy
      have hy' := boundaryJar_subset_boundary _ hy
      simp only [ContinuousMap.coe_mk]
      have := congr_fun H2prop.right ⟨⟨y, hy'⟩, 1⟩
      simp only [cubeBoundaryInclusion, hom_ofHom, Function.comp_apply, Prod.map_apply,
        id_eq] at this
      change _ = H2 ({ down := y }, 1) at this
      rw [← this]
      replace := congr_fun H1prop.right ⟨⟨y, hy⟩, 1⟩
      simp only [cubeBoundaryJarInclusionToBoundary, boundaryJarInclusionToBoundary,
        ContinuousMap.coe_mk, hom_ofHom, Function.comp_apply, Prod.map_apply, id_eq] at this
      change _ = H1 ({ down := ⟨y, hy'⟩ }, 1) at this
      unfold H1'
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [← this]
      unfold Hfj' ContinuousMap.argSwap a₀
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
        ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
        ContinuousMap.prodSwap_apply, ContinuousMap.Homotopy.coe_toContinuousMap,
        ContinuousMap.Homotopy.apply_one, ContinuousMap.const_apply]
  use ⟨g, gprop⟩
  exact Nonempty.intro <|
    { toContinuousMap := H2.argSwap.comp <|
        (ContinuousMap.id _).prodMap ⟨ULift.up, continuous_uliftUp⟩
      map_zero_left y := by
        unfold ContinuousMap.argSwap
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_assoc, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
          Prod.map_apply, id_eq, ContinuousMap.prodSwap_apply]
        have := congr_fun H2prop.left ⟨y⟩
        change _ = H2 ({ down := y }, 0)  at this
        rw [← this]
        rfl
      map_one_left y := by
        unfold ContinuousMap.argSwap g
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_assoc, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
          Prod.map_apply, id_eq, ContinuousMap.prodSwap_apply]
      prop' t y hy := by
        unfold ContinuousMap.argSwap
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_assoc, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
          Prod.map_apply, id_eq, ContinuousMap.prodSwap_apply]
        have := congr_fun H2prop.right ⟨⟨y, hy⟩, t⟩
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, cubeBoundaryInclusion, hom_ofHom,
          Function.comp_apply, Prod.map_apply, id_eq, H1'] at this
        change _ = H2 ({ down := y }, t) at this
        rw [← this]
        exact Subtype.coe_prop (H1 ({ down := ⟨y, hy⟩ }, t)) }

lemma homotopicWith_isMapOfPairs_of_relGenLoop_homotopic
    {X : Type u} [TopologicalSpace X] {A : Set X}
    {a : A} {f g : RelGenLoop n X A a} (fg : RelGenLoop.Homotopic f g) :
    f.val.HomotopicWith g.val fun h ↦ IsMapOfPairs X A h := by
  replace fg := fg.some
  exact Nonempty.intro <|
    { toHomotopy := fg.toHomotopy
      prop' t y hy := (fg.prop' t).left y hy }

/-- Suppose `n ≥ 1` and the relative homotopy group `π﹍ n X A a` is zero for all `a : A`.
If `f` is a continuous map of pairs from `(I^ Fin n, ∂I^n)` to `(X, A)`,
then it is as a map of pairs homotopic to a constant map. -/
theorem homotopicWith_const_isMapOfPairs_of_unique_pi
    (f : C(I^ Fin (n + 1), X)) (hf : IsMapOfPairs X A f)
    (hpi : ∀ a : A, Nonempty <| Unique <| π﹍ (n + 1) X A a) :
    ∃ a : A, f.HomotopicWith (ContinuousMap.const _ a) fun h ↦ IsMapOfPairs X A h := by
  obtain ⟨a, g, H⟩ := exists_relGenLoop_homotopicWith_isMapOfPairs X A f hf
  have g0 := (hpi a |>.some.uniq ⟦g⟧).trans (hpi a |>.some.uniq ⟦RelGenLoop.const⟧).symm
  rw [Quotient.eq] at g0
  change RelGenLoop.Homotopic .. at g0
  use a
  exact H.trans <| homotopicWith_isMapOfPairs_of_relGenLoop_homotopic g0

end Cube


namespace TopCat.disk

open TopCat

variable {n : ℕ} (X : Type u) [TopologicalSpace X] (A : Set X)

/-- A continuous map from the `n`-dimensional disk to `X` is called a map of pairs to `(X, A)`
if it sends the boundary `∂𝔻 n` into `A`. -/
abbrev IsMapOfPairs (f : C(𝔻 n, X)) : Prop := ∀ y : ∂𝔻 n, f (diskBoundaryInclusion n y) ∈ A

/-- Suppose `n ≥ 1` and the relative homotopy group `π﹍ n X A a` is zero for all `a : A`.
If `f` is a continuous map of pairs from `(∂𝔻 n, 𝔻 n)` to `(X, A)`,
then it is as a map of pairs homotopic to a constant map. -/
theorem homotopicWith_const_isMapOfPairs_of_unique_pi
    (f : C(disk.{u} (n + 1), X)) (hf : IsMapOfPairs X A f)
    (hpi : ∀ a : A, Nonempty <| Unique <| π﹍ (n + 1) X A a) :
    ∃ a : A, f.HomotopicWith (ContinuousMap.const _ a) fun h ↦ IsMapOfPairs X A h := by
  let e := diskPair.homeoCubePairULift.{u} (n + 1)
  let idown : C(𝕀 (n + 1), I^ Fin (n + 1)) := ⟨ULift.down.{u}, continuous_uliftDown⟩
  let iup : C(I^ Fin (n + 1), 𝕀 (n + 1)) := ⟨ULift.up.{u}, continuous_uliftUp⟩
  let i_d : C(I^ Fin (n + 1), 𝔻 (n + 1)) := e.inv.right.hom.comp iup
  let d_i : C(𝔻 (n + 1), I^ Fin (n + 1)) := idown.comp e.hom.right.hom
  let f' : C(I^ Fin (n + 1), X) := f.comp i_d
  have hf' : Cube.IsMapOfPairs X A f' := fun y hy ↦ by
    unfold f' i_d iup
    simp only [Arrow.mk_right, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    change f ( (cubeBoundaryInclusion (n + 1) ≫ e.inv.right) ⟨⟨y, hy⟩⟩ ) ∈ A
    change f ( (e.inv.left ≫ diskBoundaryInclusion (n + 1)) ⟨⟨y, hy⟩⟩ ) ∈ A
    change f ( diskBoundaryInclusion (n + 1) <| e.inv.left ⟨⟨y, hy⟩⟩ ) ∈ A  -- CategoryTheory.Arrow.iso_w e
    apply hf
  obtain ⟨a, H⟩ := Cube.homotopicWith_const_isMapOfPairs_of_unique_pi X A f' hf' hpi
  use a
  replace H := H.some
  let H' := (ContinuousMap.Homotopy.refl d_i).hcomp H.toHomotopy
  have f'_d_i : f'.comp d_i = f := by
    unfold f' d_i i_d
    simp only [Arrow.mk_right, ContinuousMap.comp_assoc]
    change _ = f.comp (ContinuousMap.id _)
    congr 1
    change e.inv.right.hom.comp ((iup.comp idown).comp e.hom.right.hom) = _
    rw [(by rfl : iup.comp idown = ContinuousMap.id _), ContinuousMap.id_comp]
    change (e.hom.right ≫ e.inv.right).hom = _
    simp only [Arrow.mk_right, Arrow.hom_inv_id_right, hom_id]
  exact Nonempty.intro <|
    { toContinuousMap := H'.toContinuousMap
      map_zero_left x := by rw [H'.map_zero_left x, f'_d_i]
      map_one_left x := by rw [H'.map_one_left x]; rfl
      prop' t x := by
        unfold H' d_i diskBoundaryInclusion
        simp only [Arrow.mk_right, ContinuousMap.toFun_eq_coe,
          ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.hcomp_apply,
          ContinuousMap.Homotopy.refl_apply, ContinuousMap.comp_apply,
          ContinuousMap.HomotopyWith.coe_toHomotopy, hom_ofHom, ContinuousMap.coe_mk]
        apply H.prop' t
        change idown ((diskBoundaryInclusion (n + 1) ≫ e.hom.right) x) ∈ _
        change idown ((e.hom.left ≫ cubeBoundaryInclusion (n + 1)) x) ∈ _  -- diskPair.homeoCubePairULift_comm
        change idown (cubeBoundaryInclusion (n + 1) (e.hom.left x)) ∈ ∂I^n + 1
        have : ∀ z, idown (cubeBoundaryInclusion (n + 1) z) ∈ ∂I^n + 1 := by
          intro ⟨z, hz⟩
          unfold idown cubeBoundaryInclusion
          simp only [hom_ofHom, ContinuousMap.coe_mk]
          simp_all only [Subtype.forall, Arrow.mk_right, ContinuousMap.comp_assoc, f', i_d, e, iup, d_i, idown]
          obtain ⟨val, property⟩ := a
          obtain ⟨val_1, property_1⟩ := t
          simp_all only [Set.mem_Icc]
          obtain ⟨left, right⟩ := property_1
          exact hz
        apply this }

noncomputable def _root_.TopCat.Cyl.stretchToWall :
    C(I × (disk.{u} (n + 1)), I × (disk.{u} (n + 1))) := by
  let β : C((disk.{u} (n + 1)) × I, ℝ) :=
    { toFun := fun ⟨⟨x, hx⟩, t⟩ ↦ max (2 * ‖x‖) (2 - t)
      continuous_toFun := by fun_prop }
  refine
    { toFun := fun ⟨t, ⟨x, hx⟩⟩ ↦
        ⟨ ⟨2 - β ⟨⟨x, hx⟩, t⟩, ?_⟩, ⟨(2 / β ⟨⟨x, hx⟩, t⟩) • x, ?_⟩ ⟩
      continuous_toFun := ?_ }
  · simp only [ContinuousMap.coe_mk, Set.mem_Icc, sub_nonneg, sup_le_iff, Nat.ofNat_pos,
    mul_le_iff_le_one_right, tsub_le_iff_right, le_add_iff_nonneg_right, β]
    have t1 : 1 ≤ ((2 : ℝ) - t.val) := by linarith only [t.property.right]
    constructor
    · constructor
      · have := mem_closedBall_iff_norm.mp hx
        simp_all only [Metric.mem_closedBall, dist_zero_right, sub_zero]
      · exact t.property.left
    · by_cases hxt : 2 * ‖x‖ ≥ 2 - t
      · simp only [hxt, sup_of_le_left]
        have := t1.trans hxt
        replace := (add_le_add_iff_left 1).mpr this
        convert this
        norm_num
      · replace hxt := le_of_not_ge hxt
        simp only [hxt, sup_of_le_right, ge_iff_le]
        convert (add_le_add_iff_left 1).mpr t1
        norm_num
  · simp only [ContinuousMap.coe_mk, Metric.mem_closedBall, dist_zero_right, β]
    by_cases hxt : 2 * ‖x‖ ≥ 2 - t
    · simp only [hxt, sup_of_le_left]
      rw [div_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_le_one
    · replace hxt := le_of_not_ge hxt
      simp only [hxt, sup_of_le_right, ge_iff_le]
      rw [norm_smul]
      replace hxt := le_div_iff₀' (by norm_num : (2 : ℝ) > 0) |>.mpr hxt
      replace hxt := mul_le_mul_of_nonneg_left hxt (norm_nonneg _ : ‖(2 : ℝ) / (2 - t)‖ ≥ 0)
      convert hxt
      have : ‖(2 : ℝ) / (2 - t)‖ = (2 : ℝ) / (2 - t) := by
        apply Real.norm_of_nonneg
        exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith only [t.property.right])
      rw [this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_div_cancel₀']
      apply Eq.symm
      apply div_self
      linarith only [t.property.right]
  · simp only [ContinuousMap.coe_mk, β]
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply Continuous.sub
      · exact continuous_const
      · fun_prop
    · apply continuous_uliftUp.comp
      apply Continuous.subtype_mk
      apply Continuous.smul
      · apply Continuous.div
        · exact continuous_const
        · apply Continuous.max
          · fun_prop
          · fun_prop
        · intro ⟨t, ⟨x, hx⟩⟩
          dsimp only
          have t1 : 0 < ((2 : ℝ) - t.val) := by linarith only [t.property.right]
          apply ne_of_gt
          exact lt_sup_of_lt_right t1
      · fun_prop

lemma _root_.TopCat.Cyl.stretchToWall_eq_zero_of_norm_eq_one
    {n : ℕ} {t : I} {x : EuclideanSpace ℝ (Fin (n + 1))} {hx : x ∈ Metric.closedBall 0 1}
    (hx1 : ‖x‖ = 1) : Cyl.stretchToWall ⟨t, ⟨x, hx⟩⟩ = ⟨0, ⟨x, hx⟩⟩ := by
  unfold Cyl.stretchToWall
  simp only [ContinuousMap.coe_mk, hx1, mul_one, Prod.mk.injEq]
  have : 2 ≥ 2 - t.val := by linarith only [t.property.left]
  simp only [this, sup_of_le_left, sub_self, Set.Icc.mk_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, one_smul, and_self]

/-- Suppose `n ≥ 1` and `f` is a continuous map of pairs from `(∂𝔻 n, 𝔻 n)` to `(X, A)`.
If `f` is as a map of pairs homotopic to a map into `A`,
then `f` is relative to `∂𝔻 n` homotopic to a map into `A`. -/
theorem homotopicRel_boundary_of_homotopicWith_isMapOfPairs
    (f : C(disk.{u} (n + 1), X))  -- (hf : IsMapOfPairs X A f)
    (H : ∃ g : C(disk.{u} (n + 1), X),
      Set.range g ⊆ A ∧ f.HomotopicWith g fun h ↦ IsMapOfPairs X A h) :
    ∃ l : C(disk.{u} (n + 1), X),
      Set.range l ⊆ A ∧ f.HomotopicRel l (Set.range (diskBoundaryInclusion _)) := by
  obtain ⟨g, gA, H⟩ := H
  replace H := H.some
  let H' := H.toContinuousMap.comp Cyl.stretchToWall
  let l : C(disk.{u} (n + 1), X) := ⟨fun x ↦ H' ⟨1, x⟩, by fun_prop⟩
  use l
  constructor
  · apply Set.range_subset_iff.mpr
    intro ⟨x, hx⟩
    unfold l H' Cyl.stretchToWall
    simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.HomotopyWith.coe_toHomotopy,
      Set.Icc.coe_one]
    simp only [(by norm_num : (2 : ℝ) - 1 = 1)]
    by_cases hx1 : 2 * ‖x‖ ≥ 1
    · simp only [hx1, sup_of_le_left]
      simp only [div_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)]
      generalize_proofs pf1 pf2
      have xmem : ‖x‖⁻¹ • x ∈ Metric.sphere 0 1 := by
        apply Metric.mem_sphere.mpr
        rw [dist_eq_norm, sub_zero, norm_smul, norm_inv, norm_norm]
        apply inv_mul_cancel₀
        linarith only [hx1]
      have : diskBoundaryInclusion.{u} (n + 1) ⟨‖x‖⁻¹ • x, xmem⟩ = ⟨⟨‖x‖⁻¹ • x, pf2⟩⟩ := rfl
      rw [← this]
      have := H.prop' ⟨2 - 2 * ‖x‖, pf1⟩ ⟨⟨‖x‖⁻¹ • x, xmem⟩⟩
      simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap,
        ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk] at this
      exact this
    · replace hx1 := le_of_not_ge hx1
      simp only [hx1, sup_of_le_right, div_one]
      simp only [(by norm_num : (2 : ℝ) - 1 = 1)]
      change H (1, _) ∈ A
      rw [H.apply_one]
      apply gA
      simp_all only [Set.mem_range, exists_apply_eq_apply]
  · exact Nonempty.intro <|
      { toContinuousMap := H'
        map_zero_left := fun ⟨x, hx⟩ ↦ by
          unfold H' Cyl.stretchToWall
          simp only [ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply,
            Set.Icc.coe_zero, sub_zero, ContinuousMap.Homotopy.coe_toContinuousMap,
            ContinuousMap.HomotopyWith.coe_toHomotopy]
          have : 2 * ‖x‖ ≤ 2 := by
            have := Metric.mem_closedBall.mp hx
            rw [dist_eq_norm, sub_zero] at this
            linarith only [this]
          simp only [this, sup_of_le_right, sub_self, Set.Icc.mk_zero, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, div_self, one_smul, ContinuousMap.HomotopyWith.apply_zero]
        map_one_left x := by unfold l; rfl
        prop' t x hy := by
          unfold H'
          simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply,
            ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.HomotopyWith.coe_toHomotopy,
            ContinuousMap.coe_mk]
          obtain ⟨x, hx⟩ := x
          obtain ⟨⟨y, hy⟩, hy'⟩ := Set.mem_range.mp hy
          simp only [diskBoundaryInclusion, hom_ofHom] at hy'
          replace hy' := (congr_arg (Subtype.val ∘ ULift.down) hy')
          simp only [Function.comp_apply] at hy'
          have hx1 : ‖x‖ = 1 := by
            rw [← hy']
            change ‖y‖ = 1
            convert Metric.mem_sphere.mp hy using 1
            exact Eq.symm (dist_zero_right y)
          rw [Cyl.stretchToWall_eq_zero_of_norm_eq_one hx1]
          rw [H.apply_zero] }

/-- Suppose `n ≥ 1` and the relative homotopy group `π﹍ n X A a` is zero for all `a : A`.
If `f` is a continuous map of pairs from `(∂𝔻 n, 𝔻 n)` to `(X, A)`,
then it is relative to `∂𝔻 n` homotopic to a map into `A`. -/
theorem homotopicRel_boundary_of_unique_pi
    (f : C(disk.{u} (n + 1), X)) (hf : IsMapOfPairs X A f)
    (hpi : ∀ a : A, Nonempty <| Unique <| π﹍ (n + 1) X A a) :
    ∃ l : C(disk.{u} (n + 1), X),
      Set.range l ⊆ A ∧ f.HomotopicRel l (Set.range (diskBoundaryInclusion _)) := by
  obtain ⟨a, H⟩ := homotopicWith_const_isMapOfPairs_of_unique_pi X A f hf hpi
  let g : C(disk.{u} (n + 1), X) := ContinuousMap.const (𝔻 (n + 1)) a
  have gr : Set.range g ⊆ A := by
    unfold g
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_range.mp hx
    simp only [ContinuousMap.const_apply] at hy
    subst hy
    simp_all only [ContinuousMap.coe_const, Set.mem_range, Function.const_apply, exists_const_iff, and_true,
      Subtype.coe_prop]
  apply homotopicRel_boundary_of_homotopicWith_isMapOfPairs X A
  use g

/-- For `n ≥ 1`, if the relative homotopy group `π﹍ (n + 1) X A a` is zero
(regardless of the basepoint `a`), then the inclusion map form `A` to `X` is `n`-compressible. -/
theorem isCompressible_subtype_val_of_unique_pi
    (n : ℕ) (X : Type u) [TopologicalSpace X] (A : Set X)
    (hpi : ∀ a : A, Nonempty <| Unique <| π﹍ (n + 1) X A a) :
    IsCompressible (diskBoundaryInclusion (n + 1))
      (ofHom ⟨Subtype.val, continuous_subtype_val⟩ : of A ⟶ of X) where
  sq_hasLift := fun {F f} sq ↦ by
    constructor
    have F_pair : disk.IsMapOfPairs X A F.hom := fun x ↦ by
      change (diskBoundaryInclusion (n + 1) ≫ F) x ∈ A
      rw [← sq.w]
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        Subtype.coe_prop]
    obtain ⟨l, lA, H⟩ := disk.homotopicRel_boundary_of_unique_pi X A F.hom F_pair hpi
    replace lA := Set.range_subset_iff.mp lA
    let l' :  C(disk.{u} (n + 1), A) := ⟨fun x ↦ ⟨l x, lA x⟩, by fun_prop⟩
    refine Nonempty.intro ⟨ofHom l', ?_, ?_⟩
    · ext x
      unfold l'
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      let x' := diskBoundaryInclusion (n + 1) x
      have x'r : x' ∈ Set.range (diskBoundaryInclusion (n + 1)) := Set.mem_range_self x
      have := H.some.prop' 1 x' x'r
      simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap,
        ContinuousMap.Homotopy.apply_one, ContinuousMap.coe_mk] at this
      convert this
      unfold x'
      change _ = (diskBoundaryInclusion (n + 1) ≫ F) x
      rw [← sq.w]
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    · convert H

open RelHomotopyGroup in
/-- If `iStar : π_ 0 A pt → π_ 0 X pt` is bijective (for some basepoint `pt`, which is irrelevant),
then the inclusion map from `A` to `X` is `0`-compressible. -/
theorem isCompressible_zero_subtype_val_of_bijective_iStar_zero
    (X : Type u) [TopologicalSpace X] (A : Set X) (pt : A)
    (hbi : Function.Bijective <| iStar 0 X A pt) :
    IsCompressible (diskBoundaryInclusion 0)
      (ofHom ⟨Subtype.val, continuous_subtype_val⟩ : of A ⟶ of X) := by
  constructor
  intro F f sq
  have xD0 : 0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1 := by
    simp only [Metric.mem_closedBall, dist_self, zero_le_one]
  let x : X := F.hom ⟨0, xD0⟩
  let β' : GenLoop (Fin 0) X pt :=
    ⟨ContinuousMap.const _ x, fun y hy ↦ isEmptyElim (⟨y, hy⟩ : ∂I^0)⟩
  let β : π_ 0 X pt := ⟦β'⟧
  obtain ⟨α, iα⟩ := hbi.surjective β
  let α' := α.out
  replace iα : iStar 0 X A pt ⟦α'⟧ = ⟦β'⟧ := by unfold α'; rwa [Quotient.out_eq]
  change iStar' .. = _ at iα
  have H : ContinuousMap.HomotopicRel .. := Quotient.eq.mp iα.symm
  replace H := H.some
  let a : X := H ⟨1, ![]⟩
  have aA : a ∈ A := by
    unfold a
    rw [H.apply_one ![]]
    simp_all only [ContinuousMap.coe_mk, Function.comp_apply, Subtype.coe_prop, α', β', x]
  have := H.toContinuousMap
  let l : C(disk.{u} 0, A) := ContinuousMap.const _ ⟨a, aA⟩
  constructor
  refine ⟨ofHom l, ?_, ?_⟩
  · ext x
    exact isEmptyElim x
  · exact Nonempty.intro
      { toFun := fun ⟨t, _⟩ ↦ H.toContinuousMap ⟨t, ![]⟩
        continuous_toFun := by fun_prop
        map_zero_left y := by
          unfold β'
          simp only [ContinuousMap.const_apply, ContinuousMap.Homotopy.coe_toContinuousMap,
            ContinuousMap.Homotopy.apply_zero]
          unfold x
          congr
          have u : Unique <| EuclideanSpace ℝ (Fin 0) := by infer_instance
          convert u.uniq 0
          exact u.uniq _
        map_one_left y := by
          unfold l a
          simp only [ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_one,
            ContinuousMap.coe_mk, Function.comp_apply, ContinuousMap.HomotopyWith.apply_one,
            Subtype.coe_eta, hom_comp, hom_ofHom, ContinuousMap.comp_const,
            ContinuousMap.const_apply]
        prop' t x := by
          simp only [Set.mem_range, IsEmpty.exists_iff, ContinuousMap.Homotopy.coe_toContinuousMap,
            ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk, IsEmpty.forall_iff] }

/-- If `φ` is a weak homotopy equivalence,
then the inclusion map `MapCyl.domInclFromTop φ`
from the top surface of the mapping cylinder of `φ` to the mapping cylinder of `φ`
is `n`-compressible for each natural number `n`. -/
lemma isCompressible_mapcyl_domInclFromTop_of_isWeakHomotopyEquiv
    (n : ℕ) {X Y : TopCat.{u}} (φ : X ⟶ Y) (hφ : IsWeakHomotopyEquiv φ.hom) :
    IsCompressible (diskBoundaryInclusion n) <| ofHom <| MapCyl.domInclFromTop φ := by
  induction n with
  | zero =>
      have x := hφ.left.some
      replace hφ := isIso_inducedPointedHom_of_isWeakHomotopyEquiv hφ 0
      have hbi : Function.Bijective <|
          RelHomotopyGroup.iStar 0 (MapCyl φ) (MapCyl.top φ) (MapCyl.domInclToTop φ x) :=
        RelHomotopyGroup.bijective_iStar_mapCyl_of_isIso 0 φ x (hφ x)
      exact isCompressible_zero_subtype_val_of_bijective_iStar_zero _ _ _ hbi
  | succ n =>
      have hpi a : Nonempty <| Unique <| π﹍ (n + 1) (MapCyl φ) (MapCyl.top φ) a := by
        let x := (TopCat.MapCyl.domHomeoTop φ).invFun a
        convert RelHomotopyGroup.unique_pi_mapCyl_of_isWeakHomotopyEquiv n φ x hφ
        unfold MapCyl.domInclToTop x
        simp only [Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv, ContinuousMap.coe_coe,
          Homeomorph.apply_symm_apply]
      convert isCompressible_subtype_val_of_unique_pi n (MapCyl φ) (MapCyl.top φ) hpi

/-- If `φ : X ⟶ Y` is a weak homotopy equivalence,
then the inclusion map `MapCyl.domIncl φ` from `X` to the mapping cylinder of `φ`
is `n`-compressible for each natural number `n`. -/
theorem isCompressible_mapCyl_domIncl_of_isWeakHomotopyEquiv
    (n : ℕ) {X Y : TopCat.{u}} (φ : X ⟶ Y) (hφ : IsWeakHomotopyEquiv φ.hom) :
    IsCompressible (diskBoundaryInclusion n) <| MapCyl.domIncl φ where
  sq_hasLift := fun {F f} sq ↦ by
    have com := isCompressible_mapcyl_domInclFromTop_of_isWeakHomotopyEquiv n φ hφ
    have sq' : CommSq (f ≫ (ofHom <| MapCyl.domInclToTop φ)) (diskBoundaryInclusion n)
      (ofHom <| MapCyl.domInclFromTop φ) F := ⟨sq.w⟩  -- (domIncl f).hom = (domInclFromTop f).comp (domInclToTop f)
    let l := com.sq_hasLift sq' |>.hasLift.some
    let inv : C(MapCyl.top φ, X) := toContinuousMap (MapCyl.domHomeoTop φ).symm
    use l.l ≫ ofHom inv
    · have := congrArg₂ CategoryStruct.comp l.fac_left (Eq.refl (ofHom inv))
      convert this using 1
      rw [Category.assoc]
      unfold inv MapCyl.domInclToTop
      ext x : 1
      simp only [hom_comp, hom_ofHom, Homeomorph.symm_comp_toContinuousMap, ContinuousMap.id_comp]
    · convert l.H using 2
      rw [Category.assoc]
      congr 1
      ext x
      change ((MapCyl.domIncl φ).hom ∘ inv) x = _
      rw [MapCyl.domIncl_hom_eq_domInclFromTop_comp_domInclToTop]
      unfold inv
      simp only [ContinuousMap.coe_comp, ContinuousMap.coe_coe, Function.comp_apply, hom_ofHom]
      congr 1
      unfold MapCyl.domInclToTop
      simp only [ContinuousMap.coe_coe, Homeomorph.apply_symm_apply]

end TopCat.disk
