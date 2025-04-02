import WhiteheadTheorem.RelHomotopyGroup.Defs
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps


open CategoryTheory
open scoped Topology


variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


abbrev PointedTopCat := Under (TopCat.of PUnit)

namespace PointedTopCat

universe u

/-- Make a pointed topological space from `X` and a piont in `X`. -/
abbrev of (point : X) : PointedTopCat.{u} :=
  Under.mk <| TopCat.ofHom <| ContinuousMap.const _ point

/-- Typecheck a `ContinuousMap` as a morphism in `PointedTopCat`, by choosing a point in `X`. -/
abbrev ofHom (f : C(X, Y)) (point : X) :
    PointedTopCat.of point ⟶ PointedTopCat.of (f point) :=
  Under.homMk (TopCat.ofHom f)

-- instance : Coe PointedTopCat TopCat where
--   coe X := X.right

/-- Regard a pointed topological space as simply a topological space. -/
abbrev as (X : PointedTopCat.{u}) : TopCat.{u} := X.right

/-- The distinguished piont of a pointed topological space -/
abbrev point (X : PointedTopCat.{u}) : X.as := (TopCat.Hom.hom X.hom) PUnit.unit

/-- A morphism between pointed topological spaces maps the base point to the base point. -/
lemma w {X Y : PointedTopCat.{u}} (f : X ⟶ Y) : f.right X.point = Y.point := by
  change (TopCat.Hom.hom (X.hom ≫ f.right)) _ = _
  rw [Under.w]
  rfl

instance _root_.TopCat.isIso_of_isHomeomorph
    (f : C(X, Y)) (hf : IsHomeomorph f) : IsIso (TopCat.ofHom f) :=
  let e : TopCat.of X ≅ TopCat.of Y := TopCat.isoOfHomeo (IsHomeomorph.homeomorph f hf)
  ⟨e.inv, ⟨e.hom_inv_id, e.inv_hom_id⟩⟩

instance isIso_of_isHomeomorph
    (f : C(X, Y)) (point : X) (hf : IsHomeomorph f) : IsIso (PointedTopCat.ofHom f point) :=
  let e : TopCat.of X ≅ TopCat.of Y := TopCat.isoOfHomeo (IsHomeomorph.homeomorph f hf)
  let E : PointedTopCat.of point ≅ PointedTopCat.of (f point) := Under.isoMk e
  ⟨E.inv, ⟨E.hom_inv_id, E.inv_hom_id⟩⟩

lemma ofHom_comp (f : C(X, Y)) (g : C(Y, Z)) (point : X) :
    ofHom (g.comp f) point = (ofHom f point) ≫ (ofHom g (f point)) := by
  unfold ofHom
  simp only [ContinuousMap.comp_apply, TopCat.ofHom_comp]
  rfl

end PointedTopCat

lemma Pointed.isIso_iff_bijective {A B : Type u} {a₀ : A} {b₀ : B}
    (f : Pointed.of a₀ ⟶ Pointed.of b₀) : Function.Bijective f ↔ IsIso f := by
  constructor
  · intro bf
    constructor
    obtain ⟨g, ⟨gl, gr⟩⟩ := Function.bijective_iff_has_inverse.mp bf
    use { toFun := g,
          map_point := by
            dsimp only
            have : f a₀ = b₀ := f.map_point
            rw [← this, gl a₀] }
    constructor
    · ext a; exact gl a
    · ext b; exact gr b
  · intro isof
    apply (CategoryTheory.isIso_iff_bijective _).mp
    exact hom_isIso f


namespace HomotopyGroup

-- example (X : Under (TopCat.of PUnit)) : Discrete PUnit := X.left
-- example (X : Under (TopCat.of PUnit)) : TopCat.{u} := X.right
-- example (X : Under (TopCat.of PUnit)) : (TopCat.of PUnit) ⟶ X.right := X.hom
-- example (X : Under (TopCat.of PUnit)) : C((TopCat.of PUnit), X.right) := X.hom.hom -- TopCat.Hom.hom (CategoryTheory.Comma.hom X)
-- example (X : Under (TopCat.of PUnit)) : X.right := X.hom.hom () -- X.hom.hom PUnit.unit
-- example {n : ℕ} (hn : n > 0) : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn

def inducedMap (n : ℕ) (x : X) (f : C(X, Y)) :
    GenLoop (Fin n) X x → GenLoop (Fin n) Y (f x) :=
  fun α ↦ ⟨f.comp α.val, fun y hy ↦ by
    rw [ContinuousMap.comp_apply]
    congr 1
    exact α.property y hy ⟩

def inducedMap' (n : ℕ) {X Y : PointedTopCat} (f : X ⟶ Y) :
    GenLoop (Fin n) X.as X.point → GenLoop (Fin n) Y.as Y.point :=
  fun α ↦ ⟨f.right.hom.comp α.val, fun i hi ↦ by
    rw [ContinuousMap.comp_apply, ← PointedTopCat.w f]
    congr 1
    exact α.property i hi ⟩

/-- `π_n` is a functor sending a based topological space `(X, x₀)`
to its `n`-th homotopy group (as a type, ignoring its group structure) based at `x₀`. -/
noncomputable def functorToType (n : ℕ) : PointedTopCat.{u} ⥤ Type u where
  obj X := π_ n X.as X.point
  map {X Y} f := by
    refine Quotient.map (inducedMap' n f) fun α β hαβ ↦ ?_
    · -- f maps homotopic `GenLoop`s to homotopic `GenLoop`s
      dsimp only
      let H := hαβ.some
      have := H.toHomotopy
      exact Nonempty.intro <|
        { toHomotopy := H.hcomp (ContinuousMap.Homotopy.refl f.right.hom)
          prop' t y hy := by
            simp only [inducedMap', ContinuousMap.toFun_eq_coe,
              ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.hcomp_apply,
              ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.Homotopy.refl_apply,
              ContinuousMap.coe_mk, ContinuousMap.comp_apply]
            congr 1
            convert H.prop' t y hy }
  map_id X := by
    ext α
    simp only [inducedMap', ContinuousMap.comp_apply, ContinuousMap.toFun_eq_coe,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.hcomp_apply,
      ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.Homotopy.refl_apply,
      ContinuousMap.coe_mk, eq_mpr_eq_cast, cast_eq, id_eq, types_id_apply]
    rw [← Quotient.out_eq α, Quotient.map_mk]
    congr 1
  map_comp {X Y Z} f g := by
    ext α
    simp only [inducedMap', ContinuousMap.comp_apply, ContinuousMap.toFun_eq_coe,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.hcomp_apply,
      ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.Homotopy.refl_apply,
      ContinuousMap.coe_mk, eq_mpr_eq_cast, cast_eq, id_eq, types_comp_apply]
    rw [← Quotient.out_eq α]
    iterate 3 (rw [Quotient.map_mk])
    congr 1

/-- `π_n` is a functor sending a based topological space `(X, x₀)`
to its `n`-th homotopy group
(as a pointed type whose base point is the contant map, ignoring its group structure)
based at `x₀`. -/
noncomputable def functorToPointed (n : ℕ) : PointedTopCat.{u} ⥤ Pointed.{u} where
  obj X := Pointed.of (default : π_ n X.as X.point)
  map {X Y} f :=
    { toFun := (functorToType n).map f
      map_point := by
        change (functorToType n).map f ⟦GenLoop.const⟧ = ⟦GenLoop.const⟧
        unfold functorToType
        dsimp only [Quotient.map_mk]
        congr 1
        unfold GenLoop.const
        simp only [inducedMap',ContinuousMap.comp_const, Subtype.mk.injEq]
        ext y
        rw [ContinuousMap.const_apply]
        exact PointedTopCat.w f }
  map_id X := by
    simp only [Quotient.map_mk, id_eq, ContinuousMap.const_apply, eq_mpr_eq_cast, cast_eq,
      CategoryTheory.Functor.map_id]
    congr
  map_comp {X Y Z} f g := by
    simp only [Quotient.map_mk, id_eq, ContinuousMap.const_apply, eq_mpr_eq_cast, cast_eq,
      Functor.map_comp]
    congr

-- -- noncomputable instance piGroup {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}
-- --     [hpos : Fact (n > 0)] : Group (π_ n X x) := by
-- --   have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hpos.out
-- --   exact HomotopyGroup.group (Fin n)

/-- If `n > 0`, then `π_n` is a functor sending a based topological space `(X, x₀)`
to its `n`-th homotopy group based at `x₀`. -/
noncomputable def functorToGrp (n : ℕ) [Nonempty (Fin n)] : PointedTopCat.{u} ⥤ Grp.{u} where
  obj X := Grp.of (π_ n X.as X.point)
  map {X Y} f :=  by
    refine Grp.ofHom <| MonoidHom.mk' ((functorToType n).map f) fun α β ↦ ?_
    refine Quotient.inductionOn₂ α β fun a b ↦ ?_
    -- erw [HomotopyGroup.mul_spec] -- doesn't work. Why?
    apply Quotient.sound
    apply Quotient.eq_iff_equiv.mp
    conv_lhs =>
      rhs; rhs;
      equals GenLoop.transAt (Classical.arbitrary (Fin n)) b a =>
        simp [GenLoop.transAt, GenLoop.copy_eq]
    conv_lhs =>
      equals (functorToType n).map f ⟦(GenLoop.transAt (Classical.arbitrary (Fin n)) b a)⟧ =>
        simp only [functorToType, Quotient.map_mk]
    conv_rhs =>
      rhs;
      equals GenLoop.transAt (Classical.arbitrary (Fin n))
          (inducedMap' n f b) (inducedMap' n f a) =>
        simp [GenLoop.transAt, GenLoop.copy_eq]
    iterate 2
      (rw [@HomotopyGroup.transAt_indep _ _ _ _ _ (Classical.arbitrary (Fin n)) ⟨0, Fin.pos'⟩])
    unfold functorToType
    simp only [Quotient.map_mk, Quotient.eq]
    apply Quotient.eq_iff_equiv.mp
    congr 1
    ext y
    rw [inducedMap', GenLoop.mk_apply, ContinuousMap.comp_apply]
    rw [GenLoop.transAt]; change f.right.hom (⇑(GenLoop.copy ..) y) = _
    rw [GenLoop.coe_copy]
    rw [GenLoop.transAt, GenLoop.coe_copy]
    by_cases hy0 : y ⟨0, Fin.pos'⟩ ≤ (2⁻¹ : ℝ)
    iterate 2 (simp only [one_div, hy0, ↓reduceIte]; rfl)
  map_id X := by
    simp only [ne_eq, Homeomorph.coe_toEquiv, GenLoop.loopHomeo_apply, Homeomorph.coe_symm_toEquiv,
      GenLoop.loopHomeo_symm_apply, one_div, id_eq, Quotient.map_mk, GenLoop.mk_apply,
      ContinuousMap.comp_apply, eq_mpr_eq_cast, cast_eq, CategoryTheory.Functor.map_id]
    rfl
  map_comp {X Y Z} f g := by
    simp only [ne_eq, Homeomorph.coe_toEquiv, GenLoop.loopHomeo_apply, Homeomorph.coe_symm_toEquiv,
      GenLoop.loopHomeo_symm_apply, one_div, id_eq, Quotient.map_mk, GenLoop.mk_apply,
      ContinuousMap.comp_apply, eq_mpr_eq_cast, cast_eq, Functor.map_comp]
    rfl

-- #check FundamentalGroupoid.fundamentalGroupoidFunctor
-- #check FundamentalGroupoidFunctor.equivOfHomotopyEquiv

/-- The morphism $f_{*} : π_n(X, x₀) → π_n(Y, f(x₀))$ in the category `Pointed`,
induced by $f : X → Y$ -/
noncomputable abbrev inducedPointedHom (n : ℕ) (x₀ : X) (f : C(X, Y)) :
    Pointed.of (default : π_ n X x₀) ⟶ Pointed.of (default : π_ n Y (f x₀)) :=
  (functorToPointed n).map (PointedTopCat.ofHom f x₀)

instance isIso_inducedPointedHom_of_isHomeomorph (n : ℕ) (x₀ : X) (f : C(X, Y))
    (hf : IsHomeomorph f) : IsIso (inducedPointedHom n x₀ f) := by
  unfold inducedPointedHom
  have : IsIso (PointedTopCat.ofHom f x₀) := PointedTopCat.isIso_of_isHomeomorph f _ hf
  infer_instance

instance isIso_inducedPointedHom_id (n : ℕ) (x₀ : X) :
    IsIso (inducedPointedHom n x₀ (ContinuousMap.id X)) := by
  apply isIso_inducedPointedHom_of_isHomeomorph
  apply isHomeomorph_iff_exists_homeomorph.mpr
  use Homeomorph.refl X
  rfl

lemma inducedPointedHom_comp (x₀ : X) (f : C(X, Y)) (g : C(Y, Z)) :
    inducedPointedHom n x₀ (g.comp f) =
    inducedPointedHom n x₀ f ≫ inducedPointedHom n (f x₀) g := by
  unfold inducedPointedHom
  rw [PointedTopCat.ofHom_comp, (functorToPointed n).map_comp]

end HomotopyGroup
