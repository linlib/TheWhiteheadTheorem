import WhiteheadTheorem.Shapes.Jar
import WhiteheadTheorem.Shapes.Maps
import WhiteheadTheorem.CWComplex.Basic
-- import WhiteheadTheorem.Auxiliary
import WhiteheadTheorem.Exponential
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.LiftingProperties.Limits

open CategoryTheory TopCat
open scoped Topology unitInterval


section HomotopyExtensionProperty

-- def HomotopyExtensionProperty' {A X : TopCat.{u}} (i : A ⟶ X) (Y : TopCat.{u}) : Prop :=
--   ∀ (f : X ⟶ Y) (h : A × I ⟶ Y), i ≫ f = (TopCat.ofHom (·, 0)) ≫ h

def HasHomotopyExtensionProperty {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ (f : C(X, Y)) (h : C(A × I, Y)), f ∘ i = h ∘ (·, 0) →
  ∃ H : C(X × I, Y), f = H ∘ (·, 0) ∧ h = H ∘ Prod.map i id

theorem TopCat.diskBoundaryInclusion_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (diskBoundaryInclusion.{u} n).hom Y :=
  fun f H hf ↦ ⟨HEP.Jar.homotopyExtension n f H hf,
    HEP.Jar.homotopyExtension_bottom_commutes n f H hf,
    HEP.Jar.homotopyExtension_wall_commutes n f H hf⟩

/--
The map `i : A ⟶ X` is said to have
the "curried HomotopyExtensionProperty" with respect to `Y`,
if the commutative square
```
  A ---h---> C(I, Y)
  |          |
  i        eval₀
  |          |
  v          v
  X ---f---> Y
```
has a lift H : X -> C(I, Y).
-/
class HasCurriedHEP {A X : TopCat.{u}} (i : A ⟶ X) (Y : TopCat.{u}) : Prop where
  hasLift : HasLiftingProperty i (PathSpace.eval₀ Y)

instance {A X : TopCat.{u}} (i : A ⟶ X) (Y : TopCat.{u}) [HasCurriedHEP i Y] :
  HasLiftingProperty i (PathSpace.eval₀ Y) := HasCurriedHEP.hasLift

instance HasCurriedHEP.of_iso {A X : TopCat.{u}} (i : A ⟶ X) [IsIso i] {Y : TopCat.{u}} :
    HasCurriedHEP i Y :=
  ⟨by infer_instance⟩ --⟨HasLiftingProperty.of_left_iso i (PathSpace.eval₀ Y)⟩

instance HasCurriedHEP.of_comp_left {A X X' : TopCat.{u}} (i : A ⟶ X) (i' : X ⟶ X')
    {Y : TopCat.{u}} [HasCurriedHEP i Y] [HasCurriedHEP i' Y] : HasCurriedHEP (i ≫ i') Y :=
  ⟨by infer_instance⟩ -- ⟨HasLiftingProperty.of_comp_left i i' (PathSpace.eval₀ p)⟩

instance HasCurriedHEP.of_sigma_map {J : Type u} {A B : J → TopCat.{u}}
    (f : (j : J) → A j ⟶ B j) {Z : TopCat.{u}}
    [∀ j, HasCurriedHEP (f j) Z] : HasCurriedHEP (Limits.Sigma.map f) Z :=
  ⟨by infer_instance⟩


section HasLiftingProperty.of_colimit_ofSequence

variable {C : Type u} [Category.{v, u} C] {A Z Y : C}
  {X : ℕ → C} (i : ∀ n, X n ⟶ X (n + 1))
  [Limits.HasColimitsOfShape ℕ C]
  -- [Limits.HasColimit (Functor.ofSequence i)]
  -- [Limits.HasColimit (Functor.ofSequence fun n ↦ i (n + 1))]
  -- [∀ m, Limits.HasColimit (Functor.ofSequence fun n ↦ i (m + n))]
  (p : Z ⟶ Y) [lp : ∀ n, HasLiftingProperty (i n) p]

namespace Limits.Cocone.ofSequence_of_hasLiftingProperty

/--
The cocone has a natural transformation from `Functor.ofSequence i`
to the constant functor at `Z`.  Here we define the first component,
`NatTrans.app`, of this natural transformation.
(The second component `NatTrans.naturality` will be obtained by `NatTrans.ofSequence`.)
```
 X n ------- app n -----> Z
  |                       |
 i n                      p
  |                       |
  v                       v
X (n+1) -----> X ---f---> Y
       ι (n+1)
```
Each `app` gives rise to the next commutative square,
and is a lift for the previous square.
-/
noncomputable def app (h : X 0 ⟶ Z) (f : Limits.colimit (Functor.ofSequence i) ⟶ Y)
    (bigSq : CommSq h (Limits.colimit.ι (Functor.ofSequence i) 0) p f) :
    ∀ n, { app : X n ⟶ Z //
      CommSq app (i n) p <| Limits.colimit.ι (Functor.ofSequence i) (n + 1) ≫ f }
  | 0 => ⟨h, ⟨by
      convert bigSq.w using 1
      rw [← Category.assoc]; congr 1
      exact Limits.colimit.w (Functor.ofSequence i) <| homOfLE <| Nat.le_succ 0 ⟩⟩
  | n + 1 =>
      let liftStruct := (lp n).sq_hasLift (app h f bigSq n).property |>.exists_lift.some
      ⟨liftStruct.l, ⟨by
        convert (liftStruct.fac_right) using 1
        rw [← Category.assoc]; congr 1
        have := Limits.colimit.w (Functor.ofSequence i) <| homOfLE <| Nat.le_succ <| n + 1
        simp at this; exact this ⟩⟩

noncomputable def _root_.Limits.Cocone.ofSequence_of_hasLiftingProperty
    (h : X 0 ⟶ Z) (f : Limits.colimit (Functor.ofSequence i) ⟶ Y)
    (bigSq : CommSq h (Limits.colimit.ι (Functor.ofSequence i) 0) p f) :
    Limits.Cocone (Functor.ofSequence i) where
  pt := Z
  ι := NatTrans.ofSequence (fun n ↦ (app i p h f bigSq n).val) fun n ↦ by
    simp [app]
    generalize_proofs _ _ liftStruct   -- reuse `⋯` (an omitted proof)
    exact liftStruct.some.fac_left

end Limits.Cocone.ofSequence_of_hasLiftingProperty

/-- Postcompose a cocone `cc` with a morphism `cc.pt ⟶ Y`,
giving a cocone whose point is `Y`. (Does mathlib have this?) -/
def CategoryTheory.Limits.Cocone.postcompose {J C : Type*} [Category J] [Category C] {F : J ⥤ C}
    (cc : Limits.Cocone F) {Y : C} (p : cc.pt ⟶ Y) : Limits.Cocone F where
  pt := Y
  ι := { app j := cc.ι.app j ≫ p }

instance HasLiftingProperty.of_colimit_ofSequence_zero :
    HasLiftingProperty (Limits.colimit.ι (Functor.ofSequence i) 0) p := ⟨fun {h f} sq ↦ by
  change X 0 ⟶ _ at h
  let ccz := Limits.Cocone.ofSequence_of_hasLiftingProperty i p h f sq -- a cocone whose point is Z
  let H := Limits.colimit.desc (Functor.ofSequence i) ccz
  exact ⟨H, by simp [H]; rfl, by
    simp [H]
    let ccy := ccz.postcompose p   -- a cocone whose point is Y
    let cc := Limits.getColimitCocone (Functor.ofSequence i)   -- the colimit cocone
    have uniq_f : f = cc.isColimit.desc ccy := by   -- f is a morphism of cocones
      apply cc.isColimit.uniq ccy; intro n
      induction n with
      | zero => convert sq.w.symm
      | succ n =>
          dsimp [ccy, Limits.Cocone.postcompose, ccz]
          dsimp [Limits.Cocone.ofSequence_of_hasLiftingProperty]
          dsimp [Limits.Cocone.ofSequence_of_hasLiftingProperty.app]
          generalize_proofs _ _ liftStruct
          exact liftStruct.some.fac_right.symm
    have uniq_desc_p : Limits.colimit.desc (Functor.ofSequence i) ccz ≫ p
        = cc.isColimit.desc ccy := by
      apply cc.isColimit.uniq ccy; intro n
      dsimp [ccy, Limits.Cocone.postcompose]
      rw [← Category.assoc]; congr 1
      exact cc.isColimit.fac ccz n
    rw [uniq_f, uniq_desc_p] ⟩ ⟩


namespace Functor.ofSequence

noncomputable abbrev coconeDropFirst
    (cc : Limits.Cocone <| Functor.ofSequence i) :
    Limits.Cocone <| Functor.ofSequence fun n ↦ i (n + 1) where
  pt := cc.pt
  ι := NatTrans.ofSequence (fun n ↦ cc.ι.app (n + 1))
        (fun n ↦ by
          simp only [Functor.ofSequence_obj, Functor.const_obj_obj, homOfLE_leOfHom,
            Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map, Category.comp_id]
          rw [← cc.w <| homOfLE <| Nat.le_succ <| n + 1]
          simp_all only [Functor.ofSequence_obj, Nat.succ_eq_add_one, Functor.const_obj_obj,
            homOfLE_leOfHom, Functor.ofSequence_map_homOfLE_succ] )

noncomputable abbrev coconeUndropFirst
    (cc' : Limits.Cocone <| Functor.ofSequence fun n ↦ i (n + 1)) :
    Limits.Cocone <| Functor.ofSequence i where
  pt := cc'.pt
  ι :=
    NatTrans.ofSequence
      (fun n ↦ match n with
        | 0 => (Functor.ofSequence i).map (homOfLE (by omega : 0 ≤ 1)) ≫ cc'.ι.app 0
        | n + 1 => cc'.ι.app n )
      (fun n ↦ match n with
        | 0 => by
            simp only [Functor.ofSequence_obj, Nat.reduceAdd, Functor.const_obj_obj,
              homOfLE_leOfHom, Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map,
              Category.comp_id]
        | n + 1 => by
            simp only [Functor.ofSequence_obj, Functor.const_obj_obj, homOfLE_leOfHom,
              Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map, Category.comp_id]
            rw [← cc'.w <| homOfLE <| Nat.le_succ n]
            congr 1
            simp_all only [Nat.succ_eq_add_one, homOfLE_leOfHom,
              Functor.ofSequence_map_homOfLE_succ] )

/-- Undrop (recover) the first morphism of
`Limits.colimit.cocone (Functor.ofSequence fun n ↦ i (n + 1))` -/
noncomputable abbrev colimitCoconeUndropFirst :
    Limits.ColimitCocone <| Functor.ofSequence i := by
  let i' := fun n ↦ i (n + 1)
  -- let Xlim := Limits.colimit (Functor.ofSequence i)
  -- let Xlim' := Limits.colimit (Functor.ofSequence i')
  -- change Xlim ≅ Xlim'
  let cc : Limits.Cocone (Functor.ofSequence i) :=
    Functor.ofSequence.coconeUndropFirst i <| Limits.colimit.cocone (Functor.ofSequence i')
  -- have : cc.pt = Xlim' := rfl
  have lcc : Limits.IsColimit cc :=
    { desc cc' :=
        Limits.colimit.desc (Functor.ofSequence i') <| Functor.ofSequence.coconeDropFirst i cc'
      fac cc' n := by
        simp only [Functor.ofSequence_obj, Functor.const_obj_obj]
        simp_all only [Limits.colimit.cocone_x, Functor.ofSequence_obj, Functor.const_obj_obj, homOfLE_leOfHom,
          Functor.ofSequence_map_homOfLE_succ, Limits.colimit.cocone_ι, NatTrans.ofSequence_app, cc, i']
        split
        next x =>
          simp_all only [Category.assoc, Limits.colimit.ι_desc, NatTrans.ofSequence_app, Nat.reduceAdd]
          rw [← cc'.w <| homOfLE <| Nat.le_succ 0]
          simp_all only [Functor.ofSequence_obj, Nat.succ_eq_add_one, Nat.reduceAdd, Functor.const_obj_obj,
            homOfLE_leOfHom, Functor.ofSequence_map_homOfLE_succ, cc, i']
        next x n => simp_all only [Nat.succ_eq_add_one, Limits.colimit.ι_desc, NatTrans.ofSequence_app]
      uniq cc' M hM := by
        apply Limits.colimit.hom_ext
        intro n
        simp only [Functor.ofSequence_obj, Limits.colimit.ι_desc, NatTrans.ofSequence_app, cc, i']
        exact hM (n + 1) }
  exact ⟨cc, lcc⟩

/-- The colimit of a sequence `i` of morphisms is isomorphic to
the colimit of the sequence with the first morphism dropped. -/
noncomputable example :
    Limits.colimit (Functor.ofSequence i) ≅
    Limits.colimit (Functor.ofSequence fun n ↦ i (n + 1)) :=
  Limits.colimit.isoColimitCocone <| Functor.ofSequence.colimitCoconeUndropFirst i

end Functor.ofSequence


instance HasLiftingProperty.of_colimit_ofSequence
    {C : Type u} [Category.{v, u} C] {Z Y : C}
    {X : ℕ → C} (i : ∀ n, X n ⟶ X (n + 1)) [Limits.HasColimitsOfShape ℕ C]
    (p : Z ⟶ Y) [lp : ∀ n, HasLiftingProperty (i n) p]
    (m : ℕ) :
    HasLiftingProperty (Limits.colimit.ι (Functor.ofSequence i) m) p :=
  match m with
  | 0 => by infer_instance  -- HasLiftingProperty.of_colimit_ofSequence_zero
  | m + 1 => by
      rw [← (Limits.colimit.isoColimitCocone_ι_inv <|
              Functor.ofSequence.colimitCoconeUndropFirst i) (m + 1) ]
      rw [(by rfl : (Functor.ofSequence.colimitCoconeUndropFirst i).cocone.ι.app (m + 1)
            = Limits.colimit.ι (Functor.ofSequence fun n ↦ i (n + 1)) m )]
      have := of_colimit_ofSequence (fun n ↦ i (n + 1)) p m  -- recursion
      infer_instance  -- composition of `Limits.colimit.ι (Functor.ofSequence …) m` with an iso

end HasLiftingProperty.of_colimit_ofSequence


instance HasCurriedHEP.of_colimit_ofSequence {X : ℕ → TopCat.{u}} (i : ∀ n, X n ⟶ X (n + 1))
    {Y : TopCat.{u}} [∀ n, HasCurriedHEP (i n) Y] (n : ℕ) :
    HasCurriedHEP (Limits.colimit.ι (Functor.ofSequence i) n) Y :=
  ⟨by infer_instance⟩


theorem HasCurriedHEP.iff_hasHomotopyExtensionProperty {A X : TopCat.{u}}
    (i : A ⟶ X) (Y : TopCat.{u}) :
    HasCurriedHEP i Y ↔ HasHomotopyExtensionProperty i.hom Y := by
  constructor
  · intro lhep f h fac
    have sq : CommSq (ofHom h.curry) i (PathSpace.eval₀ Y) (ofHom f) := ⟨by
      ext a; simp; change _ = (f ∘ i.hom) a; rw [fac]; simp ⟩
    obtain ⟨H, H1, H2⟩ := (lhep.hasLift.sq_hasLift sq).exists_lift.some
    apply_fun DFunLike.coe ∘ Hom.hom at H1 H2
    simp at H1 H2
    use H.hom.uncurry -- the key
    constructor
    · rw [← H2]; ext x; simp
    · ext ⟨a, t⟩; simp; change (h.curry a) t = _; rw [← H1]; simp
  · intro hep
    exact ⟨⟨fun {h} {f} sq ↦ by
      have fac := congr_arg (DFunLike.coe ∘ Hom.hom) sq.w.symm -- strip down sq to functions
      have : (fun f ↦ f 0) ∘ h.hom = h.hom.uncurry ∘ (·, 0) := by ext; simp
      simp [this] at fac
      obtain ⟨H, H1, H2⟩ := hep f.hom h.hom.uncurry fac
      exact ⟨Nonempty.intro {
        l := ofHom H.curry -- the key
        fac_left := by ext a t; simp; change _ = h.hom.uncurry ⟨a, t⟩; rw [H2]; simp
        fac_right := by ext x; simp; rw [H1]; simp } ⟩ ⟩ ⟩

instance TopCat.diskBoundaryInclusion_hasCurriedHEP (n : ℕ) (Y : TopCat.{u}) :
    HasCurriedHEP (diskBoundaryInclusion.{u} n) Y :=
  HasCurriedHEP.iff_hasHomotopyExtensionProperty (diskBoundaryInclusion.{u} n) Y |>.mpr <|
    TopCat.diskBoundaryInclusion_hasHEP n Y

/--
If
```
  A ---f---> B
  |          |
  i          j
  |    p.o.  |
  v          v
  X ---F---> Y
```
is a pushout square and the left side `i` has the homotopy extension property,
then the right side `j` has the homotopy extension property.
-/
lemma CategoryTheory.IsPushout.hasCurriedHEP {A B X Y Z : TopCat.{u}}
    {f : A ⟶ B} {i : A ⟶ X} {j : B ⟶ Y} {F : X ⟶ Y}
    (po : IsPushout f i j F) [lhep : HasCurriedHEP i Z] :
    HasCurriedHEP j Z where
  hasLift := by apply po.hasLiftingProperty -- uses `hep.haslift` by typeclass resolution

end HomotopyExtensionProperty


section Cofibration

class IsCofibration {A X : TopCat.{u}} (i : A ⟶ X) : Prop where
  hasCurriedHEP : ∀ (Y : TopCat.{u}), HasCurriedHEP i Y

theorem IsCofibration.iff_hasHomotopyExtensionProperty
    {A X : TopCat.{u}} (i : A ⟶ X) :
    IsCofibration i ↔ ∀ (Y : TopCat.{u}), HasHomotopyExtensionProperty i.hom Y :=
  ⟨fun h Y ↦ HasCurriedHEP.iff_hasHomotopyExtensionProperty i Y |>.mp (h.hasCurriedHEP Y),
    fun h ↦ ⟨fun Y ↦ HasCurriedHEP.iff_hasHomotopyExtensionProperty i Y |>.mpr (h Y)⟩ ⟩

instance {A X : TopCat.{u}} (i : A ⟶ X) [IsCofibration i] (Y : TopCat.{u}) :
  HasCurriedHEP i Y := IsCofibration.hasCurriedHEP Y

instance IsCofibration.of_iso {A X : TopCat.{u}} (i : A ⟶ X) [IsIso i] : IsCofibration i :=
  ⟨by infer_instance⟩ -- ⟨fun _ ↦ HasCurriedHEP.of_iso i⟩

instance IsCofibration.of_comp_left {A X X' : TopCat.{u}} (i : A ⟶ X) (i' : X ⟶ X')
    [IsCofibration i] [IsCofibration i'] : IsCofibration (i ≫ i') :=
  ⟨by infer_instance⟩ -- ⟨fun _ ↦ HasCurriedHEP.of_comp_left i i'⟩

instance IsCofibration.of_sigma_map {J : Type u} {A B : J → TopCat.{u}} (f : (j : J) → A j ⟶ B j)
    [∀ j, IsCofibration (f j)] : IsCofibration (Limits.Sigma.map f) :=
  ⟨by infer_instance⟩

instance IsCofibration.of_colimit_ofSequence
    {X : ℕ → TopCat.{u}} (i : ∀ n, X n ⟶ X (n + 1)) [∀ n, IsCofibration (i n)]
    (n : ℕ) : IsCofibration (Limits.colimit.ι (Functor.ofSequence i) n) :=
  ⟨by infer_instance⟩

instance TopCat.diskBoundaryInclusion_isCofibration (n : ℕ) :
    IsCofibration (diskBoundaryInclusion.{u} n) where
  hasCurriedHEP := by apply diskBoundaryInclusion_hasCurriedHEP

lemma CategoryTheory.IsPushout.isCofibration {A B X Y : TopCat.{u}}
    {f : A ⟶ B} {i : A ⟶ X} {j : B ⟶ Y} {F : X ⟶ Y}
    (po : IsPushout f i j F) (cof : IsCofibration i) : IsCofibration j :=
  ⟨fun _ ↦ po.hasCurriedHEP⟩


/--
```
                  curriedArgSwap
C(I, C(I, Y)) --------------------> C(I, C(I, Y))
     |                  ≃                |
     |                                   |
(exp' I).map (PathSpace.eval₀ Y)    PathSpace.eval₀ (TopCat.of C(I, Y))
     |                                   |
     v                                   v
  C(I, Y)  =========================  C(I, Y)
```
-/
lemma exp_PathSpace.eval₀_eq_curriedArgSwap_PathSpace.eval₀ {Y : TopCat.{u}} :
    (exp' I).map (PathSpace.eval₀ Y) =
    TopCat.ofHom ContinuousMap.curriedArgSwap ≫ PathSpace.eval₀ (TopCat.of C(I, Y)) :=
  rfl

/-- If `A ⟶ X` is a cofibration, then `TopCat.of (A × I) ⟶ TopCat.of (X × I)` is a cofibration.
```
A × I --------> C(I, Y)
  |               |
i × id       (PathSpace.eval₀ Y)
  |               |
  v               v
X × I ----------> Y
```
```
A  ---f----> C(I, C(I, Y)) ----curriedArgSwap---> C(I, C(I, Y))
|               |                                     |
i       (exp' I).map (PathSpace.eval₀ Y)      PathSpace.eval₀ (TopCat.of C(I, Y))
|               |                                     |
v               v                                     v
X ----g----> C(I, Y)  ===========================  C(I, Y)
```
related: https://math.stackexchange.com/questions/381527/the-product-of-a-cofibration-with-an-identity-map-is-a-cofibration
-/
instance IsCofibration.prod_unitInterval {A X : TopCat.{u}}
    (i : A ⟶ X) [cof : IsCofibration i] :
    IsCofibration <| TopCat.ofHom <| i.hom.prodMap (ContinuousMap.id I) := by
  change IsCofibration (topBinaryProductRight' I |>.map i)
  constructor -- IsCofibration.hasCurriedHEP
  intro Y
  constructor -- HasCurriedHEP.hasLift
  apply (Adjunction.hasLiftingProperty_iff (topBinaryProductRightAdjunctionExp' I) i _).mpr
  constructor -- HasLiftingProperty.sq_hasLift
  intro f g sq
  have bigSq : CommSq (f ≫ TopCat.ofHom ContinuousMap.curriedArgSwap)
      i (PathSpace.eval₀ <| TopCat.of C(I, Y)) g :=
    ⟨by rw [Category.assoc, ← exp_PathSpace.eval₀_eq_curriedArgSwap_PathSpace.eval₀, sq.w]⟩
  let lift := cof.hasCurriedHEP (TopCat.of C(I, Y)) |>.hasLift |>.sq_hasLift bigSq
    |>.exists_lift |>.some
  refine ⟨Nonempty.intro ⟨lift.l ≫ TopCat.ofHom ContinuousMap.curriedArgSwap, ?_, ?_⟩⟩
  · rw [← Category.assoc, lift.fac_left, Category.assoc]
    rfl
  · nth_rw 2 [← lift.fac_right]
    rw [Category.assoc, exp_PathSpace.eval₀_eq_curriedArgSwap_PathSpace.eval₀]
    rfl

end Cofibration


namespace RelCWComplex

lemma HasLiftingProperty.of_comp_iso {C : Type*} [Category C] {A B B' X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) (iso : B ≅ B')
    (h : HasLiftingProperty i p) : HasLiftingProperty (i ≫ iso.hom) p :=
  HasLiftingProperty.of_comp_left i iso.hom p

instance skInclusionToNextSk_isCofibration (X : RelCWComplex.{u}) (n : ℕ) :
    IsCofibration (X.skInclusionToNextSk n) := by
  refine @IsCofibration.of_comp_left _ _ _ _ _ ?_ (by infer_instance) -- iso is cofibration
  apply (X.attachCells n).pushout_isPushout.isCofibration
  infer_instance -- sigma map is cofibration

theorem skInclusion_isCofibration
    (X : RelCWComplex.{u}) (n : ℕ) : IsCofibration (X.skInclusion n) := by
  unfold skInclusion
  infer_instance -- inclusion into a sequential colimit is cofibration
                 -- (by `IsCofibration.of_colimit_ofSequence`)

end RelCWComplex
