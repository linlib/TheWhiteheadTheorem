import WhiteheadTheorem.CWComplex
import WhiteheadTheorem.Shapes.DiskHomeoCube
import WhiteheadTheorem.HEP.Cofibration

/-!
In this file we derive the homotopy extension property (HEP)
of the pair $(I^n, ∂I^n)$ from the HEP of $(D^n, ∂D^n)$.
-/

open CategoryTheory TopCat
open scoped Topology unitInterval


/--
```
  ∂𝔻 n ---φ---> ∂I^n ------h---> C(I, Y)
  |       ≃       |                |
  i               ι            pathStart
  |               |                |
  v       ≃       v                v
  𝔻 n ----Φ--> I^ (Fin n) ---f---> Y
```
-/
instance Cube.boundaryInclusion_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom (Cube.boundaryInclusion n) where
  hasCurriedHEP Y :=
    let Φ := (diskPair.homeoCubePair n).hom.right
    let Φinv := (diskPair.homeoCubePair n).inv.right
    let φ := (diskPair.homeoCubePair n).hom.left
    let φinv := (diskPair.homeoCubePair n).inv.left
    let i := diskBoundaryInclusion n
    let ι := TopCat.ofHom (Cube.boundaryInclusion n)
    ⟨{  sq_hasLift {h f} sq := by
          have hepd : HasCurriedHEP (diskBoundaryInclusion n) Y := by infer_instance
          have bigSq : CommSq (φ ≫ h) i (pathStart Y) (Φ ≫ f) := ⟨by
            simp only [Arrow.mk_left, Category.assoc, Arrow.mk_right]
            rw [sq.w, ← Category.assoc, ← Category.assoc]
            congr 1 ⟩
          have l := hepd.hasLift.sq_hasLift bigSq |>.exists_lift.some
          refine ⟨Nonempty.intro ⟨Φinv ≫ l.l, ?_, ?_⟩⟩
          · suffices φ ≫ ι ≫ Φinv ≫ l.l = φ ≫ h by
              have : (φinv ≫ φ) ≫ ι ≫ Φinv ≫ l.l = (φinv ≫ φ) ≫ h := by
                simp only [Category.assoc]; rw [this]
              rwa [Arrow.inv_hom_id_left, Category.id_comp, Category.id_comp] at this
            -- calc φ ≫ ι ≫ Φinv ≫ l.l = (φ ≫ ι) ≫ Φinv ≫ l.l := rfl
            --     _ = (i ≫ Φ) ≫ Φinv ≫ l.l := by rw [← diskPair.homeoCubePair_comm n]
            --     _ = i ≫ (Φ ≫ Φinv) ≫ l.l := rfl
            --     _ = i ≫ l.l := by rw [Arrow.hom_inv_id_right]; rfl
            --     _ = φ ≫ h := l.fac_left
            -- Note : `calc` freezes Lean, why?
            change (φ ≫ ι) ≫ Φinv ≫ l.l = _
            rw [← diskPair.homeoCubePair_comm n]
            change (i ≫ Φ) ≫ Φinv ≫ l.l = _
            rw [Category.assoc]
            change i ≫ (Φ ≫ Φinv) ≫ l.l = _
            rw [Arrow.hom_inv_id_right]
            change i ≫ l.l = _
            exact l.fac_left
          · simp only [Category.assoc]
            suffices Φ ≫ Φinv ≫ l.l ≫ Y.pathStart = Φ ≫ f by
              have : (Φinv ≫ Φ) ≫ Φinv ≫ l.l ≫ Y.pathStart = (Φinv ≫ Φ) ≫ f := by
                simp only [Category.assoc]; rw [this]
              rwa [Arrow.inv_hom_id_right, Category.id_comp, Category.id_comp] at this
            calc Φ ≫ Φinv ≫ l.l ≫ Y.pathStart = (Φ ≫ Φinv) ≫ l.l ≫ Y.pathStart := rfl
                _ = l.l ≫ Y.pathStart := by rw [Arrow.hom_inv_id_right]; rfl
                _ = Φ ≫ f := l.fac_right }⟩

instance Cube.boundaryInclusion_prod_unitInterval_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom <| (Cube.boundaryInclusion n).prodMap (ContinuousMap.id I) := by
  change IsCofibration <| TopCat.ofHom <| (TopCat.ofHom <| Cube.boundaryInclusion n).hom.prodMap _
  apply IsCofibration.prod_unitInterval

theorem Cube.boundaryInclusion_hasHEP
    (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (Cube.boundaryInclusion n) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
    (Cube.boundaryInclusion_isCofibration n) (TopCat.of Y)

theorem Cube.boundaryInclusion_prod_unitInterval_hasHEP
    (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty ((Cube.boundaryInclusion n).prodMap (ContinuousMap.id I)) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
     (Cube.boundaryInclusion_prod_unitInterval_isCofibration n) (TopCat.of Y)


/-!
The universe-polymorphic version of the above theorems
-/

namespace TopCat

universe u

instance cubeBoundaryInclusion_isCofibration (n : ℕ) :
    IsCofibration (cubeBoundaryInclusion.{u} n) where
  hasCurriedHEP Y :=
    let Φ := (diskPair.homeoCubePairULift.{u} n).hom.right
    let Φinv := (diskPair.homeoCubePairULift.{u} n).inv.right
    let φ := (diskPair.homeoCubePairULift.{u} n).hom.left
    let φinv := (diskPair.homeoCubePairULift.{u} n).inv.left
    let i := diskBoundaryInclusion.{u} n
    let ι := cubeBoundaryInclusion.{u} n
    ⟨{  sq_hasLift {h f} sq := by
          have hepd : HasCurriedHEP (diskBoundaryInclusion n) Y := by infer_instance
          have bigSq : CommSq (φ ≫ h) i (pathStart Y) (Φ ≫ f) := ⟨by
            simp only [Arrow.mk_left, Category.assoc, Arrow.mk_right]
            rw [sq.w, ← Category.assoc, ← Category.assoc]
            congr 1 ⟩
          have l := hepd.hasLift.sq_hasLift bigSq |>.exists_lift.some
          refine ⟨Nonempty.intro ⟨Φinv ≫ l.l, ?_, ?_⟩⟩
          · suffices φ ≫ ι ≫ Φinv ≫ l.l = φ ≫ h by
              have : (φinv ≫ φ) ≫ ι ≫ Φinv ≫ l.l = (φinv ≫ φ) ≫ h := by
                simp only [Category.assoc]; rw [this]
              rwa [Arrow.inv_hom_id_left, Category.id_comp, Category.id_comp] at this
            change (φ ≫ ι) ≫ Φinv ≫ l.l = _
            rw [← diskPair.homeoCubePairULift_comm n]
            change (i ≫ Φ) ≫ Φinv ≫ l.l = _
            rw [Category.assoc]
            change i ≫ (Φ ≫ Φinv) ≫ l.l = _
            rw [Arrow.hom_inv_id_right]
            change i ≫ l.l = _
            exact l.fac_left
          · simp only [Category.assoc]
            suffices Φ ≫ Φinv ≫ l.l ≫ Y.pathStart = Φ ≫ f by
              have : (Φinv ≫ Φ) ≫ Φinv ≫ l.l ≫ Y.pathStart = (Φinv ≫ Φ) ≫ f := by
                simp only [Category.assoc]; rw [this]
              rwa [Arrow.inv_hom_id_right, Category.id_comp, Category.id_comp] at this
            calc Φ ≫ Φinv ≫ l.l ≫ Y.pathStart = (Φ ≫ Φinv) ≫ l.l ≫ Y.pathStart := rfl
                _ = l.l ≫ Y.pathStart := by rw [Arrow.hom_inv_id_right]; rfl
                _ = Φ ≫ f := l.fac_right }⟩

instance cubeBoundaryInclusion_prod_unitInterval_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom <|
    (cubeBoundaryInclusion.{u} n).hom.prodMap (ContinuousMap.id I) := by
  apply IsCofibration.prod_unitInterval

theorem cubeBoundaryInclusion_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (cubeBoundaryInclusion.{u} n).hom Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
    (cubeBoundaryInclusion_isCofibration n) (TopCat.of Y)

theorem cubeBoundaryInclusion_prod_unitInterval_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty ((cubeBoundaryInclusion n).hom.prodMap (ContinuousMap.id I)) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
     (cubeBoundaryInclusion_prod_unitInterval_isCofibration n) (TopCat.of Y)

end TopCat
