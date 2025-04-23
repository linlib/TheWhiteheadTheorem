import WhiteheadTheorem.CWComplex.Basic
import WhiteheadTheorem.Shapes.DiskHomeoCube
import WhiteheadTheorem.HEP.Cofibration

/-!
In this file, the homotopy extension property (HEP) of the pair $(I^n, ∂I^n)$
is derived from the HEP of $(D^n, ∂D^n)$.
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
  hasCurriedHEP _ :=
    ⟨HasLiftingProperty.of_arrow_iso_left (diskPair.homeoCubePair n) _⟩

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
  hasCurriedHEP _ :=
    ⟨HasLiftingProperty.of_arrow_iso_left (diskPair.homeoCubePairULift n) _⟩

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
