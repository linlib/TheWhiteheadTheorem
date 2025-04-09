import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.CategoryTheory.LiftingProperties.Limits


open CategoryTheory

namespace TopCat

variable {A' A X' X : TopCat.{u}}
variable {f : A' ⟶ A} {ι : A' ⟶ X'} {i : A ⟶ X} {F : X' ⟶ X}

/-- A commutative square
```
A' -----f----→ A
|              |
ι              i
|              |
↓              ↓
X' -----F----→ X
```
in `TopCat` is said to have a lift, up to relative homotopy, if
there exists a map ` l : X' ⟶ A ` and a homotopy ` H : I × X' ⟶ X ` from `F` to `l ≫ i`,
such that `ι ≫ l = f` and `∀ t, ι ≫ H(t, ·) = f ≫ i`.
(Note: If `i` is injective, then `ι ≫ l = f` is implied by `ι ≫ H(1, ·) = f ≫ i`,
since `H(1, ·) = l ≫ i`.)
 -/
structure LiftStructUpToRelHomotopy (sq : CommSq f ι i F) where
  /-- The lift -/
  l : X' ⟶ A
  /-- The upper left triangle commutes. -/
  fac_left : ι ≫ l = f
  /-- The lower right triangle commutes up to relative homotopy. -/
  H : ContinuousMap.HomotopicRel F.hom (l ≫ i).hom (Set.range ι)
  -- H : ContinuousMap.HomotopicWith F.hom (l ≫ i).hom fun h ↦ h ∘ ⇑ι = ⇑(f ≫ i)

structure HasLiftUpToRelHomotopy (sq : CommSq f ι i F) : Prop where
  hasLift : Nonempty <| LiftStructUpToRelHomotopy sq

/-- A map `i : A ⟶ X` is called compressible with respect to ` ι : A' ⟶ X' `
if every commutative square
```
A' -----f----→ A
|              |
ι              i
|              |
↓              ↓
X' -----F----→ X
```
has a lift, up to relative homotopy.
 -/
structure IsCompressible (ι : A' ⟶ X') (i : A ⟶ X) : Prop where
  sq_hasLift : ∀ {F : X' ⟶ X} {f : A' ⟶ A} (sq : CommSq f ι i F), HasLiftUpToRelHomotopy sq

-- #check CommSq
-- #check CommSq.HasLift
-- #check CommSq.LiftStruct
-- #check HasLiftingProperty
-- #check cubeBoundaryInclusion

end TopCat
