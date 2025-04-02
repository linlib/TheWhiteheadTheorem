import WhiteheadTheorem.Shapes.Maps
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square


universe u

open CategoryTheory TopCat
open scoped unitInterval

noncomputable def MapCyl {X Y : TopCat.{u}} (f : X ⟶ Y) : TopCat.{u} :=
  Limits.pushout (inclZero X) f
