import WhiteheadTheorem.HEP.Cofibration
import WhiteheadTheorem.Shapes.Cube


namespace TopCat

universe u

theorem cubeBoundaryJarInclusionToBoundary_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (cubeBoundaryJarInclusionToBoundary (n + 1)).hom Y :=
  sorry

end TopCat
