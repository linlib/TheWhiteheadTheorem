import WhiteheadTheorem.Auxiliary
import WhiteheadTheorem.Compressible.CWComplex
import WhiteheadTheorem.Compressible.Defs
import WhiteheadTheorem.Compressible.Disk
import WhiteheadTheorem.Compressible.WeakEquiv
import WhiteheadTheorem.CWComplex.Basic
import WhiteheadTheorem.CWComplex.IProd
import WhiteheadTheorem.Defs
import WhiteheadTheorem.Exponential
import WhiteheadTheorem.HEP.Cofibration
import WhiteheadTheorem.HEP.Cube
import WhiteheadTheorem.HEP.CubeJar
import WhiteheadTheorem.HEP.Retract
import WhiteheadTheorem.HomotopyGroup.ChangeBasePt
import WhiteheadTheorem.HomotopyGroup.InducedMaps
import WhiteheadTheorem.RelHomotopyGroup.Algebra
import WhiteheadTheorem.RelHomotopyGroup.Compression
import WhiteheadTheorem.RelHomotopyGroup.Defs
import WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
import WhiteheadTheorem.Shapes.Cube
import WhiteheadTheorem.Shapes.Disk
import WhiteheadTheorem.Shapes.DiskHomeoCube
import WhiteheadTheorem.Shapes.Jar
import WhiteheadTheorem.Shapes.MappingCylinder
import WhiteheadTheorem.Shapes.Maps
import WhiteheadTheorem.Shapes.Pushout


open CategoryTheory

universe u

theorem WhiteheadTheorem (X Y : CWComplex.{u}) (f : (X : TopCat.{u}) ⟶ Y) :
    IsWeakHomotopyEquiv f.hom → IsHomotopyEquiv f.hom := by
  intro hf
  obtain ⟨g, hgf⟩ := hf.CWComplex_induced_map_surjective Y (𝟙 _)
  have hfgf : (f ≫ g ≫ f).hom.Homotopic f.hom :=
    (ContinuousMap.Homotopic.refl f.hom).hcomp hgf
  use
    { toFun := f.hom
      invFun := g.hom
      left_inv := hf.CWComplex_induced_map_injective X (f ≫ g) (𝟙 _) hfgf
      right_inv := hgf }

-- #print axioms WhiteheadTheorem
