import WhiteheadTheorem.Auxiliary
import WhiteheadTheorem.Compressible.Defs
import WhiteheadTheorem.Compressible.Disk
import WhiteheadTheorem.CWComplex
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


open CategoryTheory TopCat
open scoped Topology  -- notation π﹍

universe u

theorem WhiteheadTheorem (X Y : CWComplex.{u}) (f : (X : TopCat.{u}) ⟶ Y) :
    IsWeakHomotopyEquiv f.hom → IsHomotopyEquiv f.hom := by
  intro hf
  replace hf : ∀ n x, Nonempty <| Unique <|
      π﹍ (n + 1) (MapCyl f) (MapCyl.top f) (MapCyl.domInclToTop f x) :=
    fun n x ↦ RelHomotopyGroup.unique_pi_mapCyl_of_isWeakHomotopyEquiv n f x hf
  sorry

-- #print axioms RelCWComplex.skInclusion_isCofibration
-- #print axioms RelHomotopyGroup.ker_jStar_supset_im_iStar
-- #print axioms RelHomotopyGroup.ker_jStar_subset_im_iStar
-- #print axioms RelHomotopyGroup.ker_bd_supset_im_jStar
-- #print axioms RelHomotopyGroup.ker_bd_subset_im_jStar
-- #print axioms RelHomotopyGroup.ker_iStar_supset_im_bd
-- #print axioms RelHomotopyGroup.ker_iStar_subset_im_bd
-- #print axioms WhiteheadTheorem
