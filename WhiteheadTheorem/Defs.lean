import WhiteheadTheorem.HomotopyGroup.InducedMaps


open CategoryTheory
open scoped ContinuousMap

universe u

def IsWeakHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  Nonempty X ∧
    ∀ n x, Function.Bijective (HomotopyGroup.inducedMap n x f)

-- def IsWeakHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
--     (f : C(X, Y)) : Prop :=
--   ∀ n x, IsIso (HomotopyGroup.inducedPointedHom n x f)

lemma isIso_inducedPointedHom_of_isWeakHomotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : IsWeakHomotopyEquiv f) :
    ∀ n x, IsIso (HomotopyGroup.inducedPointedHom n x f) := by
  intro n x
  apply (Pointed.isIso_iff_bijective _).mpr
  have := hf.right n x
  rwa [HomotopyGroup.inducedMap] at this

def IsHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  ∃ equiv : X ≃ₕ Y, equiv.toFun = f
