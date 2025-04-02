import WhiteheadTheorem.HomotopyGroup.InducedMaps


open CategoryTheory ContinuousMap

universe u

def IsWeakHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  ∀ n x, IsIso <| (HomotopyGroup.functorToType n).map <| PointedTopCat.ofHom f x
-- ∀ n x, IsIso <| (HomotopyGroup.functorToPointed n).map <| PointedTopCat.ofHom f x

def IsHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  ∃ equiv : X ≃ₕ Y, equiv.toFun = f
