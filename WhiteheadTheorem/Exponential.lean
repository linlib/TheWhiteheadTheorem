import Mathlib.Topology.UnitInterval
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Category.TopCat.Limits.Products

open CategoryTheory
open scoped Topology

section

variable {X Y Y' Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]

def ContinuousMap.uncurry_curry [LocallyCompactSpace Y]
  (f : C(X × Y, Z)) : f = f.curry.uncurry := rfl

def ContinuousMap.curry_uncurry [LocallyCompactSpace Y]
  (f : C(X, C(Y, Z))) : f = f.uncurry.curry := rfl

/-- An auxiliary lemma only used for showing the naturality of `topBinaryProductRightAdjunctionExp` -/
lemma TopCat.exp_homEquiv_naturality_left [LocallyCompactSpace X]
    (f : C(Y', Y)) (g : C(Y, C(X, Z))) :
  (g.comp f).uncurry = g.uncurry.comp (f.prodMap (ContinuousMap.id X)) := rfl

end


namespace TopCat

/-- The functor `TopCat.of (· × X)` (taking the topological binary product, with `X` on the right)
from `TopCat` to `TopCat` -/
abbrev topBinaryProductRight (X : TopCat.{u}) : TopCat ⥤ TopCat where
  obj Y := of (Y × X)
  map {Y Z} f := ofHom (f.hom.prodMap (ContinuousMap.id X))

/-- The exponentiation functor `C(X, ·)` from `TopCat` to `TopCat` -/
abbrev exp (X : TopCat.{u}) : TopCat ⥤ TopCat where
  obj Y := of C(X, Y)
  map {Y Z} f := ofHom ⟨fun g ↦ f.hom.comp g, f.hom.continuous_postcomp⟩

noncomputable def topBinaryProductRightAdjunctionExp (X : TopCat.{u}) [LocallyCompactSpace X] :
    topBinaryProductRight X ⊣ exp X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
    { toFun f := ofHom f.hom.curry
      invFun f := ofHom f.hom.uncurry
      left_inv _ := by simp [← ContinuousMap.uncurry_curry _]
      right_inv _ := by simp [← ContinuousMap.curry_uncurry _] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by simp [exp_homEquiv_naturality_left]
    homEquiv_naturality_right {Y Z Z'} f g := by simp; rfl }

/-- Same as `topBinaryProductRight`, except that `X` is not an object in `TopCat`,
but simply a topological space -/
abbrev topBinaryProductRight' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := of (Y × X)
  map {Y Z} f := ofHom (f.hom.prodMap (ContinuousMap.id X))

/-- Same as `exp`, except that `X` is not an object in `TopCat`, but simply a topological space -/
abbrev exp' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := of C(X, Y)
  map {Y Z} f := ofHom ⟨fun g ↦ f.hom.comp g, f.hom.continuous_postcomp⟩

/-- Same as `topBinaryProductRightAdjunctionExp`,
except that `X` is not an object in `TopCat`, but simply a topological space -/
noncomputable def topBinaryProductRightAdjunctionExp'
    (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] :
    topBinaryProductRight' X ⊣ exp' X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
    { toFun f := ofHom f.hom.curry
      invFun f := ofHom f.hom.uncurry
      left_inv _ := by simp [← ContinuousMap.uncurry_curry _]
      right_inv _ := by simp [← ContinuousMap.curry_uncurry _] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by simp [exp_homEquiv_naturality_left]
    homEquiv_naturality_right {Y Z Z'} f g := by simp; rfl }

end TopCat


namespace ContinuousMap

variable {A B Y : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Y]

def argSwap : C(C(A × B, Y), C(B × A, Y)) where
  toFun f := f.comp ContinuousMap.prodSwap
  continuous_toFun := by fun_prop

def curriedArgSwap [LocallyCompactSpace A] [LocallyCompactSpace B] :
    C(C(A, C(B, Y)), C(B, C(A, Y))) where
  toFun f := ContinuousMap.curry <| argSwap <| ContinuousMap.uncurry f
  continuous_toFun := by
    refine Continuous.comp continuous_curry ?_
    exact Continuous.comp argSwap.continuous continuous_uncurry

lemma curriedArgSwap_curriedArgSwap [LocallyCompactSpace A] [LocallyCompactSpace B] :
  curriedArgSwap ∘ (curriedArgSwap (A := A) (B := B) (Y := Y)) = id := rfl

end ContinuousMap

---------------------------------------------------------------

open scoped unitInterval

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] : ContinuousEval C(X, Y) X Y := by infer_instance
example : LocallyCompactSpace I := by infer_instance
example {Y : Type*} [TopologicalSpace Y] : ContinuousEval C(I, Y) I Y := by infer_instance
example {Y : Type*} [TopologicalSpace Y] : ContinuousEval C(I, Y) _ _ := by infer_instance
