-- reference:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/quasicategories

import Mathlib.CategoryTheory.Category.Basic

import Mathlib.AlgebraicTopology.SimplicialSet

namespace InfCategory
  open CategoryTheory
  open Simplicial -- notations such as `Λ[n, i]` and `Δ[n]` become available

  section
    variable (X Y : SSet)
    #check X ⟶ Y
    #check NatTrans X Y

    def NatGtZero := {X : Nat // X > 0}
    example : NatGtZero := ⟨1, by decide⟩
    section
      variable (n : NatGtZero)
      #check n.val
      #check n.property
      #check n.1
      #check n.2
    end

    instance : ToString NatGtZero where
      toString p := toString p.1

    #check (inferInstance : ToString Nat)
    #check (inferInstance : ToString NatGtZero)

    def Vec (n : Nat) (a : Type) := { ls : List a // ls.length = n }
    example : Vec 3 Nat := ⟨[1, 2, 3], rfl⟩
  end

  def horn_filling_condition (X : SSet) (n i : Nat): Prop :=
    ∀ f : Λ[n, i] ⟶ X, ∃ g : Δ[n] ⟶ X,
    f = SSet.hornInclusion n i ≫ g

  -- def inner_horn_filling_condition (X : SSet) : Prop :=
  --   ∀ (n i : Nat), n ≥ 2 ∧ 0 < i ∧ i < n →
  --   ∀ f : Λ[n, i] ⟶ X, ∃ g : Δ[n] ⟶ X,
  --   f = SSet.hornInclusion n i ≫ g

  /-- A simplicial set is called an ∞-category if it has the extension property
  for all inner horn inclusions `Λ[n, i] ⟶ Δ[n]`, n ≥ 2, 0 < i < n. -/
  def InfCategory := {X : SSet //
    ∀ (n i : Nat), n ≥ 2 ∧ 0 < i ∧ i < n → horn_filling_condition X n i}

  #check (inferInstance : Category SSet)
  #check (inferInstance : Category InfCategory)
  instance : Category InfCategory := inferInstance -- ?

end InfCategory