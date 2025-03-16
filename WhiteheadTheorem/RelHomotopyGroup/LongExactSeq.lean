import WhiteheadTheorem.RelHomotopyGroup.Compression

open scoped unitInterval Topology Topology.Homotopy
open ContinuousMap


namespace RelHomotopyGroup

variable (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A)

/-- `Ker j* ⊇ Im i*` (for `n ≥ 1`) in
`⋯ πₙ(A, a) ---i*ₙ---> πₙ(X, a) ---j*ₙ---> πₙ(X, A, a) ⋯`

The long exact sequences ends with
`π₁(X, A, a) ---∂--> π₀(A, a) ---i*--> π₀(X, a)`.
It is possible to extend the sequence to `⋯ π₀(X, a) ---j*--> π₀(X, A, a) -----> 0`
by re-defining `π₀(X, A, a)` as the quotient of `π₀(X, a)` by the set `i*(π₀(X, a))`,
i.e., `π₀(X, A, a)` would be in bijection with the quotient of the path components of `X`
by those path components that intersect with `A`.

But this extension is not implemented in this Whitehead theorem project.

reference:
https://math.stackexchange.com/questions/1302389/meaning-of-n-connected-pairs
-/
theorem ker_jStar_supset_im_iStar (f : π_ (n + 1) X a) :
    (∃ g, iStar (n + 1) X A a g = f) → jStar (n + 1) X A a f = default := fun ⟨g, hgf⟩ ↦ by
  change _ = ⟦RelGenLoop.const⟧
  let f' := Quotient.out f   -- pick a representative of the homotopy class `f`
  let g' := Quotient.out g
  have : iStar (n + 1) X A a ⟦g'⟧ = ⟦f'⟧ := by simp only [Quotient.out_eq, hgf, g', f']
  replace : iStar' (n + 1) X A a g' = ⟦f'⟧ := this
  have H : ContinuousMap.HomotopicRel _ f'.val (∂I^(n+1)) := Quotient.eq.mp this
  have : jStar (n + 1) X A a ⟦f'⟧ = ⟦RelGenLoop.const⟧ :=
    compression_criterion_1_subtype n X A a _ g'.val H.some.symm
  rw [← this]; simp only [f', Quotient.out_eq]

/-- `Ker j* ⊆ Im i*` in
`⋯ πₙ(A, a) ---i*ₙ---> πₙ(X, a) ---j*ₙ---> πₙ(X, A, a) ⋯` -/
theorem ker_jStar_subset_im_iStar (f : π_ n X a) :
    jStar n X A a f = default → ∃ g, iStar n X A a g = f := fun hf0 ↦ by
  change _ = ⟦RelGenLoop.const⟧ at hf0
  let f' := Quotient.out f
  replace hf0 : jStar n X A a ⟦f'⟧ = ⟦RelGenLoop.const⟧ := by rw [← hf0, Quotient.out_eq f]
  replace hf0 : jStar' n X A a f' = ⟦RelGenLoop.const⟧ := hf0
  have ⟨g', H⟩ := compression_criterion_2_subtype n X A a _ hf0
  -- `f'` is homotopic rel `∂I^n` to a map `g'`.
  -- Since `f'` maps `∂I^n` to `a`, so does `g'`.
  have g'_prop : ∀ y ∈ ∂I^n, g' y = a := fun y hy ↦ by
    have := H.some.prop' 1 y hy
    simp only [toFun_eq_coe, Homotopy.coe_toContinuousMap, Homotopy.apply_one, coe_mk,
      Function.comp_apply] at this
    exact SetCoe.ext <| this.trans <| f'.property y hy
  use ⟦⟨g', g'_prop⟩⟧
  suffices iStar n X A a _ = ⟦f'⟧ by rw [this, Quotient.out_eq f]
  change iStar' n X A a _ = ⟦f'⟧
  exact Quotient.eq.mpr <| Nonempty.intro H.some.symm

/-- `Ker ∂ ⊇ Im j*` in
`⋯ πₙ₊₁(X, a) ---j*ₙ---> πₙ₊₁(X, A, a) ---∂ₙ---> πₙ(A, a) ⋯` -/
theorem bd_comp_jStar_eq_zero (f : π﹍ (n+1) X A a) :
    (∃ g, jStar (n+1) X A a g = f) → bd n X A a f = default := fun ⟨g, hgf⟩ ↦ by
  change _ = ⟦GenLoop.const⟧
  let g' := Quotient.out g
  rw [(by simp only [g', Quotient.out_eq] : g = ⟦g'⟧)] at hgf
  -- change jStar' .. = f at hgf
  rw [← hgf]
  change bd' .. = _
  exact Quotient.eq.mpr <| Nonempty.intro <|  -- just use the const homotopy of the const map
    { toFun := ContinuousMap.Homotopy.refl (@GenLoop.const _ A _ a).val
      continuous_toFun := ContinuousMap.continuous_toFun _
      map_zero_left y := by
        simp only [toFun_eq_coe, Homotopy.coe_toContinuousMap, Homotopy.apply_zero,
          Function.comp_apply, coe_mk]
        dsimp [GenLoop.const]
        apply Subtype.eq_iff.mpr; dsimp
        rw [g'.property _ (Cube.inclToTopFace.mem_boundary y)]
      map_one_left y := by
        simp only [toFun_eq_coe, Homotopy.coe_toContinuousMap, Homotopy.apply_one, g']
      prop' t y hy := by
        simp only [toFun_eq_coe, Homotopy.coe_toContinuousMap, Homotopy.refl_apply, coe_mk,
          Function.comp_apply]
        dsimp [GenLoop.const]
        apply Subtype.eq_iff.mpr; dsimp
        rw [g'.property _ (Cube.inclToTopFace.mem_boundary y)] }

/-- g'' (yₙ, (y₀, y₁, …, yₙ₋₁)) = if yₙ ≤ 1/2
      then f' (y₀, y₁, …, yₙ₋₁, 2 * yₙ)
      else H (2 * yₙ - 1, (y₀, y₁, …, yₙ₋₁)) -/
noncomputable def ker_bd_subset_im_jStar.g''
    (f' : RelGenLoop (n + 1) X A a) (hf0 : bd' n X A a f' = ⟦GenLoop.const⟧) :
    C(I × (I^ Fin n), X) :=
  let H : HomotopyRel .. := Quotient.eq.mp hf0 |>.some
  { toFun := fun ⟨yn, y⟩ ↦ if hyn : yn ≤ ((1/2) : ℝ)
      then f'.val <| Cube.splitAtLastFin.symm ⟨Set.projIcc 0 1 (by norm_num) (2 * yn), y⟩
      else Subtype.val <| H ⟨Set.projIcc 0 1 (by norm_num) (2 * yn - 1), y⟩
    -- toFun := fun ⟨yn, y⟩ ↦ if hyn : yn ≤ ((1/2) : ℝ)
    --     then by
    --       refine f'.val <| Cube.splitAtLastFin.symm <| ⟨⟨2 * yn, ?_⟩, y⟩
    --       constructor; linarith only [yn.property.1]; linarith only [hyn]
    --     else by
    --       refine Subtype.val <| H ⟨⟨2 * yn - 1, ?_⟩, y⟩
    --       constructor; linarith only [hyn]; linarith only [yn.property.2]
    -- This definition is dependent on `hyn` and leads to the following error
    -- when trying to prove its continuity:
    --   apply Continuous.if
    --   -- failed to unify `Continuous fun a ↦ if ?p a then ?f a else ?g a` with ⋯
    continuous_toFun:= by
      simp only [one_div, Function.comp_apply, coe_mk, dite_eq_ite]
      apply Continuous.if_le
      · refine f'.val.continuous.comp <| Cube.splitAtLastFin.symm.continuous.comp ?_
        refine Continuous.prod_mk (Continuous.comp continuous_projIcc ?_) continuous_snd
        exact Continuous.mul continuous_const <| Continuous.subtype_val continuous_fst
      · refine Continuous.subtype_val <| H.continuous.comp ?_
        refine Continuous.prod_mk (Continuous.comp continuous_projIcc ?_) continuous_snd
        refine Continuous.sub ?_ continuous_const
        exact Continuous.mul continuous_const <| Continuous.subtype_val continuous_fst
      · exact Continuous.subtype_val continuous_fst
      · exact continuous_const
      · intro ⟨yn, y⟩ hyn
        dsimp only at hyn ⊢; rw [hyn]
        simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.mul_inv_cancel, Set.projIcc_right, Set.Icc.mk_one, sub_self, Set.projIcc_left,
          Set.Icc.mk_zero, HomotopyWith.apply_zero, Function.comp_apply, coe_mk]
        congr 1 }

/-- `g''` is an element of `Ω^ (Fin (n+1)) X a`, i.e., it sends the boundary to `a`. -/
noncomputable def ker_bd_subset_im_jStar.g'
    (f' : RelGenLoop (n + 1) X A a) (hf0 : bd' n X A a f' = ⟦GenLoop.const⟧) :
    Ω^ (Fin (n+1)) X a :=
  let g'' := ker_bd_subset_im_jStar.g'' _ _ _ _ f' hf0
  let H : HomotopyRel .. := Quotient.eq.mp hf0 |>.some
  ⟨g''.comp (toContinuousMap Cube.splitAtLastFin),
  fun y ⟨i, hi⟩ ↦ by
    by_cases hin : i = Fin.last n  -- y n = 0 ∨ y n = 1
    · rw [hin] at hi
      obtain hin0 | hin1 := hi
      · -- `f'` maps the bottom face to `a`
        simp [g'', ker_bd_subset_im_jStar.g'', Cube.splitAtLastFin_fst_eq, hin0]
        apply f'.property.right
        constructor
        · use Fin.last n; left; simp [Cube.splitAtLastFin]
        · intro hfalse; simp [Cube.splitAtLastFin] at hfalse
      · -- `H` maps the top face to `a`
        simp [g'', ker_bd_subset_im_jStar.g'', Cube.splitAtLastFin_fst_eq, hin1]
        simp [(by norm_num : ¬((1 : ℝ) ≤ (2⁻¹ : ℝ))),
          (by norm_num : (2 : ℝ) - (1 : ℝ) = 1), GenLoop.const]
    · by_cases hyn : y (Fin.last n) ≤ (2⁻¹ : ℝ)
      · -- `f'` maps the sides to `a`
        simp [g'', ker_bd_subset_im_jStar.g'', Cube.splitAtLastFin_fst_eq, hyn]
        apply f'.property.right
        apply Cube.mem_boundaryJar_of_lt_last
        use i, Fin.lt_last_iff_ne_last.mpr hin
        cases hi
        · left; simpa [Cube.splitAtLastFin, hin]
        · right; simpa [Cube.splitAtLastFin, hin]
      · -- `H` maps the sides to `a`
        simp [g'', ker_bd_subset_im_jStar.g'', Cube.splitAtLastFin_fst_eq, hyn]
        have y_mem_bd : (Cube.splitAtLastFin y).2 ∈ ∂I^n := by
          use ⟨i, Fin.lt_last_iff_ne_last.mpr hin⟩
          obtain hi | hi := hi
          · left; rw [Cube.splitAtLastFin_snd_apply_eq]; simp only [Fin.castSucc_mk, Fin.eta, hi]
          · right; rw [Cube.splitAtLastFin_snd_apply_eq]; simp only [Fin.castSucc_mk, Fin.eta, hi]
        have := H.prop' (Set.projIcc 0 1 (by norm_num) (2 * (y (Fin.last n)) - 1))
          (Cube.splitAtLastFin y).2 y_mem_bd
        simp only [Function.comp_apply, coe_mk, toFun_eq_coe, Homotopy.coe_toContinuousMap,
          HomotopyWith.coe_toHomotopy, g''] at this
        rw [this]
        apply f'.property.right
        exact Cube.inclToTopFace.mem_boundaryJar_of y_mem_bd ⟩

/-- G'' (t, (yₙ, (y₀, y₁, …, yₙ₋₁))) = if yₙ ≤ (1 + t) / 2
      then f' (y₀, y₁, …, yₙ₋₁, (2 / (1 + t)) * yₙ)
      else H (2 * yₙ - (1 + t), (y₀, y₁, …, yₙ₋₁)) -/
noncomputable def ker_bd_subset_im_jStar.G''
    (f' : RelGenLoop (n + 1) X A a) (hf0 : bd' n X A a f' = ⟦GenLoop.const⟧) :
    C(I × (I × (I^ Fin n)), X) :=
  let H : HomotopyRel .. := Quotient.eq.mp hf0 |>.some
  { toFun := fun ⟨t, ⟨yn, y⟩⟩ ↦ if hyn : yn.val ≤ (1 + t) / 2
      then f'.val <| Cube.splitAtLastFin.symm
        ⟨Set.projIcc 0 1 (by norm_num) <| (2 / (1 + t)) * yn, y⟩
      else Subtype.val <| H ⟨Set.projIcc 0 1 (by norm_num) <| 2 * yn - (1 + t), y⟩
    continuous_toFun := by
      simp only [Function.comp_apply, coe_mk, dite_eq_ite]
      apply Continuous.if_le
      · refine f'.val.continuous.comp <| Cube.splitAtLastFin.symm.continuous.comp ?_
        refine Continuous.prod_mk (Continuous.comp continuous_projIcc ?_)
          (Continuous.snd continuous_snd)
        refine Continuous.mul ?_ (Continuous.subtype_val <| Continuous.fst continuous_snd)
        refine Continuous.div continuous_const (by fun_prop) fun x ↦ ?_
        linarith only [x.1.property.1]
      · refine Continuous.subtype_val <| H.continuous.comp ?_
        refine Continuous.prod_mk (Continuous.comp continuous_projIcc ?_)
          (Continuous.snd continuous_snd)
        fun_prop
      · exact Continuous.subtype_val <| Continuous.fst continuous_snd
      · fun_prop
      · intro ⟨t, ⟨yn, y⟩⟩ hyn
        dsimp only at hyn ⊢; rw [hyn]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_div_cancel₀']
        rw [div_self (by linarith only [t.property.1])]
        rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), sub_self]
        rw [Set.projIcc_left, Set.projIcc_right, Set.Icc.mk_zero, Set.Icc.mk_one]
        simp only [HomotopyWith.apply_zero, Function.comp_apply, coe_mk]
        congr 1 }

/-- `Ker ∂ ⊆ Im j*` in
`⋯ πₙ₊₁(X, a) ---j*ₙ---> πₙ₊₁(X, A, a) ---∂ₙ---> πₙ(A, a) ⋯` -/
theorem ker_bd_subset_im_jStar (f : π﹍ (n+1) X A a) :
    bd n X A a f = default → ∃ g, jStar (n+1) X A a g = f := fun hf0 ↦ by
  change _ = ⟦GenLoop.const⟧ at hf0
  let f' := Quotient.out f
  rw [(by simp only [f', Quotient.out_eq] : f = ⟦f'⟧)] at hf0 ⊢
  change bd' .. = _ at hf0
  let H : HomotopyRel .. := Quotient.eq.mp hf0 |>.some
  let g' : Ω^ (Fin (n+1)) X a := ker_bd_subset_im_jStar.g' _ _ _ _ f' hf0
  use ⟦g'⟧
  change jStar' .. = _
  exact Quotient.eq.mpr <| Nonempty.intro <|
    { toFun := ContinuousMap.comp (ker_bd_subset_im_jStar.G'' _ _ _ _ f' hf0) <|
        ContinuousMap.prodMap (ContinuousMap.id _) (toContinuousMap Cube.splitAtLastFin)
      continuous_toFun := ContinuousMap.continuous _
      map_zero_left y := by  -- G₀ = g'
        simp only [comp_apply, prodMap_apply, coe_id, ContinuousMap.coe_coe, Prod.map_apply, id_eq,
          ker_bd_subset_im_jStar.G'', g', ker_bd_subset_im_jStar.g', ker_bd_subset_im_jStar.g'']
        by_cases hyn : (Cube.splitAtLastFin y).fst.val ≤ 1 / 2
        repeat {simp only [Function.comp_apply, coe_mk, dite_eq_ite, Set.Icc.coe_zero, add_zero, one_div,
          div_one, g', f']}
      map_one_left y := by  -- G₁ = f'
        simp only [comp_apply, prodMap_apply, coe_id, ContinuousMap.coe_coe, Prod.map_apply, id_eq,
          g', ker_bd_subset_im_jStar.G'']
        have hyn : (Cube.splitAtLastFin y).fst.val ≤ 1 := (Cube.splitAtLastFin y).fst.property.2
        simp only [Function.comp_apply, coe_mk, dite_eq_ite, Set.Icc.coe_one, add_self_div_two,
          hyn, ↓reduceIte]
        have : (2 : ℝ) / (1 + 1) = 1 := by norm_num
        simp only [this, one_mul, Set.projIcc_val, Prod.mk.eta, Homeomorph.symm_apply_apply, g']
      prop' t := by
        apply RelGenLoop.mem_of_boundaryLid_and_boundaryJar
        simp only [comp_apply, prodMap_apply, coe_id, ContinuousMap.coe_coe, Prod.map_apply, id_eq,
          coe_mk, g']
        . intro y hy  -- `y` is in the top face
          simp only [Cube.boundaryLid, Set.mem_setOf_eq] at hy
          by_cases hyn : (Cube.splitAtLastFin y).fst.val ≤ (1 + t) / 2
          · -- `f'` maps the top face into `A`
            simp [ker_bd_subset_im_jStar.G'', hyn]
            rw [Cube.splitAtLastFin_fst_eq, hy] at hyn
            have t1 : t.val = 1 := by
              apply eq_of_le_of_le t.property.2
              replace hyn := (mul_le_mul_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hyn
              rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Set.Icc.coe_one, one_mul] at hyn
              linarith only [hyn]
            rw [t1, (by norm_num : (2 : ℝ) / (1 + 1) = 1), one_mul]
            simp only [Set.projIcc_val, Prod.mk.eta, Homeomorph.symm_apply_apply, g']
            apply f'.property.left
            use (Fin.last _); right; exact hy
          · -- `H` maps the top face into `A`
            simp only [ker_bd_subset_im_jStar.G'', Function.comp_apply, coe_mk, dite_eq_ite, hyn,
              ↓reduceIte, Subtype.coe_prop, g']
        · intro y hy -- `y` is in the `boundaryJar`
          simp only [ker_bd_subset_im_jStar.G'', Function.comp_apply, coe_mk, dite_eq_ite,
            comp_apply, prodMap_apply, coe_id, ContinuousMap.coe_coe, Prod.map_apply, id_eq, g']
          by_cases hbot : y (Fin.last _) = 0
          · -- `f'` maps the bottom face to `a`
            rw [Cube.splitAtLastFin_fst_eq, hbot]
            have : 0 ≤ (1 + t.val) / 2 := by linarith only [t.property.1]
            simp only [Set.Icc.coe_zero, this, ↓reduceIte, mul_zero, Set.projIcc_left,
              Set.Icc.mk_zero]
            apply f'.property.right
            apply Cube.mem_boundaryJar_of_exists_eq_zero
            use Fin.last n
            simp only [Cube.splitAtLastFin, ne_eq, Homeomorph.trans_apply,
              Homeomorph.funSplitAt_apply, Fin.natCast_eq_last, Homeomorph.coe_prodCongr,
              Homeomorph.refl_apply, Prod.map_apply, id_eq, Homeomorph.symm_trans_apply,
              Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm,
              Homeomorph.apply_symm_apply, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]
          · -- `y` is on the sides of the (n+1)-dimensional cube
            obtain ⟨i, hi⟩ := Cube.splitAtLastFin_snd_mem_boundary_of_last_neq_zero hy hbot
            by_cases hyn : (Cube.splitAtLastFin y).fst.val ≤ (1 + t) / 2
            · -- `f'` maps the sides to `a`
              simp only [hyn, ↓reduceIte]
              apply f'.property.right
              apply Cube.mem_boundaryJar_of_lt_last
              use i.castSucc; constructor; exact Fin.castSucc_lt_last i
              -- rw [Cube.splitAtLastFin_snd_apply_eq] at hi
              obtain hi0 | hi1 := hi
              · left
                rwa [Cube.splitAtLastFin_symm_apply_eq_of_neq_last _ _ _ (Fin.castSucc_ne_last i)]
              · right
                rwa [Cube.splitAtLastFin_symm_apply_eq_of_neq_last _ _ _ (Fin.castSucc_ne_last i)]
            · -- `H` maps the sides to `a`
              simp only [hyn, ↓reduceIte]
              have := H.prop' (Set.projIcc 0 1 (by norm_num)
                  (2 * (Cube.splitAtLastFin y).1.val - (1 + t))) (Cube.splitAtLastFin y).2 ⟨i, hi⟩
              simp only [Function.comp_apply, coe_mk, toFun_eq_coe, Homotopy.coe_toContinuousMap,
                HomotopyWith.coe_toHomotopy] at this
              rw [this]
              apply f'.property.right
              exact Cube.inclToTopFace.mem_boundaryJar_of ⟨i, hi⟩ }

/-- `Ker i* ⊇ Im ∂` in
`⋯ πₙ₊₁(X, A, a) ---∂ₙ---> πₙ(A, a) ---i*ₙ--> πₙ(X, a) ⋯` -/
theorem ker_iStar_supset_im_bd (f : π_ n A a) :
    (∃ g, bd n X A a g = f) → iStar n X A a f = default := fun ⟨g, hgf⟩ ↦ by
  change _ = ⟦GenLoop.const⟧
  let g' := Quotient.out g
  rw [(by simp only [g', Quotient.out_eq] : g = ⟦g'⟧)] at hgf
  -- change jStar' .. = f at hgf
  rw [← hgf]
  change iStar' .. = _
  apply Eq.symm
  -- `0 = i* ∂ g` via the homotopy `g'`.
  exact Quotient.eq.mpr <| Nonempty.intro <|
    { toFun := g'.val.comp (toContinuousMap Cube.splitAtLastFin.symm)
      continuous_toFun := ContinuousMap.continuous _
      map_zero_left y := by
        simp only [comp_apply, ContinuousMap.coe_coe, GenLoop.const, const_apply]
        apply g'.property.right (Cube.splitAtLastFin.symm ⟨0, y⟩)
        apply Cube.mem_boundaryJar_of_exists_eq_zero
        use Fin.last _
        simp only [Cube.splitAtLastFin, ne_eq, Homeomorph.symm_trans_apply,
          Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm,
          Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
          Homeomorph.funSplitAt_symm_apply, Fin.natCast_eq_last, ↓reduceDIte]
      map_one_left y := by
        simp only [comp_apply, ContinuousMap.coe_coe, Function.comp_apply, coe_mk]
        congr 1
      prop' t y hy := by
        simp only [comp_apply, ContinuousMap.coe_coe, coe_mk, GenLoop.const, const_apply]
        apply g'.property.right
        apply Cube.mem_boundaryJar_of_lt_last
        obtain ⟨i, hi⟩ := hy
        use i.castSucc; constructor; exact Fin.castSucc_lt_last i
        obtain hi0 | hi1 := hi
        · left
          rwa [Cube.splitAtLastFin_symm_apply_eq_of_neq_last _ _ _ (Fin.castSucc_ne_last i)]
        · right
          rwa [Cube.splitAtLastFin_symm_apply_eq_of_neq_last _ _ _ (Fin.castSucc_ne_last i)] }

/-- `Ker i* ⊆ Im ∂` in
`⋯ πₙ₊₁(X, A, a) ---∂ₙ---> πₙ(A, a) ---i*ₙ--> πₙ(X, a) ⋯` -/
theorem ker_iStar_subset_im_bd (f : π_ n A a) :
    iStar n X A a f = default → ∃ g, bd n X A a g = f := fun hf0 ↦ by
  change _ = ⟦GenLoop.const⟧ at hf0
  let f' := Quotient.out f
  rw [(by simp only [f', Quotient.out_eq] : f = ⟦f'⟧)] at hf0 ⊢
  change iStar' .. = _ at hf0
  let H' : HomotopyRel .. := Quotient.eq.mp hf0.symm |>.some
  let H : RelGenLoop (n + 1) X A a :=
    ⟨ H'.toContinuousMap.comp (toContinuousMap Cube.splitAtLastFin),
      by
        apply RelGenLoop.mem_of_boundaryLid_and_boundaryJar
        · -- `H'` maps the top face into `A`
          intro y hy
          simp only [Cube.boundaryLid, Set.mem_setOf_eq] at hy
          change H' ⟨(Cube.splitAtLastFin y).1, (Cube.splitAtLastFin y).2⟩ ∈ A
          rw [Cube.splitAtLastFin_fst_eq, hy, H'.apply_one]
          simp only [coe_mk, Function.comp_apply, Subtype.coe_prop]
        · -- `H'` maps the jar to `a`
          intro y hy
          change H' ⟨(Cube.splitAtLastFin y).1, (Cube.splitAtLastFin y).2⟩ = a
          rw [Cube.splitAtLastFin_fst_eq]
          by_cases hbot : y (Fin.last _) = 0
          · -- `H'` maps the bottom face to `a`
            rw [hbot, H'.apply_zero, GenLoop.const, const_apply]
          · -- `H'` maps the sides to `a`
            obtain ⟨i, hi⟩ := Cube.splitAtLastFin_snd_mem_boundary_of_last_neq_zero hy hbot
            apply H'.prop'
            use i ⟩
  use ⟦H⟧
  change bd' .. = _
  unfold bd'
  congr 1  -- exact equality, no need to construct a homotopy
  ext y
  simp only [Function.comp_apply, GenLoop.mk_apply, coe_mk]
  simp only [Cube.inclToTopFace, coe_mk, comp_apply, ContinuousMap.coe_coe,
    Homeomorph.apply_symm_apply, Homotopy.coe_toContinuousMap, Homotopy.apply_one,
    Function.comp_apply, H]
  apply Subtype.eq_iff.mp
  rfl

-- #check (RelGenLoop n X A a : Set C(I^ Fin n, X))
-- #check (iStar n X A a : π_ n A a → π_ n X a)
-- #check (jStar n X A a : π_ n X a → π﹍ n X A a)
-- #check (jStar (n+1) X A a : π_ (n+1) X a → π﹍ (n+1) X A a)
-- #check (bd n X A a : π﹍ (n+1) X A a → π_ n A a)

end RelHomotopyGroup
