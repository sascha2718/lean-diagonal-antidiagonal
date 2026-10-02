module

/-
The remark of `sec:dimension_of_projections` that precedes `thm:eq_state_proj_dim`: both
coordinate marginals of the `s`-equilibrium state are double-dimensional without any
separation assumption. The projections `ν_k = \overline{π}_*μ_k` of the two Gibbs measures are
exact-dimensional by Feng–Hu, the restricted projections `ν_{x,k}`, `ν_{y,k}` are dominated by
`ν_k` and inherit its dimension, `eq:restricted-projection-dimensions`, and
`thm:exact-dimensional-mixture` applies to the sums `eq:proj_eq_is_sum`.

* `System.exists_exactDim_decomposition_of_coding`: the decomposition of a marginal into two
  non-zero exact-dimensional measures.
* `System.marginal_isDoubleDim_normalised`: the remark for a tuple with a proximal diagonal
  generator.
* `System.marginal_isDoubleDim`: the remark for every proximal box-like tuple with rotations.
* `System.unique_sq_equilibrium`: the uniqueness of `μ^(2)` in `thm:two-block-normalisation`.
-/
public import BoxLike.General
public import BoxLike.LiteratureRemarks

@[expose] public section

namespace BoxLike

open MeasureTheory Set

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `eq:proj_eq_is_sum` and `eq:restricted-projection-dimensions` without separation: a
marginal `(\overline{π} ∘ κ)_*μ` of a measure `μ = \overline{κ}_*μ_1 + \overline{κ}_*μ_2` is the
sum of two non-zero exact-dimensional measures. -/
theorem exists_exactDim_decomposition_of_coding (hfh : FengHuExactDim.{u}) {r M : ℝ}
    (hS : S.Bounds r M) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (he₁ : Ergodic (shift 1) μ₁) (he₂ : Ergodic (shift 1) μ₂)
    {κ : (ℤ → ι) → ℤ → ι × ZMod 2} (hκ : Measurable κ) {R : Set (ℤ → ι × ZMod 2)}
    (hRm : MeasurableSet R) (hR : ∀ y ∈ R, κ (unCode y) = y) (hpos₁ : 0 < μ₁ R)
    (hpos₂ : 0 < μ₂ R)
    (hμ : μ = (μ₁.restrict R).map unCode + (μ₂.restrict R).map unCode) :
    ∃ (ν₁ ν₂ : Measure ℝ) (d₁ d₂ : ℝ), IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧ ν₁ ≠ 0 ∧
      ν₂ ≠ 0 ∧ μ.map (S.projBar ∘ κ) = ν₁ + ν₂ ∧ IsExactDim ν₁ d₁ ∧ IsExactDim ν₂ d₂ := by
  have hpb := hS.measurable_projBar
  have hne : ∀ ν : Measure (ℤ → ι × ZMod 2), 0 < ν R → (ν.restrict R).map S.projBar ≠ 0 := by
    intro ν hν h0
    have := congrArg (fun m : Measure ℝ => m univ) h0
    simp only [Measure.map_apply hpb MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.coe_zero,
      Pi.zero_apply] at this
    exact hν.ne' this
  obtain ⟨d₁, hd₁⟩ := hfh S μ₁ he₁
  obtain ⟨d₂, hd₂⟩ := hfh S μ₂ he₂
  refine ⟨(μ₁.restrict R).map S.projBar, (μ₂.restrict R).map S.projBar, d₁, d₂, inferInstance,
    inferInstance, hne μ₁ hpos₁, hne μ₂ hpos₂, ?_, ?_, ?_⟩
  · rw [hμ, Measure.map_add _ _ (hpb.comp hκ), map_comp_coding hκ hRm hR hpb,
      map_comp_coding hκ hRm hR hpb]
  · exact hd₁.of_le (Measure.map_mono Measure.restrict_le_self hpb)
  · exact hd₂.of_le (Measure.map_mono Measure.restrict_le_self hpb)

variable (S)

/-- The remark before `thm:eq_state_proj_dim` for a tuple with a proximal diagonal generator:
each coordinate marginal of the `s`-equilibrium state, `0 < s < 2`, is double-dimensional, and
no separation condition is assumed. -/
theorem marginal_isDoubleDim_normalised (hfk : FengKaenmakiGibbs.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hfh : FengHuExactDim.{u}) (hrot : S.WithRotations)
    (hprox : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    ∃ d₁ d₂ : ℝ, IsDoubleDim (S.marginal c μ) d₁ d₂ := by
  have hgibbs := hfk S (irreducible_of_hasProximalDiagonal hrot hprox) hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, h⟩ := hfjj S hrot hprox hs0 hs2 μ hinv hgibbs
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have := h.prob₁
  have := h.prob₂
  have : Nonempty ι := ⟨hrot.1.choose⟩
  rw [S.marginal_eq_map hS]
  rcases zmod_two_cases c with rfl | rfl
  · obtain ⟨ν₁, ν₂, d₁, d₂, hf₁, hf₂, -, -, hsum, hd₁, hd₂⟩ :=
      exists_exactDim_decomposition_of_coding hfh hS h.ergodic₁ h.ergodic₂
        (measurable_tau S.o) (measurableSet_range_tau S.o) (by rintro _ ⟨x, rfl⟩; rfl)
        (h.gibbs₁.measure_range_tau_pos h.supp₁) (h.gibbs₂.measure_range_tau_pos h.supp₂)
        h.eq_tau
    have hdd := hd₁.isDoubleDim_add hd₂
    rw [← hsum] at hdd
    exact ⟨d₁, d₂, hdd⟩
  · obtain ⟨ν₁, ν₂, d₁, d₂, hf₁, hf₂, -, -, hsum, hd₁, hd₂⟩ :=
      exists_exactDim_decomposition_of_coding hfh hS h.ergodic₁ h.ergodic₂
        (measurable_omega S.o) (measurableSet_range_omega S.o) (by rintro _ ⟨x, rfl⟩; rfl)
        (h.gibbs₁.measure_range_omega_pos h.supp₁) (h.gibbs₂.measure_range_omega_pos h.supp₂)
        h.eq_omega
    have hdd := hd₁.isDoubleDim_add hd₂
    rw [← hsum] at hdd
    exact ⟨d₁, d₂, hdd⟩

/-- The remark before `thm:eq_state_proj_dim`: for a proximal box-like tuple with rotations and
`0 < s < 2`, both coordinate marginals of the `s`-equilibrium state are double-dimensional
without any separation assumption. Grouping preserves the marginals. -/
theorem marginal_isDoubleDim (hfk : FengKaenmakiGibbs.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hfh : FengHuExactDim.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    ∃ d₁ d₂ : ℝ, IsDoubleDim (S.marginal c μ) d₁ d₂ := by
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.marginal_isDoubleDim_normalised hfk hfjj hfh hrot h hs0 hs2 μ hinv heq c
  · have := nonempty_of_measure μ
    have key := S.sq.marginal_isDoubleDim_normalised hfk hfjj hfh (S.sq_withRotations hrot) h
      hs0 hs2 (μ.map group) (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le) c
    rwa [S.marginal_sq_map_group] at key

/-- `thm:two-block-normalisation`, uniqueness of `μ^(2)`: if `𝖠²` contains a proximal diagonal
generator, then `β_*μ` is the unique `s`-equilibrium state of `𝖠²` for `0 < s < 2`. -/
theorem unique_sq_equilibrium (hfku : FengKaenmakiUnique.{u}) (hrot : S.WithRotations)
    (hprox : S.sq.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (μ' : Measure (ℤ → ι × ι)) [IsProbabilityMeasure μ']
    (hinv' : MeasurePreserving (shift 1) μ' μ') (heq' : S.sq.IsEquilibriumState s μ') :
    μ' = μ.map group := by
  exact hfku S.sq
    (irreducible_of_hasProximalDiagonal (S.sq_withRotations hrot) hprox) hs0 hs2 μ'
    (μ.map group) hinv' (measurePreserving_shift_map_group hinv) heq'
    (heq.map_group hinv hs0.le)

end System

end BoxLike
