module

public import Solution.Extras
public import BoxLike

@[expose] public section

/-!
# Transport between the challenge vocabulary and the library

`toLib` identifies a `Challenge.System` with the `BoxLike.System` of the same data; every
challenge notion agrees with its library namesake on `toLib S`, by `rfl` except `gWord` (by
induction) and `dimaff` (which needs `[Nonempty ι]`).
-/

open MeasureTheory

universe u

namespace Solution.Transport

/-! ## Systems -/

section Systems

variable {ι : Type*}

/-- The library system with the data of a challenge system. -/
def toLib (S : Challenge.System ι) : BoxLike.System ι :=
  ⟨S.o, S.a, S.b, S.v, S.a_ne_zero, S.b_ne_zero, S.abs_a_lt_one, S.abs_b_lt_one⟩

/-- The challenge system with the data of a library system. -/
def ofLib (S : BoxLike.System ι) : Challenge.System ι :=
  ⟨S.o, S.a, S.b, S.v, S.a_ne_zero, S.b_ne_zero, S.abs_a_lt_one, S.abs_b_lt_one⟩

theorem toLib_ofLib (S : BoxLike.System ι) : toLib (ofLib S) = S := rfl

theorem ofLib_toLib (S : Challenge.System ι) : ofLib (toLib S) = S := rfl

end Systems

/-! ## The notions of the audited statements -/

section Notions

variable {ι : Type*}

theorem shift_eq (n : ℤ) : (Challenge.shift n : (ℤ → ι) → ℤ → ι) = BoxLike.shift n := rfl

theorem entropy_eq {α : Type*} [Fintype α] [MeasurableSpace α] (μ : Measure (ℤ → α)) :
    Challenge.entropy μ = BoxLike.entropy μ := rfl

theorem isExactDim_iff {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X)
    (d : ℝ) : Challenge.IsExactDim μ d ↔ BoxLike.IsExactDim μ d := Iff.rfl

theorem isDoubleDim_iff {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) :
    Challenge.IsDoubleDim μ ↔ BoxLike.IsDoubleDim μ := Iff.rfl

theorem upperPackingDim_eq {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : Challenge.upperPackingDim μ = BoxLike.upperPackingDim μ := rfl

theorem lowerHausdorffDim_eq {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : Challenge.lowerHausdorffDim μ = BoxLike.lowerHausdorffDim μ := rfl

variable (S : Challenge.System ι)

theorem withRotations_iff : S.WithRotations ↔ (toLib S).WithRotations := Iff.rfl

theorem proximal_iff : S.Proximal ↔ (toLib S).Proximal := Iff.rfl

/-- `g_𝐣(t)`, by induction on the word. -/
theorem gWord_eq (u : List (ι × ZMod 2)) (t : ℝ) : S.gWord u t = (toLib S).gWord u t := by
  induction u generalizing t with
  | nil => rfl
  | cons p u ih =>
    change S.g p (S.gWord u t) = (toLib S).g p ((toLib S).gWord u t)
    rw [ih]
    rfl

theorem gap_eq (n : ℕ) : S.gap n = (toLib S).gap n := by
  simp only [Challenge.System.gap, gWord_eq]
  rfl

theorem projExpSeparation_iff : S.ProjExpSeparation ↔ (toLib S).ProjExpSeparation := by
  simp only [Challenge.System.ProjExpSeparation, gap_eq]
  rfl

theorem noExactOverlaps_iff : S.NoExactOverlaps ↔ (toLib S).NoExactOverlaps := by
  simp only [Challenge.System.NoExactOverlaps, BoxLike.System.NoExactOverlaps]
  constructor
  · intro h u u' hne heq
    exact h u u' hne (by funext t; rw [gWord_eq, gWord_eq, heq])
  · intro h u u' hne heq
    exact h u u' hne (by funext t; rw [← gWord_eq, ← gWord_eq, heq])

theorem axisGap_eq (c : ZMod 2) (n : ℕ) : S.axisGap c n = (toLib S).axisGap c n := by
  simp only [Challenge.System.axisGap, gWord_eq]
  rfl

theorem axisExpSeparation_iff (c : ZMod 2) :
    S.AxisExpSeparation c ↔ (toLib S).AxisExpSeparation c := by
  simp only [Challenge.System.AxisExpSeparation, axisGap_eq]
  rfl

theorem strongOpenSet_iff : S.StrongOpenSet ↔ (toLib S).StrongOpenSet := Iff.rfl

theorem proj_eq : S.proj = (toLib S).proj := rfl

theorem attractor_eq : S.attractor = (toLib S).attractor := rfl

theorem marginal_eq [MeasurableSpace ι] (c : ZMod 2) (μ : Measure (ℤ → ι)) :
    S.marginal c μ = (toLib S).marginal c μ := rfl

theorem lyapunov₁_eq [MeasurableSpace ι] (μ : Measure (ℤ → ι)) :
    S.lyapunov₁ μ = (toLib S).lyapunov₁ μ := rfl

theorem lyapunov₂_eq [MeasurableSpace ι] (μ : Measure (ℤ → ι)) :
    S.lyapunov₂ μ = (toLib S).lyapunov₂ μ := rfl

theorem pressure_eq [Fintype ι] (s : ℝ) : S.pressure s = (toLib S).pressure s := rfl

theorem isEquilibriumState_iff [Fintype ι] [MeasurableSpace ι] (s : ℝ) (μ : Measure (ℤ → ι)) :
    S.IsEquilibriumState s μ ↔ (toLib S).IsEquilibriumState s μ := Iff.rfl

/-- The two affinity dimensions agree for a non-empty alphabet, where the pressure has a unique
zero on `[0, ∞)`. -/
theorem dimaff_eq [Fintype ι] [Nonempty ι] : S.dimaff = (toLib S).dimaff := by
  have h : ∃! s, 0 ≤ s ∧ S.pressure s = 0 := (toLib S).existsUnique_pressure_eq_zero
  rw [Challenge.System.dimaff, dite_eq_left h]
  rfl

/-- Rapaport's theorem in the challenge vocabulary is the library's statement. -/
theorem rapaportDiagonalDimension_iff :
    Challenge.RapaportDiagonalDimension.{u} ↔ BoxLike.RapaportDiagonalDimension.{u} := by
  constructor
  · intro h ι _ _ S hdiag hprox h0 h1
    have := h (ofLib S) hdiag hprox ((axisExpSeparation_iff (ofLib S) 0).2 h0)
      ((axisExpSeparation_iff (ofLib S) 1).2 h1)
    rwa [attractor_eq, dimaff_eq] at this
  · intro h ι _ _ S hdiag hprox h0 h1
    rw [attractor_eq, dimaff_eq]
    exact h (toLib S) hdiag hprox ((axisExpSeparation_iff S 0).1 h0)
      ((axisExpSeparation_iff S 1).1 h1)

end Notions

end Solution.Transport
