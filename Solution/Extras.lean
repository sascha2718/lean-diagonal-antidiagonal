module

public import Solution.Definitions

@[expose] public section

/-! Vocabulary needed only by supporting Solution results, outside the three-headline challenge. -/

namespace Challenge

open MeasureTheory Filter Topology Metric

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- The upper pointwise dimension `\overline{dim}_loc(μ, x)`: the `limsup` of
`log μ(B(x, r)) / log r` as `r ↓ 0`, with closed balls. The value is real. For a finite Borel
measure on `ℝ^d` the upper pointwise dimension lies in `[0, d]` almost everywhere, so the
real-valued `limsup` carries its usual meaning. -/
noncomputable def upperLocalDim (μ : Measure X) (x : X) : ℝ :=
  limsup (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0)

/-- The lower pointwise dimension `\underline{dim}_loc(μ, x)`: the `liminf` of
`log μ(B(x, r)) / log r` as `r ↓ 0`, with closed balls. The value is real. For a finite Borel
measure on `ℝ^d` the lower pointwise dimension lies in `[0, d]` almost everywhere, so the
real-valued `liminf` carries its usual meaning. -/
noncomputable def lowerLocalDim (μ : Measure X) (x : X) : ℝ :=
  liminf (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0)

/-- The upper packing dimension `\overline{dim}_p(μ)`: the essential supremum of the upper
pointwise dimension with respect to `μ`. The value is real. For a finite Borel measure on
`ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere, so the real-valued `essSup`
carries its usual meaning. -/
noncomputable def upperPackingDim (μ : Measure X) : ℝ := essSup (upperLocalDim μ) μ

/-- The lower Hausdorff dimension `\underline{dim}_H(μ)`: the essential infimum of the lower
pointwise dimension with respect to `μ`. The value is real. For a finite Borel measure on
`ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere, so the real-valued `essInf`
carries its usual meaning. -/
noncomputable def lowerHausdorffDim (μ : Measure X) : ℝ := essInf (lowerLocalDim μ) μ

end Challenge
