/-
Layer E of `PLAN.md`: the statement layer for `sec:lyapunov_exponents`, `sec:conditional`,
`sec:entropies`, `sec:normalisation` (second half), `sec:ledrappier_young_formula` (`thm:feng1`),
`sec:average_gibbs`, `sec:average_gibbs_entropy`, `sec:higher_dimensional_entropies` and
`sec:dimension_result_proof` of `diagonal-antidiagonal.tex`.

This file lives outside the library glob `BoxLike.*` and is never built by `lake build`. It
contains `sorry`. Check it with `lake env lean tools/LayerE.lean`. `LAYER_E.md` is the design
document: the choices made, the table of statements, the order of proof, the literature inputs
and the findings about the article.

The definitions, and the lemmas about them that depend on no `sorry`, live in three library
modules:

* `BoxLike/Conditional.lean`: partitions as atom maps, the `σ`-algebra `\widehat{ξ}`,
  conditional measures, conditional information and entropy (`sec:conditional`,
  `sec:entropies`).
* `BoxLike/SlowAxis.lean`: `Σ^τ`, `Σ^ω`, `Σ'`, the slow axis, `V_𝐢^i`
  (`sec:lyapunov_exponents`).
* `BoxLike/DimPartitions.lean`: the partitions `ξ_i`, `ξ_1^⊥`, `\overline{ξ}_i` and the
  entropies `h_i`, `\overline{h}_i` (`sec:entropies`), the average measure `\overline{μ}`
  (`sec:average_gibbs`), the ergodicity of the equilibrium state, and the real-variable lemma
  `neg_lt_entropy_of_two_le`.

The strong open set condition of `sec:box_like_self_affine` (tex lines 692 to 694) is
`System.StrongOpenSet` of `BoxLike/SeparationConditions.lean`, which also proves its passage to
`Φ^(2)`, `System.StrongOpenSet.sq` (`thm:two-block-normalisation`).

Conventions.

* A statement marked LITERATURE is a theorem the article cites without proof. It is written
  `theorem … := sorry` here; under the rules of `PLAN.md`, section 6, it becomes an `axiom` of
  `BoxLike/Literature.lean` or is proved from Mathlib.
* A statement marked PAPER is a result of the article; its docstring lists the labels its proof
  in the article depends on.
* Every declaration of this file is a `sorry` statement or depends on one. The assembly of
  `thm:main_extended` and `thm:main2` is proved from the statements.

Parts:

1. LITERATURE statements.
2. PAPER statements, in the order of the article.
3. The assembly of `thm:main_extended` and `thm:main2`, proved.
-/
import BoxLike.Birkhoff
import BoxLike.Conditional
import BoxLike.ConditionalLemmas
import BoxLike.ConditionalTwoWays
import BoxLike.DimPartitions
import BoxLike.EquilibriumEntropyLarge
import BoxLike.EquilibriumEntropySmall
import BoxLike.FengEntropy
import BoxLike.General
import BoxLike.MainTwo
import BoxLike.GibbsOrientation
import BoxLike.LiteratureFeng
import BoxLike.MeasurablePartitions
import BoxLike.PastEntropy
import BoxLike.PartitionIdentities
import BoxLike.SeparationConditions
import BoxLike.SlowAxis
import BoxLike.StrongOpenSetEntropy
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace BoxLike

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

/-! ## Part 1. LITERATURE -/

section Literature

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

end Literature

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-! ## Part 2. PAPER -/

/-! ### `sec:lyapunov_exponents` -/

end System

/-! ### `sec:conditional` -/

section Conditional

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

end Conditional

/-! ### `sec:entropies` -/

section ErgodicConstant

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

end ErgodicConstant

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-! ### `sec:normalisation` -/

/-! ### `sec:average_gibbs` -/

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-! ### `sec:average_gibbs_entropy` -/

/-! ### `sec:higher_dimensional_entropies` -/

/-! ### `sec:dimension_result_proof` -/

/-- PAPER. `thm:main_extended`, the case `s ≥ 2`: under the strong open set condition, if
`s = dimaff(𝖠) ≥ 2` and `μ` is an `s`-equilibrium state, then `π_*μ` is exact-dimensional of
dimension `2`. The article shows `s = 2`, `∑_i |det A_i| = 1`, `μ` Bernoulli with weights
`|det A_i|`, and `π_*μ` equal to normalised Lebesgue measure on an open set. Ergodicity,
proximality, rotations and projective exponential separation are not used in that argument; they
are kept as in the statement of the theorem.
Depends on: the Bernoulli equilibrium state for `s ≥ 2` (`sec:normalisation`, tex lines 2471 to
2480), strict monotonicity of `P(𝖠, ·)` (Käenmäki–Vilppolainen, Lemma 2.1), Hutchinson's
uniqueness of the invariant measure, the change of variables for Lebesgue measure. -/
theorem main_extended_ge_two (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hsosc : S.StrongOpenSet) (hs : 2 ≤ s)
    (hP : S.pressure s = 0) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    IsExactDim (μ.map S.proj) 2 := sorry

end System

/-! ## Part 3. The assembly of `thm:main_extended` and `thm:main2`, proved -/

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- PAPER. `thm:main_extended`, assembled: if `h_0(μ) ≤ -λ_2(𝖠, μ)` or the strong open set
condition holds, then `dim π_*μ = min{2, dimaff(𝖠)}`. For `s ≥ 2` the entropy alternative is
impossible and `main_extended_ge_two` applies. -/
theorem main_extended (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (herg2 : Ergodic (shift 1) (μ.map group))
    (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) (min 2 s) := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · rw [min_eq_right hs2.le]
    exact S.main_extended_lt_two hrot hprox hsep hs0 hs2 hP μ hinv herg herg2 heq hor
  · rw [min_eq_left hs2]
    have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
      rw [← heq.pressure_eq hinv hs0.le, hP]
    have hgt := neg_lt_entropy_of_two_le (S.lyapunov₂_le_lyapunov₁ hinv) (S.lyapunov₁_neg hinv)
      hs2 henergy
    exact S.main_extended_ge_two hrot hprox hsep (hor.resolve_left (not_le.2 hgt)) hs2 hP μ hinv
      heq

end System

end BoxLike
