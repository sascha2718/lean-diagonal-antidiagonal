module

public import Solution.Transport

@[expose] public section

/-!
# Proofs of the audited statements

Proofs of the seven theorems stated in `Challenge.lean`, for D. Allen, A. Käenmäki,
R. D. Prokaj, K. Simon and S. Troscheit, *Hausdorff dimension of planar box-like self-affine
sets with rotations*. Theorem and equation numbers refer to the manuscript. Each proof applies
the corresponding theorem of the library `BoxLike` to the system `toLib S`, through the
identifications of `Solution.Transport`; each cited theorem passes from its challenge statement
to its library statement. `Solution.Definitions` repeats the challenge vocabulary without
importing `Challenge.lean`.
-/

namespace Challenge

universe u

open MeasureTheory Solution.Transport

/-! ## Dimension of the projections of the equilibrium state -/

/-- Theorem 1.2 (`thm:main1`). Let `X` be a proximal box-like self-affine set with rotations
satisfying the projective exponential separation condition such that `dimaff(X) < 2`, and let
`μ` be an `s`-equilibrium state for `s = dimaff(X)`. Then each coordinate projection of `μ`,
the marginal `(proj_x)_*(π_*μ)` for `c = 0` and `(proj_y)_*(π_*μ)` for `c = 1`, is
double-dimensional with the values `min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`.
It fails to be exact-dimensional, with any dimension, precisely when
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`; at equality and above it is exact-dimensional of dimension one.
The conclusion holds for every `s`-equilibrium state, so the uniqueness of the equilibrium state
in the paper is not needed. The proof uses the cited theorems of Morris–Shmerkin,
Feng–Käenmäki, Fraser–Jordan–Jurga and Jordan–Rapaport. -/
theorem audit_main1 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) (hms : MorrisShmerkinLyapunov.{u}) (hfk : FengKaenmakiGibbs.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ) (c : ZMod 2) :
    IsDoubleDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔
        S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep h2 hinv heq
  simp only [isDoubleDim_iff, isExactDim_iff, marginal_eq, entropy_eq, lyapunov₁_eq,
    lyapunov₂_eq, dimaff_eq]
  exact (toLib S).main1_dimaff (morrisShmerkinLyapunov hms) (fengKaenmakiGibbs hfk)
    (fraserJordanJurgaDecomposition hfjj) (jordanRapaportDimension hjr) hrot hprox hsep h2 μ
    hinv heq c

/-- Theorem 4.4 (`thm:eq_state_proj_dim`). Let `X` be a proximal box-like self-affine set with
rotations satisfying the projective exponential separation condition, and let `μ` be an
`s`-equilibrium state with `0 < s < 2`. Then `(proj_x)_*(π_*μ)` (`c = 0`) and
`(proj_y)_*(π_*μ)` (`c = 1`) are double-dimensional with the values
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`, their upper packing dimension is
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` and their lower Hausdorff dimension is `min{1, -h_0(μ)/λ_2(𝖠, μ)}`.
The conclusion holds for every `s`-equilibrium state, so its uniqueness and ergodicity in the
paper are not needed. The proof uses the cited theorems of Morris–Shmerkin, Feng–Käenmäki,
Fraser–Jordan–Jurga and Jordan–Rapaport. -/
theorem audit_eq_state_proj_dim {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) {s : ℝ} (hms : MorrisShmerkinLyapunov.{u})
    (hfk : FengKaenmakiGibbs.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    IsDoubleDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) := by
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep hinv heq
  simp only [isDoubleDim_iff, upperPackingDim_eq, lowerHausdorffDim_eq, marginal_eq, entropy_eq,
    lyapunov₁_eq, lyapunov₂_eq]
  exact (toLib S).eq_state_proj_dim (morrisShmerkinLyapunov hms) (fengKaenmakiGibbs hfk)
    (fraserJordanJurgaDecomposition hfjj) (jordanRapaportDimension hjr) hrot hprox hsep hs0 hs2
    μ hinv heq c

/-! ## Dimension of the equilibrium state and of the self-affine set -/

/-- Theorem 1.3 (`thm:main2`). Let `X` be a proximal box-like self-affine set with rotations
satisfying the projective exponential separation condition such that `dimaff(X) < 2`, and let
`μ` be an `s`-equilibrium state for `s = dimaff(X)`. If
`dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, or if `X` satisfies the strong open set condition, then
`dim_H(X) = dimaff(X)`. Any `s`-equilibrium state may serve as `μ`. The proof uses all eight
cited theorems. -/
theorem audit_main2 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) (hms : MorrisShmerkinLyapunov.{u})
    (hfk : FengKaenmakiGibbs.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, lyapunov₁_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep h2 hinv heq hor
  rw [attractor_eq, dimaff_eq]
  exact (toLib S).main2 (morrisShmerkinLyapunov hms) (fengKaenmakiGibbs hfk)
    (fraserJordanJurgaDecomposition hfjj) (jordanRapaportDimension hjr) (fengInfoSum hfi)
    (fengInfoSumBar hfib) (fengLedrappierYoung hly) (fengLedrappierYoungBar hlyb) hrot hprox
    hsep h2 μ hinv heq hor

/-- Theorem 4.16 (`thm:main_extended`). Let `X` be a proximal box-like self-affine set with
rotations satisfying the projective exponential separation condition, and let `μ` be an
`s`-equilibrium state for `s = dimaff(𝖠)`. If `h_0(μ) ≤ -λ_2(𝖠, μ)` or `X` satisfies the strong
open set condition, then `π_*μ` is exact-dimensional with `dim(π_*μ) = min{2, dimaff(𝖠)}`. The
conclusion holds for every `s`-equilibrium state, so its uniqueness in the paper is not needed.
The proof uses all eight cited theorems. -/
theorem audit_main_extended {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hms : MorrisShmerkinLyapunov.{u})
    (hfk : FengKaenmakiGibbs.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) (min 2 S.dimaff) := by
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, entropy_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep hinv heq hor
  rw [isExactDim_iff, proj_eq, dimaff_eq]
  exact (toLib S).main_extended_min (morrisShmerkinLyapunov hms) (fengKaenmakiGibbs hfk)
    (fraserJordanJurgaDecomposition hfjj) (jordanRapaportDimension hjr) (fengInfoSum hfi)
    (fengInfoSumBar hfib) (fengLedrappierYoung hly) (fengLedrappierYoungBar hlyb) hrot hprox
    hsep μ hinv heq hor

/-- Theorem 4.16 (`thm:main_extended`), the case `s = dimaff(𝖠) ≥ 2`, with `s` entering as a
zero `P(𝖠, s) = 0` of the pressure. Under the strong open set condition, if `μ` is an
`s`-equilibrium state, then `π_*μ` is exact-dimensional of dimension two; it is normalised
Lebesgue measure on an open set. Rotations, proximality and the projective exponential
separation condition are not needed, and no cited theorem is used. -/
theorem audit_main_extended_ge_two {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) {s : ℝ} (hsosc : S.StrongOpenSet) (hs : 2 ≤ s)
    (hP : S.pressure s = 0) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    IsExactDim (μ.map S.proj) 2 := by
  rw [strongOpenSet_iff] at hsosc
  rw [pressure_eq] at hP
  rw [shift_eq] at hinv
  rw [isEquilibriumState_iff] at heq
  rw [isExactDim_iff, proj_eq]
  exact (toLib S).main_extended_ge_two hsosc hs hP μ hinv heq

/-- `dim_H(X) = min{2, dimaff(X)}` under the hypotheses of Theorem 4.16 (`thm:main_extended`),
the formula that the paper derives in the paragraph after (4.4)
(`eq:hausdorff_ergodic_lyapunov`). The lower bound follows from Theorem 4.16, since
`dim(π_*μ) ≤ dim_H(X)`, and the upper bound is Falconer's bound (3.7)
(`eq:hausdorff_affinity_upper_bound`), which holds for every box-like set. For `dimaff(X) < 2`
and the first alternative in the form `dimaff(X) ≤ 2 - λ_1/λ_2` this is Theorem 1.3. Any
`s`-equilibrium state for `s = dimaff(X)` may serve as `μ`. The proof uses all eight cited
theorems. -/
theorem audit_dimH_eq_min {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hms : MorrisShmerkinLyapunov.{u})
    (hfk : FengKaenmakiGibbs.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, entropy_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep hinv heq hor
  rw [attractor_eq, dimaff_eq]
  exact (toLib S).dimH_attractor_eq_min (morrisShmerkinLyapunov hms) (fengKaenmakiGibbs hfk)
    (fraserJordanJurgaDecomposition hfjj) (jordanRapaportDimension hjr) (fengInfoSum hfi)
    (fengInfoSumBar hfib) (fengLedrappierYoung hly) (fengLedrappierYoungBar hlyb) hrot hprox
    hsep μ hinv heq hor

/-- `dim_H(X) = 2` when `dimaff(X) ≥ 2` and `X` satisfies the strong open set condition: the
formula `dim_H(X) = min{2, dimaff(X)}` of the paragraph after (4.4) in this case. No measure is
assumed, since for `s = dimaff(X) ≥ 2` the `s`-equilibrium state exists, as the Bernoulli measure
of `sec:normalisation`. Rotations, proximality and the projective exponential separation
condition are not needed, and no cited theorem is used. -/
theorem audit_dimH_of_two_le {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) [Nonempty ι] (hsosc : S.StrongOpenSet)
    (h2 : 2 ≤ S.dimaff) : dimH S.attractor = 2 := by
  rw [strongOpenSet_iff] at hsosc
  rw [dimaff_eq] at h2
  rw [attractor_eq]
  exact (toLib S).dimH_attractor_of_two_le hsosc h2

end Challenge
