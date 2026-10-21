module

public import Solution.Transport

@[expose] public section

/-!
# Proofs of the audited statements

Completed headline proofs and supporting results for the three theorems in `Challenge.lean`, for D. Allen, A. Käenmäki,
R. D. Prokaj, K. Simon and S. Troscheit, *Hausdorff dimension of planar box-like self-affine
sets with rotations*. Theorem and equation numbers refer to the manuscript. Each proof applies
the corresponding theorem of the library `BoxLike` to the system `toLib S`, through the
identifications of `Solution.Transport`; each cited theorem passes from its challenge
statement to its library statement. `Solution.Definitions` repeats the challenge vocabulary
without importing `Challenge.lean`.
-/

namespace Challenge

universe u

open MeasureTheory Solution.Transport

/-! ## Dimension of the projections of the equilibrium state -/

/-- Theorem 1.2 (`thm:main1`). Let `X` be a proximal box-like self-affine set with rotations
satisfying the projective exponential separation condition, and let
`μ` be an `s`-equilibrium state for `s = dimaff(X)`. Then each coordinate projection of `μ`,
the marginal `(proj_x)_*(π_*μ)` for `c = 0` and `(proj_y)_*(π_*μ)` for `c = 1`, is
double-dimensional with the values `min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`.
It fails to be exact-dimensional, with any dimension, precisely when
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`; at equality and above it is exact-dimensional of dimension one.
The conclusion holds for every `s`-equilibrium state, so the uniqueness of the equilibrium state
in the paper is not needed. The proof uses Shmerkin's theorem
(`BoxLike.shmerkinLqDimension_holds`) through Jordan–Rapaport's argument
(`BoxLike.jordanRapaportDimension_of_shmerkin`); the inputs the paper takes from Morris–Shmerkin
and Feng–Käenmäki are theorems of the library. -/
theorem audit_main1 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ) (c : ZMod 2) :
    IsDoubleDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔
        S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep hinv heq
  simp only [isDoubleDim_iff, isExactDim_iff, marginal_eq, entropy_eq, lyapunov₁_eq,
    lyapunov₂_eq, dimaff_eq]
  exact (toLib S).main1_dimaff_all BoxLike.morrisShmerkinLyapunov_holds BoxLike.equilibriumGibbs
    BoxLike.fraserJordanJurgaDecomposition_holds hjr hrot hprox hsep μ
    hinv heq c

/-- Theorem 4.4 (`thm:eq_state_proj_dim`). Let `X` be a proximal box-like self-affine set with
rotations satisfying the projective exponential separation condition, and let `μ` be an
`s`-equilibrium state with `s > 0`. Then `(proj_x)_*(π_*μ)` (`c = 0`) and
`(proj_y)_*(π_*μ)` (`c = 1`) are double-dimensional with the values
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`, their upper packing dimension is
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` and their lower Hausdorff dimension is `min{1, -h_0(μ)/λ_2(𝖠, μ)}`.
The conclusion holds for every `s`-equilibrium state, so its uniqueness and ergodicity in the
paper are not needed. The proof uses Shmerkin's theorem (`BoxLike.shmerkinLqDimension_holds`)
through Jordan–Rapaport's argument (`BoxLike.jordanRapaportDimension_of_shmerkin`); the inputs
the paper takes from Morris–Shmerkin and Feng–Käenmäki are theorems of the library. -/
theorem audit_eq_state_proj_dim {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) {s : ℝ}
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    IsDoubleDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep hinv heq
  simp only [isDoubleDim_iff, upperPackingDim_eq, lowerHausdorffDim_eq, marginal_eq, entropy_eq,
    lyapunov₁_eq, lyapunov₂_eq]
  exact (toLib S).eq_state_proj_dim_all BoxLike.morrisShmerkinLyapunov_holds
    BoxLike.equilibriumGibbs BoxLike.fraserJordanJurgaDecomposition_holds
    hjr hrot hprox hsep hs0 μ hinv heq c

/-! ## Dimension of the equilibrium state and of the self-affine set -/

/-- Theorem 1.3 (`thm:main2`). Let `X` be a proximal box-like self-affine set with rotations
whose projective system has no exact overlaps, and let `μ` be an
`s`-equilibrium state for `s = dimaff(X)`. If
`dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, or if `X` satisfies the strong open set condition, then
`dim_H(X) = dimaff(X)`. Any `s`-equilibrium state may serve as `μ`. No cited theorem is used:
Feng's planar Ledrappier–Young formula is the library theorem `BoxLike.fengLedrappierYoung_holds`,
Kittle–Kogler's dimension formula is the library theorem `BoxLike.kittleKoglerDimension_holds`,
derived from its authors' Lean formalisation, and the inputs the paper takes from Morris–Shmerkin
and Feng–Käenmäki are theorems of the library. -/
theorem audit_main2 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  simp only [withRotations_iff, proximal_iff, noExactOverlaps_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, lyapunov₁_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hfree hinv heq hor
  rw [attractor_eq, dimaff_eq]
  exact (toLib S).main2_prose BoxLike.shannonMcMillanBreiman BoxLike.morrisShmerkinLyapunov_holds
    BoxLike.equilibriumGibbs BoxLike.fraserJordanJurgaDecomposition_holds BoxLike.fengLedrappierYoung_holds
    BoxLike.kittleKoglerDimension_holds hrot hprox hfree μ hinv heq hor

/-- Theorem 4.16 (`thm:main_extended`). Let `X` be a proximal box-like self-affine set with
rotations satisfying the projective exponential separation condition, and let `μ` be an
`s`-equilibrium state for `s = dimaff(𝖠)`. If `h_0(μ) ≤ -λ_2(𝖠, μ)` or `X` satisfies the strong
open set condition, then `π_*μ` is exact-dimensional with `dim(π_*μ) = min{2, dimaff(𝖠)}`. The
conclusion holds for every `s`-equilibrium state, so its uniqueness in the paper is not needed.
The proof uses Shmerkin's theorem (`BoxLike.shmerkinLqDimension_holds`) through
Jordan–Rapaport's argument (`BoxLike.jordanRapaportDimension_of_shmerkin`); Feng's planar
Ledrappier–Young formula and the scalar one are the library theorems
`BoxLike.fengLedrappierYoung_holds` and `BoxLike.fengLedrappierYoungBar_holds`, and the inputs
the paper takes from Morris–Shmerkin and Feng–Käenmäki are theorems of the library. -/
theorem audit_main_extended {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) (min 2 S.dimaff) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, entropy_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep hinv heq hor
  rw [isExactDim_iff, proj_eq, dimaff_eq]
  exact (toLib S).main_extended_min BoxLike.morrisShmerkinLyapunov_holds BoxLike.equilibriumGibbs
    BoxLike.fraserJordanJurgaDecomposition_holds hjr
    BoxLike.fengInfoSum_holds BoxLike.fengInfoSumBar_holds BoxLike.fengLedrappierYoung_holds
    BoxLike.fengLedrappierYoungBar_holds hrot hprox
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
`s`-equilibrium state for `s = dimaff(X)` may serve as `μ`. The proof uses Shmerkin's theorem
(`BoxLike.shmerkinLqDimension_holds`) through Jordan–Rapaport's argument
(`BoxLike.jordanRapaportDimension_of_shmerkin`); Feng's planar Ledrappier–Young formula and the
scalar one are the library theorems `BoxLike.fengLedrappierYoung_holds` and
`BoxLike.fengLedrappierYoungBar_holds`, and the inputs the paper takes from Morris–Shmerkin and
Feng–Käenmäki are theorems of the library. -/
theorem audit_dimH_eq_min {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, entropy_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep hinv heq hor
  rw [attractor_eq, dimaff_eq]
  exact (toLib S).dimH_attractor_eq_min BoxLike.morrisShmerkinLyapunov_holds
    BoxLike.equilibriumGibbs BoxLike.fraserJordanJurgaDecomposition_holds
    hjr BoxLike.fengInfoSum_holds BoxLike.fengInfoSumBar_holds
    BoxLike.fengLedrappierYoung_holds
    BoxLike.fengLedrappierYoungBar_holds hrot hprox
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



/-! ## Numbered manuscript entries

Each entry collects checked declarations with their actual Lean types. An alias of a helper
retains all its hypotheses, including internal Gibbs decompositions; it does not by itself
prove the entire prose statement. Literature inputs below name the cited theorem predicates
needed from the paper hypotheses. See `docs/correspondence.md` for the coverage assessment
and literature sources.
Missing results have entries but no manufactured proof or axiom.
-/

namespace Solution.Paper

universe u

-- PAPER_ENTRY thm:fraser
/-! 1.1 (`thm:fraser`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.System.FraserBound (`System.fraserBound_holds`, Fraser, Theorem 2.3, first
part, proved in BoxLike/Fraser/Upper.lean and BoxLike/Fraser/UpperBound.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.System.FraserROSC (`System.fraserROSC_holds`, Fraser, Theorem 2.3, second
part, proved in BoxLike/Fraser/LowerStop.lean, LowerCover.lean, Lower.lean and Main.lean); the
library statements take it as a hypothesis and Solution discharges it.

Other inputs: Finite nonempty box-like contractive invertible affine IFS; ROSC for second and
third conclusions; Both coordinate projections have Minkowski dimension one for third conclusion

Fidelity: All three assertions are proved for every box-like system, in the form of the source:
\dim_P X = \overline{\dim}_M X ≤ dimmaff(X) (`System.fraserBound_holds`); under the rectangular
open set condition \dim_P X = \dim_M X = dimmaff(X) (`System.fraserROSC_holds`; both parts,
`paper_1_1_0`); and, if moreover both coordinate projections have Minkowski dimension one,
dimmaff(X) = dimaff(X) (`paper_1_1_14`), so that \dim_P X = \dim_M X = dimaff(X)
(`paper_1_1_13`). The box dimensions of the projections exist (`System.lowerBoxDim_coord_eq`).
The upper Minkowski dimension of the manuscript is that of the source; without a separation
condition the source asserts nothing about the lower Minkowski dimension.

Proof: the paper cites Fraser with no proof; the formalisation follows Fraser's proof, with the
deviation below. The equality \dim_P X = \overline{\dim}_M X follows from bi-Lipschitz copies and
Baire category, the argument Fraser quotes (`System.packingDim_attractor`). The upper bound
\overline{\dim}_M X ≤ dimmaff(X) follows Fraser's Section 5, "Upper bound (assuming no separation
conditions)": his Lemma 5.1 (1) (`FraserUpper.exists_sum_modSvfSum_le`), the cover of X by the
copies φ_𝐢(X) of the δ-stopping words and his bounds (5.7) and (5.8) for the projections
(`System.upperBoxDim_attractor_le_of_modPressure_neg`, `System.upperBoxDim_attractor_le_dimmaff`).
The lower bound dimmaff(X) ≤ \underline{\dim}_M X under the rectangular open set condition
follows his "Lower bound (assuming the ROSC)": the open rectangles φ_𝐢(R), 𝐢 ∈ I_δ, are pairwise
disjoint, a square of side 2δ meets boundedly many of them (`System.fraserStopSum_meets_le`),
the projections onto the longer sides have the dimensions s(𝐢), and his Lemma 5.1 (2)
(`System.exists_le_fraserStopSum`) bounds the stopped sums of ψ^t from below
(`System.dimmaff_le_lowerBoxDim`). Fraser's Corollary 2.5 follows from the second part by
equality of the singular value functions on [1, 2] (`System.FraserROSC.dimmaff_eq_dimaff`).

PROOF DEVIATION: in the super-multiplicative case t ≥ s_1 + s_2 of Fraser's Lemma 5.1 (2), the
proof uses F(𝐢) = ∑_{m<b} ∑_{|𝐣|=m} ψ^t(𝐢𝐣), for a block length b with Ψ_b^t ≥ 1, in place of
Fraser's k-block stopping set I_{k,δ}; F satisfies F(𝐢) ≤ ∑_j F(𝐢j) and is comparable with ψ^t
(`System.exists_le_fraserStopSum_of_ge`). As Fraser writes it, I_{k,δ} need not be prefix-free,
so his (5.5) needs a bounded-multiplicity argument that the formalisation does not use.
-/
/-- `thm:fraser` for every box-like self-affine set, with no literature premise: both parts of
Fraser's Theorem 2.3 hold. -/
theorem paper_1_1_0 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι) :
    S.FraserBound ∧ S.FraserROSC :=
  ⟨S.fraserBound_holds, S.fraserROSC_holds⟩
noncomputable abbrev paper_1_1_1 := @BoxLike.System.FraserBound
noncomputable abbrev paper_1_1_2 := @BoxLike.System.FraserROSC
noncomputable abbrev paper_1_1_3 := @BoxLike.System.packingDim_attractor
noncomputable abbrev paper_1_1_4 := @BoxLike.System.FraserROSC.dimmaff_eq_dimaff
noncomputable abbrev paper_1_1_5 := @BoxLike.System.FraserROSC.dim_eq_dimaff
noncomputable abbrev paper_1_1_6 := @BoxLike.System.fraserBound_holds
noncomputable abbrev paper_1_1_7 := @BoxLike.System.fraserROSC_holds
noncomputable abbrev paper_1_1_8 := @BoxLike.System.upperBoxDim_attractor_le_dimmaff
noncomputable abbrev paper_1_1_9 := @BoxLike.System.upperBoxDim_attractor_le_of_modPressure_neg
noncomputable abbrev paper_1_1_10 := @BoxLike.System.dimmaff_le_lowerBoxDim
noncomputable abbrev paper_1_1_11 := @BoxLike.System.exists_le_fraserStopSum
noncomputable abbrev paper_1_1_12 := @BoxLike.System.fraserROSC_of_fraserBound
/-- `thm:fraser`, third part (Fraser's Corollary 2.5), with no literature premise: under the
rectangular open set condition, if both coordinate projections of `X` have Minkowski dimension
one, then `\dim_P X = \dim_M X = dimaff(X)`. -/
theorem paper_1_1_13 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι)
    (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, BoxLike.upperBoxDim (BoxLike.System.coord c '' S.attractor) = 1) :
    BoxLike.packingDim S.attractor = ENNReal.ofReal S.dimaff ∧
      BoxLike.lowerBoxDim S.attractor = ENNReal.ofReal S.dimaff ∧
      BoxLike.upperBoxDim S.attractor = ENNReal.ofReal S.dimaff :=
  S.fraserROSC_holds.dim_eq_dimaff hrosc hproj
/-- `thm:fraser`, third part, as the paper states it, with no literature premise: under the
rectangular open set condition, if both coordinate projections of `X` have Minkowski dimension
one, then `dimmaff(X) = dimaff(X)`. -/
theorem paper_1_1_14 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι)
    (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, BoxLike.upperBoxDim (BoxLike.System.coord c '' S.attractor) = 1) :
    S.dimmaff = S.dimaff :=
  S.fraserROSC_holds.dimmaff_eq_dimaff hrosc hproj

-- PAPER_ENTRY thm:main1
/-! 1.2 (`thm:main1`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: Finite discrete nonempty alphabet and System S; WithRotations; Proximal;
ProjExpSeparation; mu invariant probability and equilibrium at dimaff. Every value of dimaff is
covered.

Fidelity: All conclusions are proved for every value of s = dimaff: double-dimensionality, both
directions of the failure of exact-dimensionality, and exact dimension one at and above the
threshold. Lean quantifies over every equilibrium state and does not need uniqueness or
ergodicity as premises. For s >= 2 the exponents coincide, the threshold is one and both values
of the minimum are one (main1_of_two_le).

PROOF DEVIATION: For 0<s<2 the main decomposition/mixture/entropy-threshold argument agrees. Lean
calls Jordan-Rapaport directly for exact-dimensionality under separation, so Feng-Hu is not used
although the surrounding prose first establishes the no-separation component fact.

Proof for s >= 2: as in the prose of Theorem 4.4 (see that entry); it uses Jordan-Rapaport only.
-/
noncomputable abbrev paper_1_2_1 := @Challenge.audit_main1
noncomputable abbrev paper_1_2_2 := @BoxLike.System.main1_dimaff_all
noncomputable abbrev paper_1_2_3 := @BoxLike.System.main1_all
noncomputable abbrev paper_1_2_4 := @BoxLike.System.main1_of_two_le
noncomputable abbrev paper_1_2_5 := @BoxLike.System.main1
noncomputable abbrev paper_1_2_6 := @BoxLike.System.eq_state_proj_dim_all

-- PAPER_ENTRY thm:main2
/-! 1.3 (`thm:main2`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane); the library statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.KittleKoglerDimension (`kittleKoglerDimension_holds`, Kittle-Kogler,
Theorem 1.1, arXiv:2610.10511v1, 7 October 2026, derived in BoxLike/KittleKogler.lean from the
authors' Lean formalisation of the source, the library ExactOverlaps in vendor/); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: Finite discrete nonempty alphabet and System S; WithRotations; Proximal;
NoExactOverlaps for all projective words; mu invariant probability equilibrium at dimaff;
dimaff<=2-lyapunov1/lyapunov2 OR StrongOpenSet. The headline is proved by the sharp form
`System.main2_prose`, which needs neither FengInfoSumBar nor FengLedrappierYoungBar; the
Shannon-McMillan-Breiman theorem it takes is the library theorem `shannonMcMillanBreiman`.

Fidelity: Full statement proved for every value of dimaff, for every equilibrium state.

Proof: the prose argument, step by step (tex 3625-3738). For s >= 2 the threshold is impossible,
the strong open set condition forces s = 2 (`StrongOpenSet.dimaff_eq_two`) and the Lebesgue
argument of Theorem 4.16 gives dimension two. Below two: reduction to a proximal diagonal
generator; the Gibbs measure μ₁; returns to horizontal orientation; typical words by the
Shannon-McMillan-Breiman theorem (`shannonMcMillanBreiman`, proved) and Birkhoff
(`exists_class_smb`); the pigeonhole over count vectors with its explicit loss
(`log_card_le_log_card_class_add`); the genuinely diagonal subsystem (`isHomDiag_subsystem`) with
the uniform Bernoulli measure; Kittle-Kogler for the coordinate projections; under the entropy
threshold 0 <= q <= q_y = 0 by conditional-entropy monotonicity
(`condEntropyPoint_eq_zero_of_le`); in the open-set branch strong separation of the selected
subsystem (`subsystem_strongSeparation`) and then unique coding; independence of past and future
to identify Feng's entropies; Feng's formula for dim ν_n; the limit, and Falconer's upper bound
(proved internally; the prose cites it).

PROOF DEVIATION: the returns to horizontal orientation come from ergodicity through Cesàro
averages (`frequently_measure_inter_shift_ge`) along infinitely many lengths; the prose invokes
mixing of μ₁, which is not formalised and not needed.

PROOF DEVIATION: the scalar formula for the coordinate entropies of the diagonal subsystem
(tex 3716-3721) is derived from the planar `FengLedrappierYoung`, a theorem of the library
(`fengLedrappierYoung_holds`), applied to the auxiliary box-like system `lineSystem` (z ↦ diag(r, r/2) z + (t_k, 0)), which carries the line
system on the horizontal axis; the prose cites Feng's scalar theorem directly. The same
argument gives the scalar formula for the projective system of every box-like system from
`FengLedrappierYoung` (`System.isExactDim_map_projBar_of_fengLedrappierYoung`); this proof does
not use it.

The all-range endpoint `System.main2_noExactOverlaps_all` (Gibbs/Birkhoff counting with an
appended anti-diagonal symbol and an Option alphabet) is an alternative proof.
-/
noncomputable abbrev paper_1_3_1 := @Challenge.audit_main2
noncomputable abbrev paper_1_3_2 := @BoxLike.System.main2_prose
noncomputable abbrev paper_1_3_3 := @BoxLike.System.main2_noExactOverlaps_prose
noncomputable abbrev paper_1_3_4 := @BoxLike.System.main2_prose_all
noncomputable abbrev paper_1_3_5 := @BoxLike.System.StrongOpenSet.dimaff_eq_two
noncomputable abbrev paper_1_3_6 := @BoxLike.System.exists_typical_words_prose
noncomputable abbrev paper_1_3_7 := @BoxLike.System.IsHomDiag.isExactDim_map_proj
noncomputable abbrev paper_1_3_8 := @BoxLike.System.le_dimH_attractor_of_family
noncomputable abbrev paper_1_3_9 := @BoxLike.System.subsystem_strongSeparation
noncomputable abbrev paper_1_3_10 := @BoxLike.System.main2_noExactOverlaps_all

-- PAPER_ENTRY q:coincident-projection-dimensions
/-! 1.4 (`q:coincident-projection-dimensions`): intentionally_unformalized.
Literature hypotheses: none.

Other inputs: Proximal box-like with rotations; s=dimaff below 2-lyapunov1/lyapunov2; Projective
system has no exact overlaps; Asked-for property: exact-dimensional marginals with the two Gibbs
components having equal positive dimension

Fidelity: the question is recorded as the proposition
`BoxLike.CoincidentProjectionDimensionsQuestion` (BoxLike/OpenQuestion.lean): an affirmative
instance exists, with both Gibbs components and both coordinate projections exact-dimensional of
one positive dimension. The library neither proves nor refutes it. It imposes no strong
separation condition. Proposition 2.7 does not answer it.

GAP: Open question; no theorem or answer is asserted.
-/
/-- The proposition recording Question 1.4; no answer is asserted. -/
abbrev paper_1_4_1 : Prop := BoxLike.CoincidentProjectionDimensionsQuestion

-- PAPER_ENTRY thm:box_like_sa
/-! 2.1 (`thm:box_like_sa`): formalized.
Literature hypotheses: none.

Other inputs: a tuple of invertible matrices of operator norm less than one, the standing
hypotheses of sec:box_like_self_affine.

Fidelity: the tuple statement is assembled (`box_like_sa_of_contracting`, and
`PlanarSystem.box_like_sa` for the linear parts of a planar system): the tuple is box-like with
rotations, A_i = D_i R_i with diagonal D_i and square isometries R_i of which at least one exchanges
the axes and one does not, exactly when every A_i is diagonal or anti-diagonal and both types
occur. `System.isBoxLikeWithRotations_iff` and `PlanarSystem.isBoxLikeWithRotations_iff_exists_system`
identify the notion with `System.WithRotations`. "Rotating" is read as exchanging the coordinate
axes, the convention of tex 389-392; under the reading "a rotation other than the identity" the
lemma fails (−I is a diagonal rotation, the swap is an anti-diagonal reflection).

PROOF DEVIATION: Lean derives signed-permutation form from images of square corners and
orthogonality; prose asserts images of e1,e2 lie among signed coordinate vectors. This supplies
the omitted justification and is a minor proof reorganisation.
-/
noncomputable abbrev paper_2_1_1 := @BoxLike.box_like_sa_of_contracting
noncomputable abbrev paper_2_1_2 := @BoxLike.PlanarSystem.box_like_sa
noncomputable abbrev paper_2_1_3 := @BoxLike.box_like_sa
noncomputable abbrev paper_2_1_4 := @BoxLike.System.isBoxLikeWithRotations_iff
noncomputable abbrev paper_2_1_5 := @BoxLike.PlanarSystem.isBoxLikeWithRotations_iff_exists_system
noncomputable abbrev paper_2_1_6 := @BoxLike.isSquareIsometry_iff
noncomputable abbrev paper_2_1_7 := @BoxLike.isBoxLikeMatrix_iff
noncomputable abbrev paper_2_1_8 := @BoxLike.IsSquareIsometry.boxMat_zero_mul_orientation
noncomputable abbrev paper_2_1_9 := @BoxLike.System.WithRotations

-- PAPER_ENTRY thm:A_classification
/-! 2.2 (`thm:A_classification`): formalized.
Literature hypotheses: none.

Other inputs: Arbitrary index type; Every matrix determinant nonzero; TupleProximal

Fidelity: Exact trichotomy, mutual exclusivity and both explanatory equivalences are proved, in
greater generality than a finite tuple. Lines/vectors and equality/inclusion formulations are
bridged internally. Proximality is essential for the second equivalence, and is present.

PROOF DEVIATION: Prose gives citations without a proof. Lean proves the claim directly: a finite
invariant family consists of eigenlines of a proximal product (via powers and Cayley-Hamilton),
then each generator preserves or swaps the two lines. No Barany-Kaenmaki-Rossi or Barany-Kaenmaki-
Yu theorem is assumed.
-/
noncomputable abbrev paper_2_2_1 := @BoxLike.tuple_classification
noncomputable abbrev paper_2_2_2 := @BoxLike.tuple_trichotomy
noncomputable abbrev paper_2_2_3 := @BoxLike.simultaneouslyBoxLike_iff
noncomputable abbrev paper_2_2_4 := @BoxLike.not_tupleIrreducible_iff_simultaneouslyTriangular
noncomputable abbrev paper_2_2_5 := @BoxLike.tupleIrreducible_iff_lines
noncomputable abbrev paper_2_2_6 := @BoxLike.tupleStronglyIrreducible_iff_lines

-- PAPER_ENTRY thm:box_like_proximal
/-! 2.3 (`thm:box_like_proximal`): formalized.
Literature hypotheses: none.

Other inputs: System S; S.Proximal

Fidelity: Conclusion is exactly a proximal diagonal generator in S or S.sq; rotations are not
used, as in the prose.

Proof: the prose argument (`System.Proximal.box_like_proximal`, the same statement as
`hasProximalDiagonal_or_sq`). A proximal product B = A_w is diagonal with an even number of
anti-diagonal factors. A diagonal factor with entries of distinct moduli is the generator.
Otherwise |B| = c |B_1 B_2| ... |B_{2k-1} B_{2k}|, each B_{2i-1} B_{2i} is a diagonal matrix of
A^2, and if all had entries of equal moduli, |B| would be scalar. `hasProximalDiagonal_or_sq`,
which the rest of the library uses, is proved by this argument; the weighted-cocycle proof
`hasProximalDiagonal_or_sq_of_cocycle` is an alternative.
-/
noncomputable abbrev paper_2_3_1 := @BoxLike.System.Proximal.box_like_proximal
noncomputable abbrev paper_2_3_2 := @BoxLike.System.isProximalMatrix_matWord
noncomputable abbrev paper_2_3_3 := @BoxLike.System.absMat_matWord_eq_smul_pairs
noncomputable abbrev paper_2_3_4 := @BoxLike.System.sq_o_of_mem_pairs
noncomputable abbrev paper_2_3_5 := @BoxLike.System.prod_absMat_sq_mat_eq_smul
noncomputable abbrev paper_2_3_6 := @BoxLike.System.exists_anti_of_isProximalMatrix
noncomputable abbrev paper_2_3_7 := @BoxLike.System.Proximal.hasProximalDiagonal_or_sq

-- PAPER_ENTRY thm:tau_omega_sigma_commutative
/-! 2.4 (`thm:tau_omega_sigma_commutative`): formalized.
Literature hypotheses: none.

Other inputs: Arbitrary alphabet and orientation map to ZMod 2; x a two-sided sequence; n any
integer; The indicated value eps_n=0 or eps_n=1

Fidelity: All four assertions hold for every integer, including negative iterates and zero. No
geometric/proximality assumptions are needed.

PROOF DEVIATION: Same recursion/cocycle proof, implemented directly in ZMod 2 rather than an
integer antiderivative followed by reduction modulo 2. No substantive departure.
-/
noncomputable abbrev paper_2_4_1 := @BoxLike.tau_shift_of_eps_eq_zero
noncomputable abbrev paper_2_4_2 := @BoxLike.omega_shift_of_eps_eq_zero
noncomputable abbrev paper_2_4_3 := @BoxLike.tau_shift_of_eps_eq_one
noncomputable abbrev paper_2_4_4 := @BoxLike.omega_shift_of_eps_eq_one
noncomputable abbrev paper_2_4_5 := @BoxLike.eps_shift

-- PAPER_ENTRY thm:matrix_products_g_derivatives
/-! 2.5 (`thm:matrix_products_g_derivatives`): formalized.
Literature hypotheses: none.

Other inputs: System S; x any two-sided sequence; n any natural number

Fidelity: Correct product order and backward coding. Lean writes the sum of absolute coordinate
values; one coordinate vanishes, so this is the same norm as in the paper. n=0 is included by
empty products. Proximality and rotations in the prose statement are unused.

PROOF DEVIATION: Lean first proves the generic finite-word matrix product by induction, then
identifies backward coding paths. Prose inducts directly on the past length and displays the four
orientation cases. Same algebra with different factoring.
-/
noncomputable abbrev paper_2_5_1 := @BoxLike.System.abs_matWord_pastWord_e1
noncomputable abbrev paper_2_5_2 := @BoxLike.System.abs_matWord_pastWord_e2
noncomputable abbrev paper_2_5_3 := @BoxLike.System.matWord_eq
noncomputable abbrev paper_2_5_4 := @BoxLike.System.codeWord_pastWord_tau
noncomputable abbrev paper_2_5_5 := @BoxLike.System.codeWord_pastWord_omega

-- PAPER_ENTRY lem:proj_gap_dominated
/-! 2.6 (`lem:proj_gap_dominated`): formalized.
Literature hypotheses: none.

Other inputs: System S; Any subset J of its alphabet; For every i in J, S.a i = a

Fidelity: Same common-derivative subfamily argument. Lean also covers empty/singleton J and n=0
using ENNReal infimum with empty infimum=top. The prose allows anti-diagonal maps among the
subfamily, as does the Lean statement.

PROOF DEVIATION: None beyond replacing a finite minimum by the equal extended-real infimum and
proving injection of the alphabet embedding.
-/
noncomputable abbrev paper_2_6_1 := @BoxLike.System.diagGap
noncomputable abbrev paper_2_6_2 := @BoxLike.System.gap_le_diagGap

-- PAPER_ENTRY prop:ssc_no_overlap_not_pesc
/-! 2.7 (`prop:ssc_no_overlap_not_pesc`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.NoOverlap.BaranyKaenmakiPair (`baranyKaenmakiPair_holds`, the theorem of
Barany-Kaenmaki in the form the article uses: a free pair with Δ_n ≤ C_0 exp(-n²) for all n ≥ 1,
proved in BoxLike/BaranyKaenmaki.lean by a Baire category argument); the endpoint takes it as a
hypothesis and `prop_ssc_no_overlap_not_pesc_holds` discharges it. Theorem 2.1 of the source as
stated, BoxLike.NoOverlap.BaranyKaenmakiTheorem, is false (`not_baranyKaenmakiTheorem` in
BoxLike/BaranyKaenmakiCounterexample.lean); the citation at tex lines 1424 to 1429 should refer
to the proof of Theorem 2.1, which gives the bound with a constant, see docs/correspondence.md.

Other inputs: all construction parameters and all stated properties are produced in Lean

Fidelity: Exact four-map, three-diagonal/one-antidiagonal construction, proximality,
irreducibility, failure of strong irreducibility, proximal diagonal generator, SSC, free full
projective semigroup and failure of PESC. Lean also proves determinant sum<1. Freeness includes
all words, not merely admissible orientation paths. The prose requests no transcendence of
lambda; the endpoint takes `BaranyKaenmakiPair`, which holds.

Proof: the prose argument (`NoOverlap.prop_ssc_no_overlap_not_pesc`, the same statement and
premise as `ssc_no_overlap_not_pesc`). The parameters lie outside the countable union of proper
algebraic hypersurfaces over Q(λ,t) (Baire). Freeness goes through the multiplicative
independence of λ, r_1..r_5, equal symbol counts and lengths, freeness of the conjugated three-map
subsystem, the no-r coefficient of the translation variable of the first non-λ symbol and the
remaining no-r terms, then cancellation and induction. The logarithmic limits appear as: for every
c > 0, eventually Δ_n < c^n, which is what the last sentence of the proof uses. The sequential
transcendental route (`exists_params`, `Params.freeProjective`) is a retained alternative and is
not used by the endpoint.
-/
noncomputable abbrev paper_2_7_1 := @BoxLike.NoOverlap.prop_ssc_no_overlap_not_pesc
noncomputable abbrev paper_2_7_2 := @BoxLike.NoOverlap.baranyKaenmakiPair_holds
noncomputable abbrev paper_2_7_3 := @BoxLike.NoOverlap.exists_params_not_mem_exceptionalSet
noncomputable abbrev paper_2_7_4 := @BoxLike.NoOverlap.Params.mulIndependent
noncomputable abbrev paper_2_7_5 := @BoxLike.NoOverlap.Params.count_eq_of_gDeriv_eq
noncomputable abbrev paper_2_7_6 := @BoxLike.NoOverlap.eq_of_valPoly_eq
noncomputable abbrev paper_2_7_7 := @BoxLike.NoOverlap.Params.freeProjective_of_mulIndependent
noncomputable abbrev paper_2_7_8 := @BoxLike.NoOverlap.Params.strongSeparation
noncomputable abbrev paper_2_7_9 := @BoxLike.NoOverlap.Params.not_projExpSeparation
noncomputable abbrev paper_2_7_10 := @BoxLike.NoOverlap.prop_ssc_no_overlap_not_pesc_holds

-- PAPER_ENTRY thm:lyapunov_exponents_via_g_system
/-! 3.1 (`thm:lyapunov_exponents_via_g_system`): formalized.
Literature hypotheses: none.

Statement: `MatrixTuple.OseledetsSet S.mat μ` is the article's choice of Σ′ and filtration
((V1)–(V3), Borel graph, σ(Σ′)=Σ′, μ(Σ′)=1, past-saturated); Σ^τ, Σ^ω are defined by V¹ being the
y-axis and the x-axis. A choice exists (`System.oseledetsSet`, the Oseledets theorem for box-like
tuples, proved through Birkhoff), and for every choice and every 𝐢 ∈ Σ′ the four limits hold
(`System.lyapunov_exponents_via_g_system_manuscript`). The theorems of Oseledets and
Froyland-Lloyd-Quas that the article cites are proved for box-like tuples.

Fidelity: the hypotheses (proximal, rotations, ergodic, λ_2<λ_1) are those of the article; the four
limits use only (V3), the case split uses λ_2<λ_1, existence uses ergodicity. The rate-defined
`S.SigmaTau μ`, `S.SigmaOmega μ`, `S.xi μ i` used downstream are the article's objects for the
box-like choice and agree modulo null sets with those of every choice (`sigmaTau_ae_eq`,
`condMeas_oseledetsXi_ae_eq`); Feng's partitions of his admissible set have the same conditional
measures almost everywhere (`condMeas_fengXi_ae_eq`).

Proof: as in the prose: (V3) and the matrix/projective derivative identity of
`thm:matrix_products_g_derivatives`, with V¹ a coordinate axis (`V_one_eq_axis`).

GAP (representation): the Furstenberg measure Π_*μ is not formalised beyond the support of V¹ on
the axes; measurability of subspaces is a Borel graph condition; Feng's admissible set is modelled
through its atoms (any Borel full-measure set with the filtration of his (4.6)).
-/
noncomputable abbrev paper_3_1_1 := @BoxLike.System.lyapunov_exponents_via_g_system_manuscript
noncomputable abbrev paper_3_1_2 := @BoxLike.System.lyapunov_exponents_via_g_system_oseledets
noncomputable abbrev paper_3_1_3 := @BoxLike.System.oseledetsSet
noncomputable abbrev paper_3_1_4 := @BoxLike.System.V_one_eq_axis
noncomputable abbrev paper_3_1_5 := @BoxLike.System.V_eq_oseledetsSub
noncomputable abbrev paper_3_1_6 := @BoxLike.System.sigmaTau_ae_eq
noncomputable abbrev paper_3_1_7 := @BoxLike.System.sigmaOmega_ae_eq
noncomputable abbrev paper_3_1_8 := @BoxLike.System.sigmaTau_union_sigmaOmega
noncomputable abbrev paper_3_1_9 :=
  @BoxLike.MatrixTuple.OseledetsSet.disjoint_sigmaTau_sigmaOmega
noncomputable abbrev paper_3_1_10 := @BoxLike.MatrixTuple.OseledetsSet.mem_V_one_iff
noncomputable abbrev paper_3_1_11 := @BoxLike.System.condMeas_fengXi_ae_eq
noncomputable abbrev paper_3_1_12 := @BoxLike.System.condEntropy_oseledetsXi_eq
noncomputable abbrev paper_3_1_13 := @BoxLike.System.lyapunov_exponents_via_g_system
noncomputable abbrev paper_3_1_14 := @BoxLike.System.measure_SigmaPrime_compl

-- PAPER_ENTRY thm:conditional_measures_of_a_conditional_measure
/-! 3.2 (`thm:conditional_measures_of_a_conditional_measure`): formalized.
Literature hypotheses: none.

Other inputs: Any standard Borel space Omega; probability measure mu; measurable partition xi;
Borel Xi with positive mass. The saturated conclusion additionally assumes every atom through Xi
lies in Xi.

Fidelity: Exact, and more general than either shift space. Equality of measures gives the
simultaneous quantifier over all Borel A. Positivity holds mu_Xi-almost everywhere; the saturated
identity holds mu-almost everywhere on Xi.
-/
noncomputable abbrev paper_3_2_1 := @BoxLike.condMeas_cond
noncomputable abbrev paper_3_2_2 := @BoxLike.condMeas_cond_of_saturated

-- PAPER_ENTRY thm:double_conditional
/-! 3.3 (`thm:double_conditional`): formalized.
Literature hypotheses: none.

Other inputs: Any standard Borel Omega; probability measure mu; measurable partitions xi and xi';
pointwise refinement xi'(x) subset xi(x). Full-measure-domain partitions in the paper are
represented by extension with one null atom.

Fidelity: Both the iterated conditional-measure identity and the iterated integral identity are
proved. Lean writes nonnegative ENNReal integrals of measure evaluations; this is equivalent to
the article's bounded nonnegative real integrals.

PROOF DEVIATION: The prose cites Einsiedler-Ward Proposition 5.20 and Theorem 5.14. Lean
proves the needed nested-disintegration identities directly using conditional expectation,
countable generating pi-systems and uniqueness. This is an expanded foundational proof, with no
additional external premise.
-/
noncomputable abbrev paper_3_3_1 := @BoxLike.double_conditional

-- PAPER_ENTRY thm:finer_partition_dirac_mass
/-! 3.4 (`thm:finer_partition_dirac_mass`): formalized.
Literature hypotheses: none.

Other inputs: Standard Borel Omega; probability measure; two measurable partitions with pointwise
refinement; coarse conditional measures equal delta_x almost everywhere.

Fidelity: Exact after extending full-measure-domain partitions by a null atom. Lean's a.e.
conclusion expresses the article's measure-one statement.
-/
noncomputable abbrev paper_3_4_1 := @BoxLike.finer_partition_dirac_mass
noncomputable abbrev paper_3_4_2 := @BoxLike.condMeas_dirac

-- PAPER_ENTRY thm:feng_entropy_as_limit
/-! 3.5 (`thm:feng_entropy_as_limit`): formalized.
Literature hypotheses: none.

Other inputs: planar clause: every planar self-affine system (PlanarSystem), ergodic invariant
probability measure μ on Σ, λ_2<λ_1, i ≤ 2. Projective clause: proximal box-like System with
rotations, invariant probability measure ν carried by Σ_Z, ergodic or not, i ≤ 1 (rotations and
proximality are not used).

Fidelity: both clauses at the article's scope (`feng_entropy_as_limit_general`); the box-like
endpoints are specialisations through `System.toPlanar` (`feng_entropy_as_limit_boxLike_holds`).
The library statements `System.feng_entropy_as_limit` and `System.feng_entropy_as_limit_bar` take
FengInfoSum and FengInfoSumBar as hypotheses, which are theorems (`fengInfoSum_holds`,
`fengInfoSumBar_holds`).

Proof: the article quotes the limit from Feng. Lean proves Feng's identity (Lemma 4.6, first
identity of (4.16)) along Feng's Lemmas 4.4 and 4.5 for every planar system with μ(Σ′)=1
(`PlanarSystem.infoSum_xi`, `infoSum_of_pullShift`) and for the projective system
(`System.infoSum_xiBar`), and derives the limit from the proved Birkhoff theorem, as Feng does.
μ(Σ′)=1 is the planar Oseledets theorem (`PlanarSystem.measure_SigmaPrime_compl_of_ergodic`),
proved internally. Feng runs the induction (4.18) with the conditional-information chain rule;
Lean multiplies conditional measures through his Lemma 4.5(3) and takes logarithms.
-/
noncomputable abbrev paper_3_5_1 := @BoxLike.System.feng_entropy_as_limit
noncomputable abbrev paper_3_5_2 := @BoxLike.System.feng_entropy_as_limit_bar
noncomputable abbrev paper_3_5_3 := @BoxLike.tendsto_neg_log_condMeas_cylinder
noncomputable abbrev paper_3_5_4 := @BoxLike.feng_entropy_as_limit_boxLike
noncomputable abbrev paper_3_5_5 := @BoxLike.PlanarSystem.feng_entropy_as_limit_of_infoSum
noncomputable abbrev paper_3_5_6 := @BoxLike.feng_entropy_as_limit_boxLike_holds
noncomputable abbrev paper_3_5_7 := @BoxLike.feng_entropy_as_limit_of_full
noncomputable abbrev paper_3_5_8 := @BoxLike.PlanarSystem.feng_entropy_as_limit_of_full
noncomputable abbrev paper_3_5_9 := @BoxLike.PlanarSystem.infoSum_xi
noncomputable abbrev paper_3_5_10 := @BoxLike.fengInfoSum_holds
noncomputable abbrev paper_3_5_11 := @BoxLike.fengInfoSumBar_holds
noncomputable abbrev paper_3_5_12 := @BoxLike.infoSum_of_pullShift
noncomputable abbrev paper_3_5_13 := @BoxLike.feng_entropy_as_limit_general

-- PAPER_ENTRY thm:feng_entropy_kolmogorov_sinai
/-! 3.6 (`thm:feng_entropy_kolmogorov_sinai`): formalized.
Literature hypotheses: none.

Other inputs: planar self-affine system (PlanarSystem: invertible linear parts of operator norm
less than one), ergodic invariant probability measure on Σ, λ_2<λ_1: the article's hypotheses.

Fidelity: for every planar self-affine set and μ-almost every 𝐢 ∈ Σ′ the limit of
-n⁻¹ log μ(𝒫_0^{n-1}(𝐢)) of the unconditional cylinder masses exists and equals h_0(μ, 𝐢)
(`PlanarSystem.feng_entropy_kolmogorov_sinai_general`), with Σ′ the set of regular points of the
Oseledets filtration of sec:lyapunov_exponents. The box-like endpoint
`System.feng_entropy_kolmogorov_sinai` is its specialisation through `System.toPlanar`
(`System.feng_entropy_kolmogorov_sinai_toPlanar`). h_0(μ)=h(μ) at the same scope is
`PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_ergodic`.

Proof: Feng's (4.17) route through the Shannon-McMillan-Breiman theorem, proved internally by
Breiman's argument (`shannonMcMillanBreiman`: Chung's maximal inequality, Lévy's theorem and
Maker's theorem); ξ_0 is the past partition of Σ′ (`PlanarSystem.xi_zero_eq`). The input
μ(Σ′)=1 is Oseledets' theorem for invertible planar cocycles, which the article cites and the
library proves (`MatrixTuple.measure_regularSet_compl_of_ergodic`) from Kingman's subadditive
ergodic theorem (`kingman_ergodic`, from Birkhoff's theorem), the Furstenberg-Kesten limits
along the backward products (`MatrixTuple.tendsto_log_norm_pastProd`,
`MatrixTuple.tendsto_log_alpha₂_pastProd`) and the convergence of the slow directions
(`MatrixTuple.exists_slow_fast_of_tendsto`). The Kolmogorov-Sinai entropy is the supremum over
finite Borel partitions, attained at the time-zero partition (`ksEntropy_shift_eq_entropy`, the
generator theorem). λ_2<λ_1 is needed for Σ′ and its measurability; the limit itself holds for
every invariant measure with μ(Σ′)=1.
-/
noncomputable abbrev paper_3_6_1 := @BoxLike.PlanarSystem.feng_entropy_kolmogorov_sinai_general
noncomputable abbrev paper_3_6_2 := @BoxLike.System.feng_entropy_kolmogorov_sinai
noncomputable abbrev paper_3_6_3 :=
  @BoxLike.PlanarSystem.tendsto_neg_log_cylinder_dimEntropyAt_of_ergodic
noncomputable abbrev paper_3_6_4 :=
  @BoxLike.PlanarSystem.feng_entropy_kolmogorov_sinai_of_oseledetsSet
noncomputable abbrev paper_3_6_5 := @BoxLike.PlanarSystem.oseledetsSetOfErgodic
noncomputable abbrev paper_3_6_6 := @BoxLike.MatrixTuple.measure_regularSet_compl_of_ergodic
noncomputable abbrev paper_3_6_7 := @BoxLike.shannonMcMillanBreiman
noncomputable abbrev paper_3_6_8 := @BoxLike.tendsto_neg_log_cylinder_localEntropy_of_atoms
noncomputable abbrev paper_3_6_9 := @BoxLike.ksEntropy_shift_eq_entropy
noncomputable abbrev paper_3_6_10 := @BoxLike.PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_ergodic
noncomputable abbrev paper_3_6_11 := @BoxLike.System.feng_entropy_kolmogorov_sinai_toPlanar
noncomputable abbrev paper_3_6_12 := @BoxLike.System.feng_entropy_kolmogorov_sinai_bar
noncomputable abbrev paper_3_6_13 := @BoxLike.kingman_ergodic

-- PAPER_ENTRY thm:feng_entropy_zero
/-! 3.7 (`thm:feng_entropy_zero`): formalized.
Literature hypotheses: none.

Other inputs: as for 3.5: planar clause for every planar self-affine system, ergodic μ, λ_2<λ_1,
i ≤ 2; projective clause for invariant ν carried by Σ_Z, ergodic or not, i ≤ 1.

Fidelity: the article's stronger pointwise equivalence h_i(μ, 𝐢) = 0 ⟺ μ_𝐢^{ξ_i} = δ_𝐢 is proved
at the article's scope (`feng_entropy_zero_general`), not merely Feng's global vanishing
criterion; the scalar clause needs no ergodicity. The box-like endpoints are specialisations
(`feng_entropy_zero_boxLike_holds`).

Proof: as in the prose (`PlanarSystem.feng_entropy_zero_of_infoSum`): the invariant zero set of
the conditional information, vanishing information along every forward iterate, the finite
information-sum identity, mass one on every future cylinder, fixed past, and intersection to a
Dirac measure; the converse through the pointwise limit of 3.5. Feng's identity is proved
(`fengInfoSum_holds`, `fengInfoSumBar_holds`, `PlanarSystem.infoSum_xi`) and μ(Σ′)=1 is the
planar Oseledets theorem, proved internally.
-/
noncomputable abbrev paper_3_7_1 := @BoxLike.System.feng_entropy_zero
noncomputable abbrev paper_3_7_2 := @BoxLike.System.feng_entropy_zero_bar
noncomputable abbrev paper_3_7_3 := @BoxLike.localEntropy_eq_zero_iff_condMeas_eq_dirac
noncomputable abbrev paper_3_7_4 := @BoxLike.feng_entropy_zero_boxLike
noncomputable abbrev paper_3_7_5 := @BoxLike.PlanarSystem.feng_entropy_zero_of_infoSum
noncomputable abbrev paper_3_7_6 := @BoxLike.feng_entropy_zero_boxLike_holds
noncomputable abbrev paper_3_7_7 := @BoxLike.feng_entropy_zero_of_full
noncomputable abbrev paper_3_7_8 := @BoxLike.PlanarSystem.feng_entropy_zero_of_full
noncomputable abbrev paper_3_7_9 := @BoxLike.fengInfoSum_holds
noncomputable abbrev paper_3_7_10 := @BoxLike.fengInfoSumBar_holds
noncomputable abbrev paper_3_7_11 := @BoxLike.feng_entropy_zero_general

-- PAPER_ENTRY thm:partitions_xi1
/-! 3.8 (`thm:partitions_xi1`): formalized.
Literature hypotheses: none.

Other inputs: The four component endpoints require only a box-like System, a measure and
membership in the corresponding orientation set; the Omega components additionally require
lambda_2 < lambda_1. The combined wrapper has unused rotations, proximality, invariance and
ergodicity binders.

Fidelity: All four identities and all four saturation inclusions are present. The combined wrapper
adds proximality, which is absent from the explicit statement of this lemma, but the stronger
component lemmas avoid that unnecessary assumption.
-/
noncomputable abbrev paper_3_8_1 := @BoxLike.System.partitions_xi1
noncomputable abbrev paper_3_8_2 := @BoxLike.System.xi_one_of_mem_SigmaTau
noncomputable abbrev paper_3_8_3 := @BoxLike.System.xiPerp_of_mem_SigmaTau
noncomputable abbrev paper_3_8_4 := @BoxLike.System.xi_one_of_mem_SigmaOmega
noncomputable abbrev paper_3_8_5 := @BoxLike.System.xiPerp_of_mem_SigmaOmega

-- PAPER_ENTRY thm:partition_tau_conj
/-! 3.9 (`thm:partition_tau_conj`): formalized.
Literature hypotheses: none.

Other inputs: The combined theorem takes rotations, proximality, invariance, ergodicity and a
strict Lyapunov gap; as in 3.8 only the gap enters the actual identities, and underlying
components remove the unused proximality binder. The identity holds for all natural n, stronger
than n>=1.

Fidelity: Matches both orientation cases and the join with the future-cylinder partition; the
unnecessary proximality binder should not be silently treated as part of the manuscript statement.
-/
noncomputable abbrev paper_3_9_1 := @BoxLike.System.partition_tau_conj
noncomputable abbrev paper_3_9_2 := @BoxLike.System.image_unCode_xiBar_inter_cylinder_tau
noncomputable abbrev paper_3_9_3 := @BoxLike.System.image_unCode_xiBar_inter_cylinder_omega

-- PAPER_ENTRY thm:irred_eq_state
/-! 3.10 (`thm:irred_eq_state`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.FengKaenmakiNormEquilibrium (`fengKaenmakiNormEquilibrium_holds`,
Feng-Kaenmaki, Discrete Contin. Dyn. Syst. 30 (2011), Proposition 1.2, for real planar invertible
irreducible tuples and the potential ‖·‖^q on the one-sided shift, read in arXiv:1009.3129v1,
proved in BoxLike/QuasiMultiplicative/); the general endpoint
`MatrixTuple.irred_eq_state_of_fengKaenmaki` takes it as a hypothesis and Solution discharges it
(`paper_3_10_25`).
Proved inputs: BoxLike.FengKaenmakiGibbs (`fengKaenmakiGibbs_holds`) and
BoxLike.FengKaenmakiUnique (`fengKaenmakiUnique_holds`), its box-like specialisations
(`FengKaenmakiNormEquilibrium.fengKaenmakiGibbs`, `.fengKaenmakiUnique`); the irreducible
box-like endpoint `System.irred_eq_state` takes them as hypotheses and Solution discharges them
(`paper_3_10_26`).

Other inputs: an irreducible tuple of invertible planar matrices (`TupleIrreducible`) and s>0;
Feng-Kaenmaki, Proposition 1.2, enters for 0<s<2 only. The endpoint for tuples with rotations
takes a box-like System with rotations and s>0.

Fidelity: the full statement at the article's scope, every irreducible tuple in GL_2(R)^N and
every s>0: existence, uniqueness, ergodicity and the Gibbs bounds of the s-equilibrium state
(`MatrixTuple.irred_eq_state_of_fengKaenmaki`; with no premise, `paper_3_10_25`). The box-like
endpoint `System.irred_eq_state` is its specialisation from the box-like predicates (with no
premise, `paper_3_10_26`). Existence of an ergodic equilibrium state for every invertible tuple
and s>=0, reducible or not (tex 2217-2218), is `MatrixTuple.exists_ergodic_isEquilibriumState`,
without literature input. For box-like tuples
with rotations, which need not be irreducible and are the tuples of the main results, the full
statement holds for every s>0 with no literature premise (`System.irred_eq_state_of_withRotations`);
the main line takes its Gibbs bounds through `EquilibriumGibbsStatement` (`equilibriumGibbs`) and
its uniqueness through `System.unique_of_withRotations`.

Proof: as in the prose: existence by the variational construction
(`MatrixTuple.exists_isEquilibriumState`); for 0<s<2 the norm potential for s<=1 and the
rescaled tuple A'_i = |det A_i|^((s-1)/(2-s)) A_i with exponent 2-s for 1<s<2
(`FengKaenmakiNormEquilibrium.svf`, `isEquilibriumState_iff_rescale`,
`hasGibbsBounds_iff_rescale`) and the reduction to the one-sided shift
(`FengKaenmakiNormEquilibrium.twoSided`, `isNormEquilibriumPlus_map_eta_iff`); for s>=2 the
determinant Bernoulli calculation (`MatrixTuple.irred_eq_state_of_two_le`). Ergodicity follows
from uniqueness (`MatrixTuple.ergodic_of_unique`), which the source states as a remark after its
(1.4); the article credits the whole proposition to Feng-Kaenmaki, whose Proposition 1.2 does not
cover s>=2.

Proof of Feng-Kaenmaki, Proposition 1.2 (BoxLike/QuasiMultiplicative/,
`fengKaenmakiNormEquilibrium_holds`), along the architecture of Bowen's theorem: the norm of an
irreducible tuple is quasi-multiplicative with connecting words of length at most one, by
compactness of the unit sphere of the matrices, and invertibility is not needed
(`MatrixTuple.normQuasiMultiplicative_of_irreducible`); for q>0 the periodic-orbit measures of
‖·‖^q satisfy uniform Gibbs bounds for every fixed word once their period is large, a weak-star
limit point is an invariant Gibbs measure, and a Gibbs measure is ergodic by a quasi-Bernoulli
lower bound (`normGibbsExistence`, `MatrixTuple.HasNormGibbs.ergodic`); for every q>=0 an
invariant q-equilibrium state μ on Σ satisfies D_n(μ ‖ μ_q) <= log C on the cylinder partitions,
so μ ≪ μ_q and μ = μ_q (`MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs`); the one-sided
statement follows through the natural extension (`exists_map_eta_eq`,
`MatrixTuple.hasNormGibbsPlus_map_eta_iff`, `fengKaenmakiNormEquilibrium_of_normGibbsExistence`).

Proof for tuples with rotations: for 0<s<2 the image μ_G = q_*μ₁ of Bowen's ergodic Gibbs
measure μ₁ for f_{1,s} on Σ_Z has the Gibbs bounds with a constant K
(`System.exists_isGibbs_potential₁`, `System.hasGibbsBounds_map_unCode`); for an invariant
s-equilibrium state μ the equilibrium equation at level n and the lower Gibbs bound give the
relative entropy bound D_n(μ ‖ μ_G) ≤ log K on the cylinder partitions
(`IsEquilibriumState.blockRelEntropy_le`), hence μ ≪ μ_G
(`absolutelyContinuous_of_blockRelEntropy_le`) and μ = μ_G, since μ_G is ergodic
(`IsEquilibriumState.eq_map_unCode`); for s>=2 μ is the Bernoulli measure of 3.12. Uniqueness,
ergodicity and the Gibbs bounds follow (`System.unique_of_withRotations`,
`IsEquilibriumState.ergodic_of_withRotations`,
`IsEquilibriumState.hasGibbsBounds_of_withRotations`).
-/
noncomputable abbrev paper_3_10_0 := @BoxLike.MatrixTuple.irred_eq_state_of_fengKaenmaki
noncomputable abbrev paper_3_10_1 := @BoxLike.System.irred_eq_state
noncomputable abbrev paper_3_10_2 := @BoxLike.System.unique_of_irreducible
noncomputable abbrev paper_3_10_3 := @BoxLike.System.IsEquilibriumState.ergodic_of_irreducible
noncomputable abbrev paper_3_10_4 :=
  @BoxLike.System.IsEquilibriumState.hasGibbsBounds_of_irreducible
noncomputable abbrev paper_3_10_5 := @BoxLike.MatrixTuple.exists_isEquilibriumState
noncomputable abbrev paper_3_10_6 := @BoxLike.MatrixTuple.irred_eq_state_of_two_le
noncomputable abbrev paper_3_10_7 := @BoxLike.MatrixTuple.ergodic_of_unique
noncomputable abbrev paper_3_10_8 := @BoxLike.MatrixTuple.isEquilibriumState_iff_rescale
noncomputable abbrev paper_3_10_9 := @BoxLike.MatrixTuple.hasGibbsBounds_iff_rescale
noncomputable abbrev paper_3_10_10 := @BoxLike.MatrixTuple.isNormEquilibriumPlus_map_eta_iff
noncomputable abbrev paper_3_10_11 := @BoxLike.MatrixTuple.exists_ergodic_isEquilibriumState
noncomputable abbrev paper_3_10_12 := @BoxLike.FengKaenmakiNormEquilibrium.svf
noncomputable abbrev paper_3_10_13 := @BoxLike.FengKaenmakiNormEquilibrium.twoSided
noncomputable abbrev paper_3_10_14 := @BoxLike.FengKaenmakiNormEquilibrium.fengKaenmakiGibbs
noncomputable abbrev paper_3_10_15 := @BoxLike.FengKaenmakiNormEquilibrium.fengKaenmakiUnique
noncomputable abbrev paper_3_10_16 := @BoxLike.System.irred_eq_state_of_withRotations
noncomputable abbrev paper_3_10_17 := @BoxLike.System.unique_of_withRotations
noncomputable abbrev paper_3_10_18 := @BoxLike.System.IsEquilibriumState.ergodic_of_withRotations
noncomputable abbrev paper_3_10_19 :=
  @BoxLike.System.IsEquilibriumState.hasGibbsBounds_of_withRotations
noncomputable abbrev paper_3_10_20 :=
  @BoxLike.System.existsUnique_isEquilibriumState_of_withRotations
noncomputable abbrev paper_3_10_21 := @BoxLike.System.IsEquilibriumState.eq_map_unCode
noncomputable abbrev paper_3_10_22 := @BoxLike.System.IsEquilibriumState.blockRelEntropy_le
noncomputable abbrev paper_3_10_23 := @BoxLike.absolutelyContinuous_of_blockRelEntropy_le
/-- The Gibbs bounds of `thm:irred_eq_state` for tuples with rotations, as the main line takes
them: `EquilibriumGibbsStatement` holds. -/
theorem paper_3_10_24 : BoxLike.EquilibriumGibbsStatement.{u} := BoxLike.equilibriumGibbs
open MeasureTheory in
/-- `thm:irred_eq_state` at the article's scope, with no literature premise: for an irreducible
tuple of invertible planar matrices and every `s > 0` there is a unique invariant
`s`-equilibrium state, and it is ergodic with the Gibbs bounds. `FengKaenmakiNormEquilibrium` is
`fengKaenmakiNormEquilibrium_holds`. -/
theorem paper_3_10_25 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i, (A i).det ≠ 0)
    (hirr : BoxLike.TupleIrreducible A) {s : ℝ} (hs0 : 0 < s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (BoxLike.shift 1) μ μ ∧
      BoxLike.MatrixTuple.IsEquilibriumState A s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (BoxLike.shift 1) ν ν →
        BoxLike.MatrixTuple.IsEquilibriumState A s ν → ν = μ) ∧
      Ergodic (BoxLike.shift 1) μ ∧ BoxLike.MatrixTuple.HasGibbsBounds A s μ :=
  BoxLike.MatrixTuple.irred_eq_state_of_fengKaenmaki BoxLike.fengKaenmakiNormEquilibrium_holds A hA
    hirr hs0
open MeasureTheory in
/-- `thm:irred_eq_state` for irreducible box-like systems, with no literature premise:
`FengKaenmakiGibbs` and `FengKaenmakiUnique` are `fengKaenmakiGibbs_holds` and
`fengKaenmakiUnique_holds`. -/
theorem paper_3_10_26 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : BoxLike.System ι) (hirr : S.Irreducible) {s : ℝ} (hs0 : 0 < s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (BoxLike.shift 1) μ μ ∧
      S.IsEquilibriumState s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (BoxLike.shift 1) ν ν →
        S.IsEquilibriumState s ν → ν = μ) ∧
      Ergodic (BoxLike.shift 1) μ ∧ S.HasGibbsBounds s μ :=
  S.irred_eq_state BoxLike.fengKaenmakiGibbs_holds BoxLike.fengKaenmakiUnique_holds hirr hs0
/-- Feng–Käenmäki, Proposition 1.2, in the form of the source: `FengKaenmakiNormEquilibrium`
holds. -/
theorem paper_3_10_27 : BoxLike.FengKaenmakiNormEquilibrium.{u} :=
  BoxLike.fengKaenmakiNormEquilibrium_holds
/-- The Gibbs bounds of `thm:irred_eq_state` for irreducible box-like tuples and `0 < s < 2`:
`FengKaenmakiGibbs` holds. -/
theorem paper_3_10_28 : BoxLike.FengKaenmakiGibbs.{u} := BoxLike.fengKaenmakiGibbs_holds
/-- The uniqueness part of `thm:irred_eq_state` for irreducible box-like tuples and
`0 < s < 2`: `FengKaenmakiUnique` holds. -/
theorem paper_3_10_29 : BoxLike.FengKaenmakiUnique.{u} := BoxLike.fengKaenmakiUnique_holds
noncomputable abbrev paper_3_10_30 := @BoxLike.fengKaenmakiNormEquilibrium_of_normGibbsExistence
noncomputable abbrev paper_3_10_31 := @BoxLike.normGibbsExistence
noncomputable abbrev paper_3_10_32 := @BoxLike.MatrixTuple.normQuasiMultiplicative_of_irreducible
noncomputable abbrev paper_3_10_33 := @BoxLike.MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs
noncomputable abbrev paper_3_10_34 := @BoxLike.MatrixTuple.HasNormGibbs.ergodic
noncomputable abbrev paper_3_10_35 := @BoxLike.MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq
noncomputable abbrev paper_3_10_36 :=
  @BoxLike.MatrixTuple.NormQuasiMultiplicative.exists_ergodic_hasNormGibbs

-- PAPER_ENTRY thm:two-block-normalisation
/-! 3.11 (`thm:two-block-normalisation`): formalized.
Literature hypotheses: none.

Other inputs: a proximal System with rotations; s>0; an invariant s-equilibrium probability
measure mu.

Fidelity: one endpoint (`System.two_block_normalisation`) assembles every conclusion: attractor
equality; both matrix types; a proximal diagonal generator of the second iterate; preservation of
strong separation, the strong open set condition and projective exponential separation; μ^(2) an
invariant s-equilibrium state, the unique one, and ergodic; P(A², t) = 2P(A, t) for t>=0;
h(μ^(2)) = 2h(μ) and both Lyapunov scalings; equality of the projected measures. The wrapper
`System.two_block_normalisation_consequences` gives the affinity dimension, the Lyapunov
dimension, the coordinate marginals and that grouping a Bernoulli measure gives a Bernoulli
measure.

Proof: as in the prose; uniqueness and ergodicity come from Proposition 3.10 applied to A²,
which has rotations, with no literature premise (`System.unique_of_withRotations`,
`IsEquilibriumState.ergodic_of_withRotations`); the proximal diagonal generator of A² squares the
original one or comes from `hasProximalDiagonal_or_sq` (`Proximal.sq_hasProximalDiagonal`); the
floor/subsequence argument gives projective separation.

The remark on invertible linear changes of coordinates (tex 2352-2353) is formalised in
BoxLike/Planar/ChangeOfBasis.lean (`MatrixTuple.comparable_conj`, `PlanarSystem.ConjBy.*`).
-/
noncomputable abbrev paper_3_11_1 := @BoxLike.System.two_block_normalisation
noncomputable abbrev paper_3_11_2 := @BoxLike.System.two_block_normalisation_consequences
noncomputable abbrev paper_3_11_3 := @BoxLike.System.Proximal.sq_hasProximalDiagonal
noncomputable abbrev paper_3_11_4 := @BoxLike.System.sq_irreducible
noncomputable abbrev paper_3_11_5 := @BoxLike.IsBernoulli.map_group
noncomputable abbrev paper_3_11_6 := @BoxLike.System.IsEquilibriumState.map_group

-- PAPER_ENTRY thm:bernoulli_equilibrium
/-! 3.12 (`thm:bernoulli_equilibrium`): formalized.
Literature hypotheses: none.

Other inputs: Finite nonempty alphabet and box-like System, s>=2. Existing-measure uniqueness
needs an invariant equilibrium probability measure, which itself implies the alphabet is nonempty.
Proximality, rotations and separation are unnecessary.

Fidelity: Complete for the section's box-like setting, including s=2, the explicit normalised
determinant weights, existence and uniqueness.
-/
noncomputable abbrev paper_3_12_1 := @BoxLike.System.pressure_of_two_le
noncomputable abbrev paper_3_12_2 := @BoxLike.System.detWeight
noncomputable abbrev paper_3_12_3 := @BoxLike.System.isEquilibriumState_bernoulli
noncomputable abbrev paper_3_12_4 := @BoxLike.System.IsEquilibriumState.eq_bernoulli
noncomputable abbrev paper_3_12_5 := @BoxLike.System.existsUnique_isEquilibriumState_of_two_le
noncomputable abbrev paper_3_12_6 := @BoxLike.bernoulli_cylinder

-- PAPER_ENTRY thm:sigma_tau_omega_positive_eq_measure
/-! 3.13 (`thm:sigma_tau_omega_positive_eq_measure`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.

Other inputs: System with rotations; 0<s<2; invariant ergodic equilibrium probability measure;
hfk. Uniqueness is not used. No Morris-Shmerkin hypothesis or simple-spectrum assumption is
required by this particular Lean endpoint, and proximality, a hypothesis of the manuscript, is
not used.

Fidelity: Both positive-mass conclusions match, without the proximality of the manuscript. The
Birkhoff display carries its almost-everywhere qualifier (tex 2462).

Proof: as in the prose (`System.sigma_tau_omega_positive_eq_measure`,
BoxLike/Aligned/SigmaTauOmega.lean, the form used by 4.6): the counting inequality summed along
the orbit, and Birkhoff's theorem for the indicators of Σ^τ and of the anti-diagonal cylinders.
The integrated one-step bound mu([i]) <= 2 mu(SigmaTau) from invariance
(`System.sigma_tau_omega_positive`) is an alternative proof.
-/
noncomputable abbrev paper_3_13_1 := @BoxLike.System.sigma_tau_omega_positive_eq_measure
noncomputable abbrev paper_3_13_2 := @BoxLike.System.measureReal_antiDiagSet_le
noncomputable abbrev paper_3_13_3 := @BoxLike.System.birkhoffSum_antiDiagSet_le
noncomputable abbrev paper_3_13_4 := @BoxLike.System.indicator_antiDiagSet_le
noncomputable abbrev paper_3_13_5 := @BoxLike.System.sigma_tau_omega_positive
noncomputable abbrev paper_3_13_6 := @BoxLike.System.measure_cylinder_le_two_mul

-- PAPER_ENTRY thm:eq_state_is_sum
/-! 3.14 (`thm:eq_state_is_sum`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean), only to
pass from the manuscript's hypothesis "μ is the s-equilibrium state" to the Gibbs bounds that the
decomposition takes; every invariant s-equilibrium state is the image q_*μ₁ of the decomposition
(`System.IsEquilibriumState.eq_map_unCode`).

Other inputs: a box-like System with rotations and 0<s<2; an invariant probability measure μ with
the Gibbs bounds of `thm:irred_eq_state`.

Fidelity: the article quotes the proposition from Fraser-Jordan-Jurga (Lemma 1.3, Corollaries
1.5 and 1.6); the library proves it (`fraserJordanJurgaDecomposition_holds`): the ergodic
s-Gibbs measures μ₁, μ₂ carried by Σ_Z, the four decompositions of μ, and
λ_1(𝖠, μ) = \overline{λ}(𝖠, μ₁), λ_2(𝖠, μ) = \overline{λ}(𝖠, μ₂). The pressure identities
P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s}) are `System.pressure_eq_pressureZ₁` and
`System.pressure_eq_pressureZ₂`. Proximality and a proximal diagonal generator are not used.

Proof: Bowen's theorem (`bowenGibbsExistence`) gives the ergodic Gibbs measure μ₁ for f_{1,s} on
the mixing Σ_Z, and μ₂ is its image under the exchange of the axes; the image of μ₁ under
forgetting the axis has the Gibbs bounds of φ^s, since each word has two lifts and φ^s(A_w) is
the larger of the two exponentials (`System.hasGibbsBounds_map_unCode`); every invariant measure
with the Gibbs bounds equals this ergodic measure (`System.eq_of_hasGibbsBounds`); the four
decompositions follow from Σ_Z = τ(Σ) ⊔ ω(Σ) and the exchange of the two ranges; the Lyapunov
identities follow from Birkhoff's theorem along the two lifts and the relative-entropy comparison
\overline{λ}(𝖠, μ₂) ≤ \overline{λ}(𝖠, μ₁) (`System.lyapunov_map_unCode_of_isGibbs`).
-/
/-- `thm:eq_state_is_sum`: the decomposition of `FraserJordanJurgaDecomposition` holds. -/
theorem paper_3_14_0 : BoxLike.FraserJordanJurgaDecomposition.{u} :=
  BoxLike.fraserJordanJurgaDecomposition_holds
noncomputable abbrev paper_3_14_1 := @BoxLike.FraserJordanJurgaDecomposition.{u}
noncomputable abbrev paper_3_14_2 := @BoxLike.System.GibbsDecomposition
noncomputable abbrev paper_3_14_3 := @BoxLike.System.pressure_eq_pressureZ₁
noncomputable abbrev paper_3_14_4 := @BoxLike.System.pressure_eq_pressureZ₂
noncomputable abbrev paper_3_14_5 := @BoxLike.System.GibbsDecomposition.lyapunov₁_eq_integral
noncomputable abbrev paper_3_14_6 := @BoxLike.System.GibbsDecomposition.lyapunov₂_eq_integral
noncomputable abbrev paper_3_14_7 := @BoxLike.System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂
noncomputable abbrev paper_3_14_8 := @BoxLike.System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂
noncomputable abbrev paper_3_14_9 := @BoxLike.System.GibbsDecomposition.map_flip
noncomputable abbrev paper_3_14_10 := @BoxLike.System.decomposition₂_of_decompositions
noncomputable abbrev paper_3_14_20 := @BoxLike.System.eq_of_hasGibbsBounds
noncomputable abbrev paper_3_14_21 := @BoxLike.System.hasGibbsBounds_map_unCode
noncomputable abbrev paper_3_14_22 := @BoxLike.System.lyapunov_map_unCode_of_isGibbs
noncomputable abbrev paper_3_14_23 := @BoxLike.System.exists_isGibbs_potential₁
noncomputable abbrev paper_3_14_24 := @BoxLike.System.IsEquilibriumState.eq_map_unCode

-- PAPER_ENTRY thm:exact-dimensional-mixture
/-! 4.1 (`thm:exact-dimensional-mixture`): formalized.
Literature hypotheses: none.

Other inputs: Finite Borel measures on a metric space with the Besicovitch covering property;
nonzero assumptions only where positive occurrence/uniqueness needs them. Finite-dimensional real
normed spaces satisfy the required type classes.

Fidelity: All four conclusions, including positive occurrence of each distinct value, are
represented. The real-space specialization of the generic lemmas matches the manuscript.

PROOF DEVIATION: The manuscript omits the proof. Lean supplies the Radon–Nikodym/Besicovitch
differentiation proof, which proves the asserted componentwise local dimensions.
-/
noncomputable abbrev paper_4_1_1 := @BoxLike.IsExactDim.ae_hasLocalDim_add_left
noncomputable abbrev paper_4_1_2 := @BoxLike.IsExactDim.ae_hasLocalDim_add_right
noncomputable abbrev paper_4_1_3 := @BoxLike.IsExactDim.isDoubleDim_add
noncomputable abbrev paper_4_1_4 := @BoxLike.IsExactDim.measure_hasLocalDim_add_left_pos
noncomputable abbrev paper_4_1_5 := @BoxLike.IsExactDim.measure_hasLocalDim_add_right_pos
noncomputable abbrev paper_4_1_6 := @BoxLike.isExactDim_add_iff

-- PAPER_ENTRY thm:feng1
/-! 4.2 (`thm:feng1`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.PlanarFengLedrappierYoung (`planarFengLedrappierYoung_holds`, Feng, Duke
Math. J. 172 (2023), Theorems 1.2 (ii) and 1.3, formula (1.6), for planar self-affine systems,
arXiv:1901.01691v2; proved in BoxLike/FengLedrappierYoung.lean along Feng's Sections 4 to 6 in the
plane: the claims (C1) to (C3) by general theorems about nested measurable partitions,
Proposition 5.1 from the planar form of Lemma 5.4, Proposition 5.5 by Besicovitch differentiation
and the weak maximal inequality on the atoms); `planar_feng1` takes it as a hypothesis and
`paper_4_2_12` discharges it.
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`), its box-like
specialisation (`PlanarFengLedrappierYoung.fengLedrappierYoung`).
Proved input: BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part of
thm:feng1 from the first, `fengLedrappierYoungBar_of_fengLedrappierYoung` in
BoxLike/ProjectiveLineSystem.lean); `planar_feng1` takes it as a hypothesis and `paper_4_2_10`
discharges it from BoxLike.PlanarFengLedrappierYoung.

Other inputs: planar clause: every planar self-affine system (PlanarSystem), ergodic invariant
probability measure, λ₂<λ₁. Scalar clause: proximal box-like System with rotations, ergodic
invariant probability measure carried by Σ_Z; its proof needs neither rotations nor
proximality.

Fidelity: both clauses at the article's scope (`planar_feng1`), proved (`paper_4_2_12`); the
article gives no proof. Both follow from PlanarFengLedrappierYoung (`paper_4_2_11`): the planar clause
is `PlanarSystem.feng1`, and the scalar clause is the planar formula for the planar system
z ↦ diag(g'_j, g'_j/2) z + (g_j(0), 0) of the projective system, whose attractor lies on the
horizontal axis, whose exponents are \overline{λ} and \overline{λ} - log 2 and whose partitions
ξ_2 and ξ_1 agree (`System.isExactDim_map_projBar_of_fengLedrappierYoung`, for every box-like
system). Lean uses closed sup-norm balls, which give the same pointwise dimension as Feng's
closed Euclidean balls. Feng's partitions on his admissible set have almost everywhere the same
conditional measures as the partitions of the library (`PlanarSystem.condMeas_fengXi_ae_eq`), so
the source statement implies the transcription (`planarFengLedrappierYoung_of_fengXi`).
-/
noncomputable abbrev paper_4_2_1 := @BoxLike.planar_feng1
noncomputable abbrev paper_4_2_2 := @BoxLike.PlanarSystem.feng1
noncomputable abbrev paper_4_2_3 := @BoxLike.PlanarFengLedrappierYoung.{u}
noncomputable abbrev paper_4_2_4 := @BoxLike.PlanarFengLedrappierYoung.fengLedrappierYoung
noncomputable abbrev paper_4_2_5 := @BoxLike.planarFengLedrappierYoung_of_fengXi
noncomputable abbrev paper_4_2_6 := @BoxLike.FengLedrappierYoung.{u}
noncomputable abbrev paper_4_2_7 := @BoxLike.FengLedrappierYoungBar.{u}
noncomputable abbrev paper_4_2_8 := @BoxLike.fengLedrappierYoungBar_of_fengLedrappierYoung
noncomputable abbrev paper_4_2_9 := @BoxLike.System.isExactDim_map_projBar_of_fengLedrappierYoung
/-- `thm:feng1`, second part, from the first: `PlanarFengLedrappierYoung` implies
`FengLedrappierYoungBar`, through its box-like specialisation `FengLedrappierYoung`. -/
theorem paper_4_2_10 (h : BoxLike.PlanarFengLedrappierYoung.{u}) :
    BoxLike.FengLedrappierYoungBar.{u} :=
  BoxLike.fengLedrappierYoungBar_of_fengLedrappierYoung h.fengLedrappierYoung
open MeasureTheory BoxLike in
/-- `thm:feng1`, both parts, at the article's scope, from `PlanarFengLedrappierYoung` alone. -/
theorem paper_4_2_11 (h : PlanarFengLedrappierYoung.{u}) :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      IsExactDim (μ.map P.proj)
        ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
          (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → Ergodic (shift 1) ν → ν (subshift S.o)ᶜ = 0 →
      IsExactDim (ν.map S.projBar)
        ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν)) :=
  planar_feng1 h (paper_4_2_10 h)
noncomputable abbrev paper_4_2_12 := @BoxLike.planarFengLedrappierYoung_holds
noncomputable abbrev paper_4_2_13 := @BoxLike.fengLedrappierYoung_holds
noncomputable abbrev paper_4_2_14 := @BoxLike.fengLedrappierYoungBar_holds

-- PAPER_ENTRY thm:entropy_eq_gibbs
/-! 4.3 (`thm:entropy_eq_gibbs`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: The entropy-rate helpers take hdec : S.GibbsDecomposition s μ μ₁ μ₂. The paper has
rotations, a proximal diagonal generator, 0<s<2, and the equilibrium state. hdec supplies the two
Gibbs measures, ergodicity and factor decompositions. To derive hdec from the equilibrium-state
hypotheses use hfk and hfjj.

Fidelity: The existing named helpers conclude equality of entropy rates, while the printed result
uses conditional-past entropies. PastEntropy contains both bridges; the planar conull-set
condition follows from ergodicity, which follows from hdec. No hms is necessary if the primed
bridge is used. The literal endpoint dimEntropy_zero_eq_gibbs assembles both conditional-entropy
identities.

PROOF DEVIATION: The proof follows the two-to-one coding argument of the prose: block entropies
differ by at most log 2 and division by n removes this difference. The final equality with
conditional-past entropy is separately proved by chain rule, Lévy upward convergence and Cesàro in
PastEntropy.
-/
noncomputable abbrev paper_4_3_1 := @BoxLike.System.GibbsDecomposition.dimEntropy_zero_eq_gibbs
noncomputable abbrev paper_4_3_2 := @BoxLike.System.GibbsDecomposition.dimEntropy_zero_eq_gibbs
noncomputable abbrev paper_4_3_3 := @BoxLike.System.GibbsDecomposition.zero_entropy_identities
noncomputable abbrev paper_4_3_4 := @BoxLike.System.GibbsDecomposition.entropy_eq₁
noncomputable abbrev paper_4_3_5 := @BoxLike.System.GibbsDecomposition.entropy_eq₂
noncomputable abbrev paper_4_3_6 := @BoxLike.entropy_map_unCode
noncomputable abbrev paper_4_3_7 := @BoxLike.System.dimEntropy_zero_eq_entropy'
noncomputable abbrev paper_4_3_8 := @BoxLike.System.dimEntropyBar_zero_eq_entropy'

-- PAPER_ENTRY thm:eq_state_proj_dim
/-! 4.4 (`thm:eq_state_proj_dim`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: WithRotations, Proximal, ProjExpSeparation, invariant probability s-equilibrium μ
for every s>0, and an arbitrary coordinate c∈ZMod 2. For s >= 2 only WithRotations,
ProjExpSeparation and Jordan-Rapaport are used.

Fidelity: Exact double-dimensionality and the upper packing and lower Hausdorff dimension values
are proved for every s>0 (eq_state_proj_dim_all), for every s-equilibrium state.

PROOF DEVIATION: For 0<s<2 the proof follows the normalized Gibbs decomposition and exact-
dimensional mixture argument. Feng–Hu is unnecessary under separation because Jordan–Rapaport already gives
exact-dimensionality.

Proof for s >= 2: as in the prose. Lemma 3.12 gives the Bernoulli state (eq_bernoulli); the lift
(τ_*μ+ω_*μ)/2 is the stationary Markov measure of orientationLift_bernoulli_cylinder, mixing on
cylinders (tendsto_orientationLift_bernoulli_cylinder_inter) and hence ergodic
(ergodic_orientationLift_bernoulli); each word has exactly two lifts, so the entropies agree
(entropy_orientationLift); Birkhoff and Lemma 2.5 give λ_1 = λ_2 = λ̄ =
(1/2) Σ p_i log|det A_i| (lyapunov_eq_of_ergodic_orientationLift,
IsEquilibriumState.lyapunov_eq_of_two_le); Jordan-Rapaport applies to the lift, whose projection
is (ν_x+ν_y)/2 (map_projBar_orientationLift), and the differentiation step gives each marginal
(isExactDim_marginal_of_two_le). Mixing is proved by an explicit parity computation, an added
detail rather than a change of route.
-/
noncomputable abbrev paper_4_4_1 := @BoxLike.System.eq_state_proj_dim_all
noncomputable abbrev paper_4_4_2 := @BoxLike.System.eq_state_proj_dim_of_two_le
noncomputable abbrev paper_4_4_3 := @BoxLike.System.isExactDim_marginal_of_two_le
noncomputable abbrev paper_4_4_4 := @BoxLike.System.IsEquilibriumState.lyapunov_eq_of_two_le
noncomputable abbrev paper_4_4_5 := @BoxLike.System.IsEquilibriumState.ergodic_orientationLift_of_two_le
noncomputable abbrev paper_4_4_6 := @BoxLike.ergodic_orientationLift_bernoulli
noncomputable abbrev paper_4_4_7 := @BoxLike.tendsto_orientationLift_bernoulli_cylinder_inter
noncomputable abbrev paper_4_4_8 := @BoxLike.orientationLift_bernoulli_cylinder
noncomputable abbrev paper_4_4_9 := @BoxLike.entropy_orientationLift
noncomputable abbrev paper_4_4_10 := @BoxLike.System.lyapunov_eq_of_ergodic_orientationLift
noncomputable abbrev paper_4_4_11 := @BoxLike.System.map_projBar_orientationLift
noncomputable abbrev paper_4_4_12 := @BoxLike.System.eq_state_proj_dim
noncomputable abbrev paper_4_4_13 := @BoxLike.System.marginal_decomposition
noncomputable abbrev paper_4_4_14 := @BoxLike.System.marginal_decomposition_normalised

-- PAPER_ENTRY ex:projection_double_dimensional
/-! 4.5 (`ex:projection_double_dimensional`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean), used through thm:eq_state_proj_dim.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: 0<s₂<s₁≤1 only. The unique p∈(1/2,1), the translation t, the four-map System (Fin 4),
its geometry (rotations, proximality, strong separation, projective exponential separation, no
exact overlaps), P(A,u)=log(2a^u+2b^u) for 0≤u≤1, dimaff=s₁, and the existence and uniqueness of
the s₁-equilibrium state are proved; FengKaenmakiUnique is not used.

Fidelity: full statement for every 0<s₂<s₁≤1, for every invariant s₁-equilibrium state; also
records h₀=log 2+H(p), both exponents in both displayed forms, both ratios, the upper packing and
lower Hausdorff dimensions of both projections, and that each pointwise value occurs on a set of
positive measure in each projection.

Proof: as in the prose. Parameters (existsUnique_p, by monotonicity, continuity and endpoint
limits of the ratio); geometry and pressure through M(u) and the two-sided partition-sum estimate
(svfSum_le_mulVec, pressure_eq, dimaff_paramsOf); strong separation on the cube B
(strongSeparation); the volume argument at the first differing symbol with κ, C=κ/8, c=b/128
(kappa_mul_pow_le, volume_L_lt_le, volume_badSet_le, volume_iUnion_badSet_le,
exists_translation); Q_ij=M(s)_ij v_j/v_i (Gibbs.Q_apply), the labelled probabilities, the entropy
by Proposition 4.3 and the exponents by Proposition 3.14 (Gibbs.isEquilibriumState_spec); then
Theorem 4.4 (Gibbs.marginal_spec).

PROOF DEVIATION: μ₁ is identified with the Markov measure by a Bernoulli construction and a
Gibbs-uniqueness argument (cylinder comparability plus ergodicity of μ₁); the prose states the
identification. The entropy of the Markov measure is obtained by comparing block entropies with a
Bernoulli measure rather than by the Markov-chain entropy formula. Both are added detail.
-/
noncomputable abbrev paper_4_5_1 := @BoxLike.PrescribedExample.projection_double_dimensional
noncomputable abbrev paper_4_5_2 := @BoxLike.PrescribedExample.projection_double_dimensional_of_geometry
noncomputable abbrev paper_4_5_3 := @BoxLike.PrescribedExample.equilibrium_spec
noncomputable abbrev paper_4_5_4 := @BoxLike.PrescribedExample.Gibbs.isEquilibriumState_spec
noncomputable abbrev paper_4_5_5 := @BoxLike.PrescribedExample.Gibbs.isEquilibriumState_ratios
noncomputable abbrev paper_4_5_6 := @BoxLike.PrescribedExample.Gibbs.marginal_spec
noncomputable abbrev paper_4_5_7 := @BoxLike.PrescribedExample.Gibbs.GibbsDecomposition.eq_markov
noncomputable abbrev paper_4_5_8 := @BoxLike.PrescribedExample.Gibbs.markov_cylinder_eq_Q
noncomputable abbrev paper_4_5_9 := @BoxLike.PrescribedExample.exists_geometry
noncomputable abbrev paper_4_5_10 := @BoxLike.PrescribedExample.existsUnique_p
noncomputable abbrev paper_4_5_11 := @BoxLike.PrescribedExample.pressure_eq
noncomputable abbrev paper_4_5_12 := @BoxLike.PrescribedExample.exists_translation
noncomputable abbrev paper_4_5_13 := @BoxLike.PrescribedExample.volume_badSet_le

-- PAPER_ENTRY thm:gibbs_tau_omega_positive
/-! 4.6 (`thm:gibbs_tau_omega_positive`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: WithRotations, HasProximalDiagonal, 0<s<2, invariant ergodic probability equilibrium
μ, and hdec : GibbsDecomposition s μ μ₁ μ₂.

Fidelity: Both sums equal one, the four zero terms and all four strict positivity assertions
match. The implicit dependence of Σ^τ and Σ^ω on μ is explicit in Lean. hdec is an internal
constructed object; its external source is hfjj after applying hfk.

Proof: as in the prose: backward Lyapunov rates identify the full and zero pieces; the factor
decompositions and the positivity of 3.13 (`sigma_tau_omega_positive_eq_measure`, by the counting
argument and Birkhoff's theorem) give the four positive terms.
-/
noncomputable abbrev paper_4_6_1 := @BoxLike.System.gibbs_tau_omega_positive

-- PAPER_ENTRY thm:conditional_two_ways
/-! 4.7 (`thm:conditional_two_ways`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: Same normalized equilibrium/Gibbs hypotheses as 4.6, with μ₁ and μ₂ probability
instances and hdec.

Fidelity: All four conditional-measure identities agree with the manuscript. Lean uses unCode at
the point instead of the inverses restricted to their respective orientation images; these are
equal there.

Proof: as in the prose (`System.conditional_two_ways_normalised`,
BoxLike/Aligned/ConditionalTwoWays.lean, the form used by 4.8 to 4.14): normalise on the positive
pieces E, F, transport the conditional measures, and remove the restrictions by 3.2. The transport
of the unnormalised restrictions with one application of conditional-measure uniqueness
(`System.conditional_two_ways`, `condMeas_transport`) is a shorter alternative proof, which needs
no positivity.
-/
noncomputable abbrev paper_4_7_1 := @BoxLike.System.conditional_two_ways_normalised
noncomputable abbrev paper_4_7_2 := @BoxLike.System.conditional_two_ways_normalised_case
noncomputable abbrev paper_4_7_3 := @BoxLike.System.normalised_orientation_restrictions
noncomputable abbrev paper_4_7_4 := @BoxLike.condMeas_map_of_ae_mem
noncomputable abbrev paper_4_7_5 := @BoxLike.System.conditional_two_ways
noncomputable abbrev paper_4_7_6 := @BoxLike.System.conditional_two_ways_aux
noncomputable abbrev paper_4_7_7 := @BoxLike.condMeas_transport

-- PAPER_ENTRY thm:overline_h1_zero
/-! 4.8 (`thm:overline_h1_zero`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane) and BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part
of thm:feng1 from the first, BoxLike/ProjectiveLineSystem.lean); the library statements take
them as hypotheses and Solution discharges them.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: Normalized proximal box-like system with rotations, projective exponential
separation, 0<s<2, invariant ergodic equilibrium μ, entropy μ≤−λ₁, and hdec.

Fidelity: The almost-everywhere zero pointwise entropy of the average is exactly represented. The
non-strict comparison of the prose is correct.

PROOF DEVIATION: The prose and Lean compare Jordan–Rapaport with scalar Feng, then
transfer conditional information limits across the fast/slow pieces. The separate initial
invocation of Feng–Hu in the prose is unused: Jordan–Rapaport already gives exact-dimensionality.
-/
noncomputable abbrev paper_4_8_1 := @BoxLike.System.overline_h1_zero

-- PAPER_ENTRY thm:overline_h1_zero_large
/-! 4.9 (`thm:overline_h1_zero_large`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane) and BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part
of thm:feng1 from the first, BoxLike/ProjectiveLineSystem.lean); the library statements take
them as hypotheses and Solution discharges them.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: As 4.8, but only entropy μ≤−λ₂; no lower entropy bound. hdec supplies Gibbs data.

Fidelity: The Lean signature assumes entropy μ≤−λ₂ only, as the prose does. The scalar
entropy-zero conclusion and the almost-everywhere Dirac conclusion on slowPart have the full
scope of the manuscript. The latter is the manuscript's measure-equality statement in equivalent
ae form.

PROOF DEVIATION: The proof follows the scalar dimension comparison of the prose, Feng entropy-zero
criterion and conditional transport. No substantive route difference.
-/
noncomputable abbrev paper_4_9_1 := @BoxLike.System.overline_h1_zero_large

-- PAPER_ENTRY thm:overline_h1_large
/-! 4.10 (`thm:overline_h1_large`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSum (fengInfoSum_holds) and BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: Normalized system with rotations and proximal diagonal generator, 0<s<2, invariant
ergodic equilibrium μ and hdec; no separation or entropy-range condition.

Fidelity: Lean states equality barh₁(μ₁)=h₁(μ) together with the ae equality for the average on
fastPart. These two conclusions are equivalent to the displayed three-term equality.

PROOF DEVIATION: Same cylinder-preimage and information-limit proof. Lean explicitly uses
positivity of just τ(Σ^τ) to identify the two constants, whereas the prose obtains the equality
pointwise on each positive part.
-/
noncomputable abbrev paper_4_10_1 := @BoxLike.System.overline_h1_large

-- PAPER_ENTRY thm:eq_state_h1_zero
/-! 4.11 (`thm:eq_state_h1_zero`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane) and BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part
of thm:feng1 from the first, BoxLike/ProjectiveLineSystem.lean); the library statements take
them as hypotheses and Solution discharges them.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSum (fengInfoSum_holds) and BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: WithRotations, HasProximalDiagonal, ProjExpSeparation, 0<s<2, invariant ergodic
probability equilibrium μ, entropy μ≤−λ₁.

Fidelity: Both h₁=0 and the ae Dirac conditional-measure assertion are proved. The manuscript
restricts the full-measure set to Σ'; Lean's assertion is on all sequences but is equivalent
because Σ' is conull.

PROOF DEVIATION: Same proof: transport Dirac measures from the average through injective
orientation codings, cover Σ' by its two orientation parts, and use Feng's zero-entropy
equivalence.
-/
noncomputable abbrev paper_4_11_1 := @BoxLike.System.eq_state_h1_zero

-- PAPER_ENTRY thm:eq_state_h1_large
/-! 4.12 (`thm:eq_state_h1_large`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane) and BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part
of thm:feng1 from the first, BoxLike/ProjectiveLineSystem.lean); the library statements take
them as hypotheses and Solution discharges them.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSum (fengInfoSum_holds) and BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: WithRotations, HasProximalDiagonal, ProjExpSeparation, 0<s<2, invariant ergodic
probability equilibrium μ, −λ₁≤entropy μ; no upper entropy bound.

Fidelity: The formula h₁=entropy μ+λ₁ agrees with h₁=h₀+λ₁ after the conditional-past bridge. The
lower boundary is included exactly as in the statement of the manuscript.

PROOF DEVIATION: Same Jordan–Rapaport/Feng comparison and 4.10 substitution; Lean uses uniqueness
of exact dimension to equate the two expressions.
-/
noncomputable abbrev paper_4_12_1 := @BoxLike.System.eq_state_h1_large

-- PAPER_ENTRY thm:eq_state_h2_zero
/-! 4.13 (`thm:eq_state_h2_zero`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane) and BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part
of thm:feng1 from the first, BoxLike/ProjectiveLineSystem.lean); the library statements take
them as hypotheses and Solution discharges them.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSum (fengInfoSum_holds) and BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: Same hypotheses as 4.11, including entropy μ≤−λ₁.

Fidelity: The h₂=0 endpoint matches. It is implied by the stronger 4.14 and keeps its own proof
and its own numbered entry.

PROOF DEVIATION: The Lean proof follows the prose exactly: 4.11 gives Dirac ξ₁-conditionals,
refinement gives Dirac ξ₂-conditionals, then Feng's zero-entropy criterion.
-/
noncomputable abbrev paper_4_13_1 := @BoxLike.System.eq_state_h2_zero

-- PAPER_ENTRY thm:orto_partition_dirac
/-! 4.14 (`thm:orto_partition_dirac`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane) and BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part
of thm:feng1 from the first, BoxLike/ProjectiveLineSystem.lean); the library statements take
them as hypotheses and Solution discharges them.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSum (fengInfoSum_holds) and BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: Normalized system with rotations, projective exponential separation, 0<s<2,
invariant ergodic probability equilibrium μ, entropy μ≤−λ₂ only.

Fidelity: The signature assumes entropy μ≤−λ₂ only; the full entropy range of the manuscript is
proved.

PROOF DEVIATION: The proof follows the prose: slow-part Dirac conditionals transfer to ξ₁-perp; ξ₂
refines ξ₁-perp; Feng's criterion gives h₂=0.
-/
noncomputable abbrev paper_4_14_1 := @BoxLike.System.orto_partition_dirac

-- PAPER_ENTRY thm:SOSC_h2_zero
/-! 4.15 (`thm:SOSC_h2_zero`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSum (fengInfoSum_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.

Other inputs: WithRotations, Proximal, StrongOpenSet, 0<s<2, invariant ergodic probability
equilibrium μ. No projective separation and no proximal diagonal generator required.

Fidelity: The printed endpoint h₂=0 matches. The manuscript's equilibrium state is already
declared ergodic in the surrounding setup. The existing lemma explicitly takes ergodicity, which
holds for every invariant equilibrium state of a tuple with rotations, with no literature premise
(`System.IsEquilibriumState.ergodic_of_withRotations`).

Proof: the open-set and unique-future-address argument of the prose. The recurrence of the word
w (tex 3506 to 3507) comes from ergodicity through Poincaré recurrence
(`ae_frequently_iterate_mem`), as the prose invokes it.
-/
noncomputable abbrev paper_4_15_1 := @BoxLike.System.SOSC_h2_zero

-- PAPER_ENTRY thm:main_extended
/-! 4.16 (`thm:main_extended`): formalized.
Literature hypotheses: none.
Proved input: BoxLike.ShmerkinLqDimension (`shmerkinLqDimension_holds`, Shmerkin, Theorem 6.6,
proved in BoxLike/Shmerkin.lean along the source), which gives Jordan-Rapaport, Theorem 1.1
(BoxLike.JordanRapaportDimension, `jordanRapaportDimension_of_shmerkin`,
BoxLike/JordanRapaport.lean).
Proved input: BoxLike.FengLedrappierYoung (`fengLedrappierYoung_holds`, Feng, Theorems 1.2 and 1.3,
proved in BoxLike/FengLedrappierYoung.lean from the planar statement, along Feng's Sections 4 to 6
in the plane) and BoxLike.FengLedrappierYoungBar (`fengLedrappierYoungBar_holds`, the second part
of thm:feng1 from the first, BoxLike/ProjectiveLineSystem.lean); the library statements take
them as hypotheses and Solution discharges them.
Proved input: BoxLike.MorrisShmerkinLyapunov (`morrisShmerkinLyapunov_holds`, eq:simple_lyapunov,
proved in BoxLike/MorrisShmerkin.lean along Morris-Shmerkin, Lemmas 3.4 and 3.5); the library
statements take it as a hypothesis and Solution discharges it.
Proved input: BoxLike.EquilibriumGibbsStatement (`equilibriumGibbs`, the Gibbs bounds of
Proposition 3.10 for tuples with rotations, proved in BoxLike/EquilibriumGibbs.lean); the library
statements take it as a hypothesis and Solution discharges it.
Proved inputs: BoxLike.FengInfoSum (fengInfoSum_holds) and BoxLike.FengInfoSumBar (fengInfoSumBar_holds), Feng, Lemma 4.6, first identity of (4.16), proved internally along Feng's Lemmas 4.4 and 4.5;
the library statements take them as hypotheses and Solution discharges them.
Proved input: BoxLike.FraserJordanJurgaDecomposition (`fraserJordanJurgaDecomposition_holds`, Proposition 3.14,
proved in BoxLike/FraserJordanJurga/); the library statements take it as a hypothesis and Solution
discharges it.

Other inputs: WithRotations, Proximal, ProjExpSeparation, invariant probability equilibrium μ at
s=dimaff, and entropy μ≤−λ₂ or StrongOpenSet. There is no s<2 restriction in the assembled
endpoint.

Fidelity: The full all-s exact-dimensionality statement is represented. Positivity of s
follows from rotations. For s≥2 the entropy alternative is impossible and the SOSC volume argument
yields exact dimension 2. The ge-two helper needs no external literature hypotheses, rotations,
proximality or projective separation. Rossi's bound `eq:hausdorff_ergodic_lyapunov`, which the
paper states before the theorem, is proved (`System.rossiBound`, `prose_rossi_0` below); the
proof does not use it.

PROOF DEVIATION: For s<2, the Lean proof follows normalization, the two entropy regimes, the SOSC
case and evaluation of Feng's formula.

PROOF DEVIATION: For s≥2, Lean identifies the equilibrium state as Bernoulli directly from
equality in entropy/Gibbs inequalities, rather than citing 3.12. It proves stationarity uniqueness
internally rather than assuming Hutchinson's theorem. The mathematical argument otherwise agrees.
-/
noncomputable abbrev paper_4_16_1 := @BoxLike.System.main_extended_min
noncomputable abbrev paper_4_16_2 := @BoxLike.System.main_extended
noncomputable abbrev paper_4_16_3 := @BoxLike.System.main_extended_normalised
noncomputable abbrev paper_4_16_4 := @BoxLike.System.main_extended_ge_two

/-! ## Unnumbered claims

Rossi's bound `eq:hausdorff_ergodic_lyapunov` (tex lines 2728 to 2731): for every ergodic
μ ∈ M_σ(Σ), \overline{dim}_H(π_*μ) ≤ min{2, dimL(𝖠, μ)}. The paper cites Rossi, J. Math. Anal.
Appl. 413 (2014), Theorem 2.2, as motivation before thm:main_extended; no proof of a numbered
result uses it.
Literature hypotheses: none.

Fidelity: the statement `System.RossiBound` (BoxLike/DimensionFormula.lean), for every box-like
system and every ergodic invariant probability measure, holds (`System.rossiBound`). Equality
holds for the equilibrium state of thm:main_extended (`System.upperHausdorffDim_map_proj_eq`).

Proof: a covering argument (BoxLike/Rossi.lean). For t ≤ 2 with h_0(μ) + Λ(𝖠, μ, t) < 0, the
Shannon-McMillan-Breiman theorem and the Furstenberg-Kesten limits along the forward products
(`System.ae_tendsto_log_norm_matWord`, `System.ae_tendsto_log_alpha₂_matWord`) bound the number
of typical words of length n and the sides of the rectangles that contain their copies of X;
covering the rectangles by squares gives a Borel set of full π_*μ-measure and Hausdorff dimension
at most t (`System.exists_dimH_le_of_add_energy_neg`), and the mass distribution principle bounds
the lower pointwise dimension by t almost everywhere (`ae_lowerLocalDim_le_of_dimH_le`,
`System.ae_lowerLocalDim_map_proj_le`, `System.essSup_lowerLocalDim_map_proj_le`).
-/
/-- Rossi's bound `eq:hausdorff_ergodic_lyapunov` holds for every box-like system. -/
theorem prose_rossi_0 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : BoxLike.System ι) : S.RossiBound :=
  S.rossiBound
noncomputable abbrev prose_rossi_1 := @BoxLike.System.RossiBound
noncomputable abbrev prose_rossi_2 := @BoxLike.System.ae_lowerLocalDim_map_proj_le
noncomputable abbrev prose_rossi_3 := @BoxLike.System.essSup_lowerLocalDim_map_proj_le
noncomputable abbrev prose_rossi_4 := @BoxLike.System.exists_dimH_le_of_add_energy_neg
noncomputable abbrev prose_rossi_5 := @BoxLike.System.ae_tendsto_log_norm_matWord
noncomputable abbrev prose_rossi_6 := @BoxLike.System.ae_tendsto_log_alpha₂_matWord
noncomputable abbrev prose_rossi_7 := @BoxLike.ae_lowerLocalDim_le_of_dimH_le
noncomputable abbrev prose_rossi_8 := @BoxLike.System.upperHausdorffDim_map_proj_eq

/-! The squeeze of the modified affinity dimension (tex lines 548 to 550): if
\dim_H X = dimaff(X), then dimmaff(X) = dimaff(X).
Literature hypotheses: none.
Proved input: BoxLike.System.FraserBound (`System.fraserBound_holds`, the first part of
thm:fraser); the library statements `System.dimmaff_eq_dimaff`,
`System.dimmaff_eq_dimaff_noExactOverlaps` and `System.dimmaff_eq_dimaff_main2` take it as a
hypothesis, and `prose_squeeze_0` discharges it for the first.

Fidelity: the squeeze for every box-like system with \dim_H X = dimaff(X) (`prose_squeeze_0`);
the hypotheses of thm:main2 give \dim_H X = dimaff(X) (`System.main2_prose`, and
`Challenge.audit_main2` for the challenge statement).
-/
/-- The squeeze of tex lines 548 to 550, with no literature premise: if `\dim_H X = dimaff(X)`,
then `dimmaff(X) = dimaff(X)`. The first part of `thm:fraser` is `System.fraserBound_holds`. -/
theorem prose_squeeze_0 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι)
    (hH : dimH S.attractor = ENNReal.ofReal S.dimaff) : S.dimmaff = S.dimaff :=
  S.dimmaff_eq_dimaff S.fraserBound_holds hH

end Solution.Paper
