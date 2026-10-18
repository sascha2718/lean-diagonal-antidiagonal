module

/-
The literature theorems of the main line that the article cites without proof, as `Prop`-valued
definitions. A result that uses one of them takes it as a hypothesis. `BoxLike/LiteratureFeng.lean`
holds the results of Feng, and `BoxLike/LiteratureRemarks.lean` the citations that no main result
depends on. `docs/correspondence.md`, "Fidelity boundary", states the rules: every citation is a statement about
defined objects and carries the hypotheses under which the article uses the cited result.

Standing conventions: `μ` is a Borel probability measure on `Σ = ℤ → ι`, invariant under the
left shift `shift 1`; the alphabet `ι` is finite with the discrete `σ`-algebra.

* `MorrisShmerkinLyapunov`: `eq:simple_lyapunov` in the normalised case, from
  Morris–Shmerkin, Trans. Amer. Math. Soc. 371 (2019), Theorem 3.1, which combines their
  Proposition 3.3 and Lemmas 3.4 and 3.5 (numbering of arXiv:1602.08789v3). The library proves
  it (`morrisShmerkinLyapunov_holds` in `BoxLike/MorrisShmerkin.lean`).
* `FengKaenmakiGibbs`: the Gibbs bounds of `thm:irred_eq_state`, from Feng–Käenmäki, Discrete
  Contin. Dyn. Syst. 30 (2011), Proposition 1.2, applied with `q = s` for `0 < s ≤ 1` and to a
  rescaled tuple with `q = 2 - s` for `1 < s < 2`. The library proves it
  (`fengKaenmakiGibbs_holds` in `BoxLike/QuasiMultiplicative/Main.lean`), and the conclusion for
  tuples with rotations, which need not be irreducible (`equilibriumGibbs` in
  `BoxLike/EquilibriumGibbs.lean`); the main line takes that statement,
  `EquilibriumGibbsStatement`, and results stated for irreducible tuples take
  `FengKaenmakiGibbs`.
* `FraserJordanJurgaDecomposition`: `thm:eq_state_is_sum`, from Fraser–Jordan–Jurga,
  J. Fractal Geom. 7 (2020), Lemma 1.3 and Corollaries 1.5 and 1.6, together with the existence
  of ergodic Gibbs measures on a mixing sub-shift of finite type (Bowen). The library proves it
  (`fraserJordanJurgaDecomposition_holds` in `BoxLike/FraserJordanJurga/Main.lean`).
* `JordanRapaportDimension`: the dimension formula used in `eq:gibbs_proj_dim`, from
  Jordan–Rapaport, Proc. Lond. Math. Soc. (3) 122 (2021), Theorem 1.1.
* `KittleKoglerDimension`: the dimension of self-similar measures on the line without exact
  overlaps, from Kittle–Kogler, arXiv:2610.10511, Theorem 1.1, used in the proof of `thm:main2`.

Falconer's bound `eq:hausdorff_affinity_upper_bound`, which the article cites, is a theorem of
the library (`System.dimH_attractor_le` in `BoxLike/FalconerBound.lean`).

The statements were compared with the sources on 2026-09-20; `docs/correspondence.md`, "Fidelity boundary",
records the reductions between each source and its statement.

Each statement quantifies over every finite alphabet `ι : Type u` with the discrete
`σ`-algebra, the instance `MeasurableSingletonClass ι`, as the cited theorems do.
-/
public import BoxLike.AffinityDim
public import BoxLike.MeasureDim
public import BoxLike.Proximal
public import BoxLike.Thermodynamic
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- `eq:simple_lyapunov` for the normalised tuple. Morris–Shmerkin, Theorem 3.1: if
`A_1, …, A_M ∈ GL_2(ℝ)` have no common invariant line and one of them is hyperbolic, then for
`0 < s < 2` every equilibrium state of `φ^s` has unequal Lyapunov exponents. A diagonal
generator with `|a_i| ≠ |b_i|` is hyperbolic, and together with an anti-diagonal generator it
makes the tuple irreducible. The source works on the one-sided shift with the products
`A_{x_n} ⋯ A_{x_1}`; it applies to the transposed tuple, which has the same norms of products,
the same pressure and the same equilibrium states. The library proves the statement
(`morrisShmerkinLyapunov_holds`), along Morris–Shmerkin's Lemmas 3.4 and 3.5 with the Gibbs
bounds of `equilibriumGibbs`. -/
def MorrisShmerkinLyapunov : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.HasProximalDiagonal → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.IsEquilibriumState s μ → S.lyapunov₂ μ < S.lyapunov₁ μ

/-- The Gibbs bounds of `thm:irred_eq_state`. Feng–Käenmäki, Proposition 1.2: if a tuple of
real matrices has no common invariant proper subspace, then for each `q > 0` the
`q`-equilibrium state of the potential `‖·‖^q` satisfies
`C⁻¹ exp(-|𝐢| P(q)) ‖A_𝐢‖^q ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(q)) ‖A_𝐢‖^q`. For `0 < s ≤ 1` the singular
value function is `‖·‖^s` and `q = s`. For `1 < s < 2` and planar matrices
`φ^s(A) = |det A|^{s-1} ‖A‖^{2-s} = ‖A'‖^{2-s}` with the rescaled tuple
`A'_i = |det A_i|^{(s-1)/(2-s)} A_i`, which is irreducible when `𝖠` is, so the proposition
applies with `q = 2 - s`. The article states `thm:irred_eq_state` for every `s > 0`, with
uniqueness and ergodicity; the statement covers the range `0 < s < 2` and the Gibbs bounds. The
library proves the statement (`fengKaenmakiGibbs_holds` in
`BoxLike/QuasiMultiplicative/Main.lean`), and its conclusion for tuples with rotations, which
need not be irreducible (`System.IsEquilibriumState.hasGibbsBounds_of_withRotations`,
`equilibriumGibbs`); the main line takes that statement, `EquilibriumGibbsStatement`, and results
stated for irreducible tuples take `FengKaenmakiGibbs`. -/
def FengKaenmakiGibbs : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.Irreducible → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.IsEquilibriumState s μ → S.HasGibbsBounds s μ

/-- `thm:eq_state_is_sum`. Fraser–Jordan–Jurga, Lemma 1.3 and Corollaries 1.5 and 1.6: for a
box-like tuple with rotations containing a proximal diagonal generator and `0 < s < 2`, the
invariant measure `μ` with the Gibbs bounds of `thm:irred_eq_state` is the sum of the
push-forwards of the restrictions of the two ergodic `s`-Gibbs measures `μ_1`, `μ_2` on `Σ_Z`,
in each of the four ways of `thm:eq_state_is_sum`, and `λ_1(𝖠, μ) = \overline{λ}(𝖠, μ_1)`,
`λ_2(𝖠, μ) = \overline{λ}(𝖠, μ_2)`. No separation condition is assumed. The statement includes
the existence of the ergodic Gibbs measures on the mixing sub-shift `Σ_Z`. The source assumes
non-negative entries on the one-sided shift and states the first decomposition; all
quantities here depend on the entries through their moduli, and the other three
decompositions follow from the symmetry exchanging the two axes. The identity
`P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` of the proposition is not part of the statement. The
library proves the statement (`fraserJordanJurgaDecomposition_holds`). -/
def FraserJordanJurgaDecomposition : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.HasProximalDiagonal → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.HasGibbsBounds s μ → ∃ μ₁ μ₂ : Measure (ℤ → ι × ZMod 2), S.GibbsDecomposition s μ μ₁ μ₂

/-- Jordan–Rapaport, Theorem 1.1, for the projective system `Ψ`: if the self-similar system
`Ψ = (g_j)` on `ℝ`, with ratios `0 < |r_j| < 1` of either sign, is exponentially separated,
which for `Ψ` is the projective exponential separation condition, and `ν` is an ergodic
shift-invariant probability measure, then `\overline{π}_*ν` is exact-dimensional with
`dim(\overline{π}_*ν) = min{1, -\overline{h}_0(ν) / \overline{λ}(𝖠, ν)}`. The source works on
the one-sided shift, with the Lyapunov exponent `∑_j ν[j] log |r_j|` and closed intervals in
the definition of exact-dimensionality. -/
def JordanRapaportDimension : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.ProjExpSeparation → ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    Ergodic (shift 1) ν → IsExactDim (ν.map S.projBar) (min 1 (-entropy ν / S.lyapBar ν))

/-- Kittle–Kogler, *The exact overlaps conjecture for self-similar measures on the real line*,
arXiv:2610.10511 (7 October 2026), Theorem 1.1, in the form the article uses in the proof of
`thm:main2` (tex lines 3702 to 3712). The source: let `μ = ∑_j p_j δ_{g_j}` be a probability
measure on finitely many distinct contracting similarities `g_j(x) = r_j x + t_j` of `ℝ`, with
`0 < |r_j| < 1` of either sign and `p_j > 0`; then the self-similar measure `ν`, the unique
probability measure with `∑_j p_j (g_j)_* ν = ν`, satisfies `dim ν = min{1, h_μ / |χ_μ|}`,
where `h_μ = lim_n H(μ^{*n}) / n` is the random walk entropy and `χ_μ = ∑_j p_j log |r_j|` the
Lyapunov exponent. The source records that `ν` is exact-dimensional, so that `dim ν` is its
exact dimension with closed intervals, and that `h_μ = H(p) = -∑_j p_j log p_j` when the
similarities generate a free semigroup, that is, when there are no exact overlaps. The statement
takes the latter hypothesis and the conclusion `dim ν = min{1, H(p) / |χ_μ|}`, which is the
exact overlaps conjecture the source proves. Every solution `ν` of the stationarity equation is
the self-similar measure, by Hutchinson's uniqueness. -/
def KittleKoglerDimension : Prop :=
  ∀ {κ : Type u} [Fintype κ] (r t p : κ → ℝ), (∀ j, r j ≠ 0) → (∀ j, |r j| < 1) →
    (∀ j, 0 < p j) → ∑ j, p j = 1 → Function.Injective (simWord r t) →
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
    ν = ∑ j, ENNReal.ofReal (p j) • ν.map (fun x => r j * x + t j) →
    IsExactDim ν (min 1 ((∑ j, Real.negMulLog (p j)) / -(∑ j, p j * Real.log |r j|)))

end BoxLike
