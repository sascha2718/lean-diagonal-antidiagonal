/-
The literature theorems of the main line that the article cites without proof, as axioms.
`BoxLike/LiteratureFeng.lean` holds the results of Feng, and `BoxLike/LiteratureRemarks.lean`
the axioms that no main result depends on. `PLAN.md`, "Fidelity boundary", states the rules: every
axiom is a statement about defined objects, carries the hypotheses under which the article
uses the cited result, and is listed by name in the comparator whitelist.

Standing conventions: `μ` is a Borel probability measure on `Σ = ℤ → ι`, invariant under the
left shift `shift 1`; the alphabet `ι` is finite with the discrete `σ`-algebra.

* `morrisShmerkin_lyapunov_lt`: `eq:simple_lyapunov` in the normalised case, from
  Morris–Shmerkin, Trans. Amer. Math. Soc. 371 (2019), Theorem 3.1, which combines their
  Proposition 3.3 and Lemmas 3.4 and 3.5 (numbering of arXiv:1602.08789v3).
* `fengKaenmaki_gibbs`: the Gibbs bounds of `thm:irred_eq_state`, from Feng–Käenmäki, Discrete
  Contin. Dyn. Syst. 30 (2011), Proposition 1.2, applied with `q = s` for `0 < s ≤ 1` and to a
  rescaled tuple with `q = 2 - s` for `1 < s < 2`.
* `fraserJordanJurga_decomposition`: `thm:eq_state_is_sum`, from Fraser–Jordan–Jurga,
  J. Fractal Geom. 7 (2020), Lemma 1.3 and Corollaries 1.5 and 1.6, together with the existence
  of ergodic Gibbs measures on a mixing sub-shift of finite type (Bowen).
* `jordanRapaport_dimension`: the dimension formula used in `eq:gibbs_proj_dim`, from
  Jordan–Rapaport, Proc. Lond. Math. Soc. (3) 122 (2021), Theorem 1.1.

Falconer's bound `eq:hausdorff_affinity_upper_bound`, which the article cites, is a theorem of
the library (`System.dimH_attractor_le` in `BoxLike/FalconerBound.lean`).

The statements were compared with the sources on 2026-09-20; `PLAN.md`, "Fidelity boundary",
records the reductions between each source and its axiom.

Every axiom lists its instance arguments in its own signature. Lean omits from an `axiom` the
section variables that its statement does not mention, and the cited theorems concern the
discrete `σ`-algebra on the alphabet, which is the instance `MeasurableSingletonClass ι`.
`BoxLike/AxCheck.lean` checks that each axiom takes this argument.
-/
import BoxLike.AffinityDim
import BoxLike.MeasureDim
import BoxLike.Proximal
import BoxLike.Thermodynamic
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace BoxLike

open MeasureTheory

/-- `eq:simple_lyapunov` for the normalised tuple. Morris–Shmerkin, Theorem 3.1: if
`A_1, …, A_M ∈ GL_2(ℝ)` have no common invariant line and one of them is hyperbolic, then for
`0 < s < 2` every equilibrium state of `φ^s` has unequal Lyapunov exponents. A diagonal
generator with `|a_i| ≠ |b_i|` is hyperbolic, and together with an anti-diagonal generator it
makes the tuple irreducible. The source works on the one-sided shift with the products
`A_{x_n} ⋯ A_{x_1}`; it applies to the transposed tuple, which has the same norms of products,
the same pressure and the same equilibrium states. -/
axiom morrisShmerkin_lyapunov_lt {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hrot : S.WithRotations)
    (hprox : S.HasProximalDiagonal) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : S.lyapunov₂ μ < S.lyapunov₁ μ

/-- The Gibbs bounds of `thm:irred_eq_state`. Feng–Käenmäki, Proposition 1.2: if a tuple of
real matrices has no common invariant proper subspace, then for each `q > 0` the
`q`-equilibrium state of the potential `‖·‖^q` satisfies
`C⁻¹ exp(-|𝐢| P(q)) ‖A_𝐢‖^q ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(q)) ‖A_𝐢‖^q`. For `0 < s ≤ 1` the singular
value function is `‖·‖^s` and `q = s`. For `1 < s < 2` and planar matrices
`φ^s(A) = |det A|^{s-1} ‖A‖^{2-s} = ‖A'‖^{2-s}` with the rescaled tuple
`A'_i = |det A_i|^{(s-1)/(2-s)} A_i`, which is irreducible when `𝖠` is, so the proposition
applies with `q = 2 - s`. The article states `thm:irred_eq_state` for every `s > 0`, with
uniqueness and ergodicity; the axiom covers the range `0 < s < 2` and the Gibbs bounds, which
is what `thm:main1` uses. -/
axiom fengKaenmaki_gibbs {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hirr : S.Irreducible) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    S.HasGibbsBounds s μ

/-- `thm:eq_state_is_sum`. Fraser–Jordan–Jurga, Lemma 1.3 and Corollaries 1.5 and 1.6: for a
box-like tuple with rotations containing a proximal diagonal generator and `0 < s < 2`, the
invariant measure `μ` with the Gibbs bounds of `thm:irred_eq_state` is the sum of the
push-forwards of the restrictions of the two ergodic `s`-Gibbs measures `μ_1`, `μ_2` on `Σ_Z`,
in each of the four ways of `thm:eq_state_is_sum`, and `λ_1(𝖠, μ) = \overline{λ}(𝖠, μ_1)`,
`λ_2(𝖠, μ) = \overline{λ}(𝖠, μ_2)`. No separation condition is assumed. The axiom includes
the existence of the ergodic Gibbs measures on the mixing sub-shift `Σ_Z`. The source assumes
non-negative entries on the one-sided shift and states the first decomposition; all
quantities here depend on the entries through their moduli, and the other three
decompositions follow from the symmetry exchanging the two axes. The identity
`P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` of the proposition is not part of the axiom. -/
axiom fraserJordanJurga_decomposition {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hrot : S.WithRotations)
    (hprox : S.HasProximalDiagonal) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (hgibbs : S.HasGibbsBounds s μ) :
    ∃ μ₁ μ₂ : Measure (ℤ → ι × ZMod 2), S.GibbsDecomposition s μ μ₁ μ₂

/-- Jordan–Rapaport, Theorem 1.1, for the projective system `Ψ`: if the self-similar system
`Ψ = (g_j)` on `ℝ`, with ratios `0 < |r_j| < 1` of either sign, is exponentially separated,
which for `Ψ` is the projective exponential separation condition, and `ν` is an ergodic
shift-invariant probability measure, then `\overline{π}_*ν` is exact-dimensional with
`dim(\overline{π}_*ν) = min{1, -\overline{h}_0(ν) / \overline{λ}(𝖠, ν)}`. The source works on
the one-sided shift, with the Lyapunov exponent `∑_j ν[j] log |r_j|` and closed intervals in
the definition of exact-dimensionality. -/
axiom jordanRapaport_dimension {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hsep : S.ProjExpSeparation)
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν) :
    IsExactDim (ν.map S.projBar) (min 1 (-entropy ν / S.lyapBar ν))

end BoxLike
