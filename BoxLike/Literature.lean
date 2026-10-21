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
  Jordan–Rapaport, Proc. Lond. Math. Soc. (3) 122 (2021), Theorem 1.1. The library proves it
  from `ShmerkinLqDimension` along the source's own argument
  (`jordanRapaportDimension_of_shmerkin` in `BoxLike/JordanRapaport.lean`).
* `KittleKoglerDimension`: the dimension of self-similar measures on the line without exact
  overlaps, from Kittle–Kogler, arXiv:2610.10511, Theorem 1.1, used in the proof of `thm:main2`.
  The library proves it (`kittleKoglerDimension_holds` in `BoxLike/KittleKogler.lean`), from the
  Lean formalisation of the source by its authors, the library `ExactOverlaps` in `vendor/`.
* `ShmerkinStopping`, `ShmerkinExpSeparation`, `ShmerkinLqDimension`: Shmerkin's family `Ω_M`,
  his exponential separation (Definition 6.5) and the lower bound of his Theorem 6.6 on the
  `L^q` dimension of self-similar measures on the line, Ann. of Math. (2) 189 (2019), numbering
  of arXiv:1609.07802v3, the input of Jordan–Rapaport's proof and so of `thm:main1` and
  `thm:main_extended`. Authorised by the project owner on 2026-10-21. The library proves it
  (`shmerkinLqDimension_holds` in `BoxLike/Shmerkin.lean`, along the source).

Falconer's bound `eq:hausdorff_affinity_upper_bound`, which the article cites, is a theorem of
the library (`System.dimH_attractor_le` in `BoxLike/FalconerBound.lean`).

The statements were compared with the sources on 2026-09-20, Shmerkin's on 2026-10-21;
`docs/correspondence.md`, "Fidelity boundary",
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
the definition of exact-dimensionality. The library proves the statement from
`ShmerkinLqDimension` (`jordanRapaportDimension_of_shmerkin` in `BoxLike/JordanRapaport.lean`),
along Section 2 of the source. -/
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
the self-similar measure, by Hutchinson's uniqueness. The library proves the statement
(`kittleKoglerDimension_holds` in `BoxLike/KittleKogler.lean`), from the Lean formalisation of the
source by its authors, the library `ExactOverlaps` in `vendor/`: its Theorem 1.1 gives the lower
Hausdorff dimension `min{1, h_μ / |χ_μ|}` of every stationary measure, its exact-dimensionality
theorem the pointwise form, and its entropy identity `h_μ = H(p)` without exact overlaps the form
stated here. -/
def KittleKoglerDimension : Prop :=
  ∀ {κ : Type u} [Fintype κ] (r t p : κ → ℝ), (∀ j, r j ≠ 0) → (∀ j, |r j| < 1) →
    (∀ j, 0 < p j) → ∑ j, p j = 1 → Function.Injective (simWord r t) →
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
    ν = ∑ j, ENNReal.ofReal (p j) • ν.map (fun x => r j * x + t j) →
    IsExactDim ν (min 1 ((∑ j, Real.negMulLog (p j)) / -(∑ j, p j * Real.log |r j|)))

/-- The word `u` belongs to Shmerkin's family `Ω_M` of the IFS with ratios `r`: it is non-empty,
`|λ_u| ≤ 2^{-M}` and `|λ_{u^-}| > 2^{-M}`, where `λ_u` is the product of the ratios along `u`
and `u^-` is `u` without its last symbol (Shmerkin, arXiv:1609.07802v3, Section 6.4). -/
def ShmerkinStopping {κ : Type*} (r : κ → ℝ) (M : ℕ) (u : List κ) : Prop :=
  u ≠ [] ∧ |(u.map r).prod| ≤ (2 : ℝ) ^ (-(M : ℝ)) ∧
    (2 : ℝ) ^ (-(M : ℝ)) < |(u.dropLast.map r).prod|

/-- Shmerkin's exponential separation, Definition 6.5 of arXiv:1609.07802v3: there are `R > 0`
and infinitely many `M` with `d(f_u, f_v) ≥ 2^{-R M}` for all distinct `u, v ∈ Ω_M`, where
`d(f_u, f_v) = |f_u(0) - f_v(0)|` if `f_u` and `f_v` have the same ratio and `d = 1` otherwise.
Since `2^{-R M} ≤ 1`, only pairs with equal ratios carry a condition. Here `f_u = simWord r t u`
is `f_{u_1} ∘ ⋯ ∘ f_{u_k}`, as in the source. -/
def ShmerkinExpSeparation {κ : Type*} (r t : κ → ℝ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ᶠ M : ℕ in Filter.atTop, ∀ u v : List κ, u ≠ v →
    ShmerkinStopping r M u → ShmerkinStopping r M v → (u.map r).prod = (v.map r).prod →
    (2 : ℝ) ^ (-(R * M)) ≤ |simWord r t u 0 - simWord r t v 0|

/-- Shmerkin, *On Furstenberg's intersection conjecture, self-similar measures, and the `L^q`
norms of convolutions*, Ann. of Math. (2) 189 (2019), Theorem 6.6 (numbering of
arXiv:1609.07802v3), the lower bound for the `L^q` dimension, in the form the proof of
Jordan–Rapaport, Theorem 1.1, uses (their Lemma 2.3).

Source. Let `f_j(x) = r_j x + t_j`, `0 < |r_j| < 1`, be a finite IFS on the line with exponential
separation (Definition 6.5, `ShmerkinExpSeparation`) and `μ = ∑_j p_j f_j μ` the self-similar
measure of a probability vector `p`. Then `D(μ, q) = min{τ̃(q)/(q - 1), 1}` for every `q > 1`,
where `τ̃(q)` is the unique solution of `∑_j p_j^q |r_j|^{-τ̃} = 1`, and where, by Definition 1.6,
`D(μ, q) = τ(μ, q)/(q - 1)` with `τ(μ, q) = liminf_M -log_2 ∑_{I ∈ 𝒟_M} μ(I)^q / M` over the
dyadic intervals `𝒟_M = {[k 2^{-M}, (k+1) 2^{-M}) : k ∈ ℤ}`. The source writes the proof for
positive ratios and states that the general case needs only notational changes; its
Definition 6.5 and Theorem 6.6 are stated for ratios of either sign.

The statement. Since `τ ↦ ∑_j p_j^q |r_j|^{-τ}` is strictly increasing, `α < τ̃(q)/(q - 1)` is
`∑_j p_j^q |r_j|^{-(q-1)α} < 1`, and for `α < min{τ̃(q)/(q - 1), 1}` the lower bound
`α < D(μ, q)` gives `∑_{I ∈ 𝒟_M} μ(I)^q ≤ 2^{-M(q-1)α}` for all large `M`, hence the same bound
for every finite family of dyadic intervals. The statement is this consequence of the source:
the lower bound only, for every finite family, with the weights `p_j > 0`.

Degenerate instances, by hand. One map `x ↦ x/2`, `μ = δ_0`: the family `Ω_M` has one word, so
exponential separation holds with every `R`; `τ̃(q) = 0`, so the statement speaks only for
`α < 0`, where `2^{-M(q-1)α} ≥ 1 ≥ μ(I)^q`. The two maps `x ↦ x/2`, `x ↦ x/2 + 1/2` with
`p = (1/2, 1/2)`, `μ` Lebesgue measure on `[0, 1]`: the words of length `M` have the distinct
values `k 2^{-M}`, so exponential separation holds with `R = 1`; `τ̃(q) = q - 1`, and
`∑_{I ∈ 𝒟_M} μ(I)^q = 2^{-M(q-1)} ≤ 2^{-M(q-1)α}` for every `α < 1`. The map `x ↦ x/2`
repeated twice: distinct words of equal length have equal maps, so exponential separation
fails and the statement is silent.

Proved by `shmerkinLqDimension_holds` (`BoxLike/Shmerkin.lean`) along the source, with Bourgain's
structure theorem (Shmerkin's Theorem 3.1) in a weak form whose doubling exponent is some
`ε(T) > 0`. Used by: `jordanRapaportDimension_of_shmerkin` (`BoxLike/JordanRapaport.lean`), and
through it `Challenge.audit_main1` and `Challenge.audit_main_extended`. -/
def ShmerkinLqDimension : Prop :=
  ∀ {κ : Type u} [Fintype κ] (r t p : κ → ℝ), (∀ j, r j ≠ 0) → (∀ j, |r j| < 1) →
    (∀ j, 0 < p j) → ∑ j, p j = 1 → ShmerkinExpSeparation r t →
    ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    μ = ∑ j, ENNReal.ofReal (p j) • μ.map (fun x => r j * x + t j) →
    ∀ q : ℝ, 1 < q → ∀ α : ℝ, α < 1 → ∑ j, p j ^ q * |r j| ^ (-((q - 1) * α)) < 1 →
    ∀ᶠ M : ℕ in Filter.atTop, ∀ s : Finset ℤ,
      ∑ k ∈ s, (μ.real (Set.Ico ((k : ℝ) / 2 ^ M) ((k + 1) / 2 ^ M))) ^ q ≤
        (2 : ℝ) ^ (-((M : ℝ) * ((q - 1) * α)))

end BoxLike
