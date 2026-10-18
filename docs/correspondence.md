# Correspondence with the manuscript

The review covers all 41 numbered theorem-like environments, including the example and the open
question. [Solution.lean](../Solution.lean) has one `PAPER_ENTRY` for each, containing checked
references, the named literature inputs, the other hypotheses, scope limits and proof deviations.
The assessment is **39 formalised, 1 cited and 1 open question**. The cited entry is Theorem 4.2
(Feng), stated for every planar self-affine set from the authorised premise
`PlanarFengLedrappierYoung`; its second part, the scalar formula `FengLedrappierYoungBar`, follows
from the first (`fengLedrappierYoungBar_of_fengLedrappierYoung`). Theorem 1.1 (Fraser) is proved
along Fraser's proof with no literature premise (`System.fraserBound_holds`,
`System.fraserROSC_holds`), and so is Proposition 3.14 (Fraser–Jordan–Jurga,
`fraserJordanJurgaDecomposition_holds`). Proposition 3.10 is proved with no literature premise for
every irreducible tuple in `GL_2(ℝ)^N`, from `FengKaenmakiNormEquilibrium`, Feng–Käenmäki's
Proposition 1.2 in the form of the source, which the library proves
(`fengKaenmakiNormEquilibrium_holds`), and for every box-like tuple with rotations
(`System.irred_eq_state_of_withRotations`); the latter gives the Gibbs bounds of the equilibrium
state that 3.14 starts from (`equilibriumGibbs`). `eq:simple_lyapunov`, which the manuscript takes
from Morris–Shmerkin, is proved along their Lemmas 3.4 and 3.5 (`morrisShmerkinLyapunov_holds`), and
Rossi's bound `eq:hausdorff_ergodic_lyapunov` by a covering argument (`System.rossiBound`). Question
1.4 is recorded as a proposition with no answer claimed. With the 45 fingerprinted prose spans the
manifest [paper-correspondence.yaml](../paper-correspondence.yaml) reads 83 formalised, 2 cited and
1 intentionally unformalised, with 6 literature hypotheses. Every numbered statement except the open
question is therefore formalised or cited, and no result rests on an unauthorised premise.

## The three headline statements

`Challenge.lean` imports Mathlib alone and contains exactly the three headline statements and
their holes: `Challenge.audit_main1` (Theorem 1.2), `Challenge.audit_main2` (Theorem 1.3) and
`Challenge.audit_main_extended` (Theorem 4.16). Its 62 definitions are exactly those needed by
these types and their literature hypotheses, and its definition block is identical to
`Solution/Definitions.lean`. Solution proves all three for the full parameter range of the
manuscript and for every invariant equilibrium state. The library and Solution contain no
`sorry` and declare no axiom; the only kernel axioms are `propext`, `Classical.choice` and
`Quot.sound`.

| Headline | Proof | Literature inputs |
|---|---|---|
| 1.2 `audit_main1` | `System.main1_dimaff_all`: below two by the Gibbs decomposition, from two on by the orientation lift of `thm:eq_state_proj_dim` | `JordanRapaportDimension` |
| 1.3 `audit_main2` | `System.main2_prose`, along the prose: typical words by the Shannon–McMillan–Breiman theorem, diagonal subsystems, Kittle–Kogler and Feng's formula | `FengLedrappierYoung`, `KittleKoglerDimension` |
| 4.16 `audit_main_extended` | `System.main_extended_min`, with `FengLedrappierYoungBar` from `fengLedrappierYoungBar_of_fengLedrappierYoung` | `JordanRapaportDimension`, `FengLedrappierYoung` |

Feng's information-sum identity is a theorem of the library (`fengInfoSum_holds`,
`fengInfoSumBar_holds`); the library statements that take `FengInfoSum` or `FengInfoSumBar` as a
hypothesis receive these proofs in Solution, and no headline takes them. The same holds for the
decomposition of `thm:eq_state_is_sum`, `FraserJordanJurgaDecomposition`, a theorem of the
library (`fraserJordanJurgaDecomposition_holds`, `BoxLike/FraserJordanJurga/`), and for the two
inputs the manuscript takes from Feng–Käenmäki and Morris–Shmerkin: `EquilibriumGibbsStatement`,
the Gibbs bounds of every invariant equilibrium state of a box-like tuple with rotations, is the
theorem `equilibriumGibbs` (`BoxLike/EquilibriumGibbs.lean`), and `MorrisShmerkinLyapunov` is the
theorem `morrisShmerkinLyapunov_holds` (`BoxLike/MorrisShmerkin.lean`). The
Shannon–McMillan–Breiman theorem used by `audit_main2` is the library theorem
`shannonMcMillanBreiman`. Feng's scalar Ledrappier–Young formula `FengLedrappierYoungBar`, which
the main line of 4.16 takes, follows from `FengLedrappierYoung` applied to the planar system
`z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` of the projective system, whose attractor lies on the
horizontal axis (`fengLedrappierYoungBar_of_fengLedrappierYoung`,
`BoxLike/ProjectiveLineSystem.lean`); Solution passes this proof, and no headline takes it.

## Verification of this review

The results are those of the current tree.

- `lake build BoxLike Challenge Solution` passes; the only warnings are the three intentional
  `sorry` holes of `Challenge.lean`.
- `./comparator-audit.sh --local-unsandboxed` passes for the three headlines
  `Challenge.audit_main1`, `Challenge.audit_main2` and `Challenge.audit_main_extended`: con-ron
  accepts 55,136 declarations, and nanoda and the Lean kernel accept. This is a local macOS
  development run without the Linux sandbox, not a Palomar verdict.
- `lake env lean tools/AuditAxioms.lean`: the completed-declaration axiom audit passes for 5,351
  constants, which depend on `propext`, `Classical.choice` and `Quot.sound` only.
- `scripts/check_module_headers.py` (202 sources), `scripts/check_challenge_vocabulary.py`
  (62 definitions, all needed), `scripts/check_solution_entries.py` and
  `scripts/check_paper_correspondence.py` pass, also in their strict forms `--require-complete`
  and without `--allow-incomplete`, and `git diff --check` is clean. The manifest records the
  reviewed manuscript commit `2e45bb0`; the fingerprints of all numbered statements and prose
  spans match, and every printed number is the number of the manifest.

The review edits and compiles no LaTeX.

## Every numbered entry

"Formalised" can mean a collected family of component theorems; the entry retains their exact
types. Internal inputs such as `GibbsDecomposition` are identified separately from the cited
theorem hypotheses used to construct them. Geometry, invariance, ergodicity, positivity and
parameter ranges are ordinary hypotheses, listed in the Solution comments. The last column
names the library theorems that the entry uses in place of a result the
manuscript cites.

| No. | Label | Coverage | Literature predicates | Proved in place of a citation |
|---|---|---|---|---|
| 1.1 | `thm:fraser` | Formalised | None | Fraser, Theorem 2.3 (`System.FraserBound`, `System.FraserROSC`) and Corollary 2.5 |
| 1.2 | `thm:main1` | Formalised | `JordanRapaportDimension` | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition` |
| 1.3 | `thm:main2` | Formalised | `FengLedrappierYoung`, `KittleKoglerDimension` | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, Shannon–McMillan–Breiman, Falconer's bound |
| 1.4 | `q:coincident-projection-dimensions` | Open question, recorded as `CoincidentProjectionDimensionsQuestion` | None | |
| 2.1 | `thm:box_like_sa` | Formalised | None | |
| 2.2 | `thm:A_classification` | Formalised | None | Bárány–Käenmäki–Rossi, Bárány–Käenmäki–Yu |
| 2.3 | `thm:box_like_proximal` | Formalised | None | |
| 2.4 | `thm:tau_omega_sigma_commutative` | Formalised | None | |
| 2.5 | `thm:matrix_products_g_derivatives` | Formalised | None | |
| 2.6 | `lem:proj_gap_dominated` | Formalised | None | |
| 2.7 | `prop:ssc_no_overlap_not_pesc` | Formalised | `NoOverlap.BaranyKaenmakiTheorem` | |
| 3.1 | `thm:lyapunov_exponents_via_g_system` | Formalised | None | Oseledets (box-like case), Froyland–Lloyd–Quas |
| 3.2 | `thm:conditional_measures_of_a_conditional_measure` | Formalised | None | |
| 3.3 | `thm:double_conditional` | Formalised | None | Einsiedler–Ward, Proposition 5.20 and Theorem 5.14 |
| 3.4 | `thm:finer_partition_dirac_mass` | Formalised | None | |
| 3.5 | `thm:feng_entropy_as_limit` | Formalised | None | Feng, Lemma 4.6, (4.16); planar Oseledets |
| 3.6 | `thm:feng_entropy_kolmogorov_sinai` | Formalised | None | Feng (4.17), Shannon–McMillan–Breiman, planar Oseledets, Kolmogorov–Sinai generator theorem |
| 3.7 | `thm:feng_entropy_zero` | Formalised | None | Feng, Lemma 4.6, (4.16); planar Oseledets |
| 3.8 | `thm:partitions_xi1` | Formalised | None | |
| 3.9 | `thm:partition_tau_conj` | Formalised | None | |
| 3.10 | `thm:irred_eq_state` | Formalised | None | Feng–Käenmäki, Proposition 1.2 (`FengKaenmakiNormEquilibrium`, `FengKaenmakiGibbs`, `FengKaenmakiUnique`), existence (Käenmäki), the case `s ≥ 2`, ergodicity from uniqueness, the whole proposition for tuples with rotations |
| 3.11 | `thm:two-block-normalisation` | Formalised | None | 3.10 for `𝖠²`, which has rotations |
| 3.12 | `thm:bernoulli_equilibrium` | Formalised | None | |
| 3.13 | `thm:sigma_tau_omega_positive_eq_measure` | Formalised | None | `EquilibriumGibbsStatement` |
| 3.14 | `thm:eq_state_is_sum` | Formalised | None | `FraserJordanJurgaDecomposition` (Fraser–Jordan–Jurga), `EquilibriumGibbsStatement`, existence and uniqueness of ergodic Gibbs measures (Sarig) |
| 4.1 | `thm:exact-dimensional-mixture` | Formalised | None | |
| 4.2 | `thm:feng1` | Cited | `PlanarFengLedrappierYoung`; the headlines take the box-like `FengLedrappierYoung` | the second part, `FengLedrappierYoungBar`, from the first (`fengLedrappierYoungBar_of_fengLedrappierYoung`) |
| 4.3 | `thm:entropy_eq_gibbs` | Formalised | None | `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition` |
| 4.4 | `thm:eq_state_proj_dim` | Formalised | `JordanRapaportDimension` | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition` |
| 4.5 | `ex:projection_double_dimensional` | Formalised | `JordanRapaportDimension` | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition` |
| 4.6 | `thm:gibbs_tau_omega_positive` | Formalised | None | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition` |
| 4.7 | `thm:conditional_two_ways` | Formalised | None | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition` |
| 4.8 | `thm:overline_h1_zero` | Formalised | `JordanRapaportDimension`, `FengLedrappierYoung` | `FengLedrappierYoungBar`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSumBar` |
| 4.9 | `thm:overline_h1_zero_large` | Formalised | `JordanRapaportDimension`, `FengLedrappierYoung` | `FengLedrappierYoungBar`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSumBar` |
| 4.10 | `thm:overline_h1_large` | Formalised | None | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSum`, `FengInfoSumBar` |
| 4.11 | `thm:eq_state_h1_zero` | Formalised | `JordanRapaportDimension`, `FengLedrappierYoung` | `FengLedrappierYoungBar`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSum`, `FengInfoSumBar` |
| 4.12 | `thm:eq_state_h1_large` | Formalised | `JordanRapaportDimension`, `FengLedrappierYoung` | `FengLedrappierYoungBar`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSum`, `FengInfoSumBar` |
| 4.13 | `thm:eq_state_h2_zero` | Formalised | `JordanRapaportDimension`, `FengLedrappierYoung` | `FengLedrappierYoungBar`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSum`, `FengInfoSumBar` |
| 4.14 | `thm:orto_partition_dirac` | Formalised | `JordanRapaportDimension`, `FengLedrappierYoung` | `FengLedrappierYoungBar`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSum`, `FengInfoSumBar` |
| 4.15 | `thm:SOSC_h2_zero` | Formalised | None | `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FengInfoSum` |
| 4.16 | `thm:main_extended` | Formalised | `JordanRapaportDimension`, `FengLedrappierYoung` | `FengLedrappierYoungBar`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengInfoSum`, `FengInfoSumBar`, Hutchinson's uniqueness of the invariant measure |

## Remaining work

- **1.4** (`q:coincident-projection-dimensions`). Open; recorded as the proposition
  `CoincidentProjectionDimensionsQuestion` (`BoxLike/OpenQuestion.lean`), with no answer
  asserted.

## Proof deviations

These flags distinguish changes of proof from missing statements. They do not claim a
mathematical error because a proof is different. Entries that follow the prose say so.

### 1.1 `thm:fraser`

- The paper cites Fraser with no proof. Lean follows Fraser's proof (arXiv:1108.2639v1, Section 5).
  `\dim_P X = \overline{\dim}_M X` follows from bi-Lipschitz copies and Baire category, the
  argument Fraser quotes (`System.packingDim_attractor`). The upper bound
  `\overline{\dim}_M X ≤ dimmaff(X)` follows his "Upper bound (assuming no separation
  conditions)": his Lemma 5.1 (1) (`FraserUpper.exists_sum_modSvfSum_le`), the cover of `X` by the
  copies `φ_𝐢(X)` of the `δ`-stopping words and his bounds (5.7) and (5.8) for the projections
  (`System.upperBoxDim_attractor_le_dimmaff`). The lower bound `dimmaff(X) ≤ \underline{\dim}_M X`
  under the rectangular open set condition follows his "Lower bound (assuming the ROSC)": the open
  rectangles `φ_𝐢(R)`, `𝐢 ∈ I_δ`, are pairwise disjoint, a square of side `2δ` meets boundedly many
  of them (`System.fraserStopSum_meets_le`), and his Lemma 5.1 (2) bounds the stopped sums of
  `ψ^t` from below (`System.exists_le_fraserStopSum`, `System.dimmaff_le_lowerBoxDim`).
  Corollary 2.5 follows from the second part by equality of the singular value functions on
  `[1, 2]` (`System.FraserROSC.dimmaff_eq_dimaff`).
- In the super-multiplicative case `t ≥ s_1 + s_2` of Fraser's Lemma 5.1 (2), Lean uses
  `F(𝐢) = ∑_{m<b} ∑_{|𝐣|=m} ψ^t(𝐢𝐣)`, for a block length `b` with `Ψ_b^t ≥ 1`, in place of Fraser's
  `k`-block stopping set `I_{k,δ}`; `F` satisfies `F(𝐢) ≤ ∑_j F(𝐢j)` and is comparable with `ψ^t`
  (`System.exists_le_fraserStopSum_of_ge`). As Fraser writes it, `I_{k,δ}` need not be prefix-free,
  so his (5.5) needs a bounded-multiplicity argument, which this proof does not use. The remark
  concerns Fraser's paper, not the manuscript.

### 1.2 `thm:main1`

- For `0 < s < 2` the decomposition, mixture and entropy-threshold argument agrees. Lean calls
  Jordan–Rapaport directly for exact-dimensionality under separation, so Feng–Hu is not used,
  although the surrounding prose first establishes the component fact without separation.
- For `s ≥ 2` the proof is that of Theorem 4.4.

### 1.3 `thm:main2`

- The proof follows the prose step by step (tex lines 3625 to 3738).
- The returns to the horizontal orientation come from ergodicity through Cesàro averages along
  infinitely many lengths (`frequently_measure_inter_shift_ge`); the prose invokes the mixing of
  `μ_1`, which is not needed.
- The scalar formula for the coordinate entropies of the diagonal subsystem (tex lines 3716 to
  3721) is derived from the authorised planar `FengLedrappierYoung` applied to an auxiliary
  box-like system carrying the line system on the horizontal axis; the prose cites Feng's scalar
  theorem directly. The same construction gives the scalar formula for the projective system of
  every box-like system (`System.isExactDim_map_projBar_of_fengLedrappierYoung`), which this
  proof does not use.
- Falconer's upper bound is proved; the prose cites it.

### 2.1 `thm:box_like_sa`

- Lean derives the signed-permutation form from the images of the corners of the square and
  orthogonality; the prose asserts that the images of `e_1`, `e_2` are signed coordinate vectors.
  This supplies the omitted step.

### 2.2 `thm:A_classification`

- The prose gives citations without a proof. Lean proves the claim directly: a finite invariant
  family consists of eigenlines of a proximal product (via powers and Cayley–Hamilton), and each
  generator preserves or swaps the two lines.

### 2.3 to 2.6

- 2.3 follows the prose. 2.4 implements the recursion in `ZMod 2` directly rather than through an
  integer antiderivative reduced modulo 2. 2.5 proves the product formula for a generic finite
  word first and then identifies the backward coding paths. 2.6 uses the equal extended-real
  infimum in place of the finite minimum.

### 2.7 `prop:ssc_no_overlap_not_pesc`

- The proof follows the prose (`NoOverlap.prop_ssc_no_overlap_not_pesc`): parameters outside the
  countable union of proper algebraic hypersurfaces, multiplicative independence, equal symbol
  counts, the coefficient extraction and induction. The logarithmic limit is used in the form: for
  every `c > 0`, eventually `Δ_n < c^n`.

### 3.1 `thm:lyapunov_exponents_via_g_system`

- The proof follows the prose: (V3) with the identity of `thm:matrix_products_g_derivatives`, with
  `V^1` a coordinate axis. In place of the citations of Oseledets and Froyland–Lloyd–Quas, Lean
  proves the box-like case through Birkhoff's theorem.

### 3.2 to 3.4

- 3.2 and 3.4 follow the prose. For 3.3 the prose cites Einsiedler–Ward, Proposition 5.20 and
  Theorem 5.14; Lean proves the nested disintegration identities directly, with conditional
  expectation, countable generating `π`-systems and uniqueness.

### 3.5 `thm:feng_entropy_as_limit` and 3.7 `thm:feng_entropy_zero`

- The article quotes 3.5 from Feng. Lean proves Feng's identity (Lemma 4.6, first identity of
  (4.16)) along Feng's Lemmas 4.4 and 4.5 and derives the limit from Birkhoff's theorem, as Feng
  does; where Feng runs the induction (4.18) with the chain rule for conditional information,
  Lean multiplies conditional measures by his Lemma 4.5(3) and takes logarithms. `μ(Σ') = 1` is
  the planar Oseledets theorem, proved. 3.7 follows the prose.

### 3.6 `thm:feng_entropy_kolmogorov_sinai`

- The article quotes the lemma from Feng. Lean follows Feng's (4.17): the Shannon–McMillan–Breiman
  theorem, proved by Breiman's argument, for the partition `ξ_0` by the past of `Σ'`, with
  `μ(Σ') = 1` from the planar Oseledets theorem.

### 3.8 to 3.9, 3.11 to 3.13

- These follow the prose. The combined wrappers of 3.8 and 3.9 carry unused binders; the component
  lemmas do not. 3.13 also has a shorter proof by integrating the one-step inclusion
  (`System.sigma_tau_omega_positive`).
- 3.11 takes the uniqueness and ergodicity of `μ^(2)` from 3.10 for `𝖠²`, which has rotations, so
  the irreducibility of `𝖠²` is not needed (`System.unique_of_withRotations`,
  `System.IsEquilibriumState.ergodic_of_withRotations`).
- 3.13 uses neither proximality, a hypothesis of the manuscript, nor a proximal diagonal
  generator: the full support of the equilibrium state comes from the Gibbs bounds of 3.10 for
  tuples with rotations (`EquilibriumGibbsStatement`).

### 3.10 `thm:irred_eq_state`

- The proposition is quoted from Feng–Käenmäki. Lean proves existence by a variational
  construction, the case `s ≥ 2` by the determinant calculation of 3.12, and ergodicity from
  uniqueness, since the extreme points of the set of equilibrium states are ergodic.
- For `0 < s < 2` the Gibbs bounds and uniqueness come from `FengKaenmakiNormEquilibrium`, the
  source's statement for the norm potential on the one-sided shift, along the prose: `q = s` for
  `s ≤ 1`, the rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` with `q = 2 - s` for
  `1 < s < 2`, and the reduction to the two-sided shift (`FengKaenmakiNormEquilibrium.svf`,
  `FengKaenmakiNormEquilibrium.twoSided`). The endpoint `MatrixTuple.irred_eq_state_of_fengKaenmaki`
  covers every irreducible tuple in `GL_2(ℝ)^N`; the irreducible box-like endpoint
  `System.irred_eq_state` is its specialisation through `FengKaenmakiGibbs` and
  `FengKaenmakiUnique`.
- Lean proves Feng–Käenmäki, Proposition 1.2, in the form of the source
  (`fengKaenmakiNormEquilibrium_holds`, `BoxLike/QuasiMultiplicative/`), along the architecture of
  Bowen's theorem; the endpoints take `FengKaenmakiNormEquilibrium`, `FengKaenmakiGibbs` and
  `FengKaenmakiUnique` as hypotheses, and Solution passes the proofs (`paper_3_10_25`,
  `paper_3_10_26`). The norm of an irreducible tuple is quasi-multiplicative with connecting words
  of length at most one, by compactness of the unit sphere of the matrices; invertibility is not
  needed (`MatrixTuple.normQuasiMultiplicative_of_irreducible`). For `q > 0` the periodic-orbit
  measures of `‖·‖^q` satisfy uniform Gibbs bounds for every fixed word once their period is large,
  a weak-star limit point is an invariant Gibbs measure, and a Gibbs measure is ergodic by a
  quasi-Bernoulli lower bound (`normGibbsExistence`, `MatrixTuple.HasNormGibbs.ergodic`). For every
  `q ≥ 0` an invariant `q`-equilibrium state `μ` on `Σ` satisfies `D_n(μ ‖ μ_q) ≤ log C` on the
  cylinder partitions, so `μ ≪ μ_q` and `μ = μ_q`
  (`MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs`). The one-sided statement follows through
  the natural extension (`fengKaenmakiNormEquilibrium_of_normGibbsExistence`).
- For box-like tuples with rotations, which need not be irreducible, Lean proves the whole
  proposition for every `s > 0` with no literature premise
  (`System.irred_eq_state_of_withRotations`), by an argument the prose does not give. For
  `0 < s < 2` the image `μ_G = q_*μ_1` of Bowen's ergodic Gibbs measure `μ_1` for `f_{1,s}` has the
  Gibbs bounds with a constant `K` (`System.hasGibbsBounds_map_unCode`). For an invariant
  `s`-equilibrium state `μ` the equilibrium equation at level `n` and the lower Gibbs bound give
  `D_n(μ ‖ μ_G) ≤ log K` for the relative entropy of the cylinder partitions
  (`System.IsEquilibriumState.blockRelEntropy_le`), bounded relative entropy gives `μ ≪ μ_G`
  (`absolutelyContinuous_of_blockRelEntropy_le`), and `μ = μ_G` because `μ_G` is ergodic
  (`System.IsEquilibriumState.eq_map_unCode`). For `s ≥ 2`, `μ` is the Bernoulli measure of 3.12.
  Uniqueness, ergodicity and the Gibbs bounds follow (`System.unique_of_withRotations`,
  `System.IsEquilibriumState.ergodic_of_withRotations`,
  `System.IsEquilibriumState.hasGibbsBounds_of_withRotations`); the main line takes the Gibbs
  bounds as `EquilibriumGibbsStatement` (`equilibriumGibbs`).

### 3.14 `thm:eq_state_is_sum`

- The article quotes the proposition from Fraser–Jordan–Jurga, Lemma 1.3 and Corollaries 1.5 and
  1.6. Lean proves it with no literature premise (`fraserJordanJurgaDecomposition_holds`,
  `BoxLike/FraserJordanJurga/`): Bowen's theorem gives the ergodic Gibbs measure `μ_1` of
  `f_{1,s}` on the mixing `Σ_Z` (`System.exists_isGibbs_potential₁`), and `μ_2` is its image
  under the exchange of the axes (`System.isGibbs_potential₂_map_flipAxis`); the image `q_*μ_1`
  of `μ_1` under forgetting the axis has the Gibbs bounds of `φ^s`, since each word has two lifts
  and `φ^s(A_w)` is the larger of the two exponentials (`System.hasGibbsBounds_map_unCode`);
  every invariant measure with these bounds equals `q_*μ_1` (`System.eq_of_hasGibbsBounds`); the
  four decompositions follow from `Σ_Z = τ(Σ) ⊔ ω(Σ)` and the exchange of the two ranges; the
  Lyapunov identities follow from Birkhoff's theorem along the two lifts and the relative-entropy
  comparison `\overline{λ}(𝖠, μ_2) ≤ \overline{λ}(𝖠, μ_1)`
  (`System.lyapunov_map_unCode_of_isGibbs`).
- The predicate starts from the Gibbs bounds of `thm:irred_eq_state`. The passage from the
  manuscript's hypothesis that `μ` is the `s`-equilibrium state to these bounds is 3.10 for
  tuples with rotations, `EquilibriumGibbsStatement`, which the library proves
  (`equilibriumGibbs`): every invariant `s`-equilibrium state equals `q_*μ_1`
  (`System.IsEquilibriumState.eq_map_unCode`). The entry has no literature input. Neither
  proximality nor the proximal diagonal generator of the hypothesis `S.HasProximalDiagonal` of
  the predicate is used.
- The pressure identities (`System.pressure_eq_pressureZ₁`, `System.pressure_eq_pressureZ₂`), the
  integral formulas, the flip symmetry and the fourth decomposition from the other three are
  proved from a decomposition. The existence of the ergodic Gibbs measures on `Σ_Z`, which the
  manuscript cites from Sarig, Theorem 4.7 and Corollary 4.2, is Bowen's theorem, proved:
  every Hölder potential on `Σ_Z` has exactly one ergodic Gibbs measure, and its constant is
  `P_Z(f)` (`bowenGibbsExistence`, `existsUnique_ergodic_isGibbsPotential`, `BoxLike/Bowen/`).
  The `s`-Gibbs measures of a decomposition are unique (`System.GibbsDecomposition.eq_mu₁`,
  `System.GibbsDecomposition.eq_mu₂`).

### 4.1 `thm:exact-dimensional-mixture`

- The manuscript omits the proof. Lean supplies the Radon–Nikodym and Besicovitch differentiation
  proof.

### 4.2 `thm:feng1`

- Cited, no manuscript proof. Both clauses are stated at the article's scope (`planar_feng1`):
  the first for every planar self-affine set from `PlanarFengLedrappierYoung`
  (`PlanarSystem.feng1`), the second for proximal box-like systems with rotations as
  `FengLedrappierYoungBar`.
- The second clause follows from the first, by an argument the manuscript does not give
  (`fengLedrappierYoungBar_of_fengLedrappierYoung`, `BoxLike/ProjectiveLineSystem.lean`). The
  planar system `z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` over the alphabet `ι × ZMod 2` of the
  projective system has its attractor on the horizontal axis and the projection
  `𝐣 ↦ (\overline{π}(𝐣), 0)`; its exponents are `\overline{λ}(𝖠, ν)` and
  `\overline{λ}(𝖠, ν) - log 2`, its set `Σ^ω` is empty, its slow axis is vertical, its partitions
  satisfy `ξ_2 = ξ_1`, and its entropies are `h_i = \overline{h}_i` for every `ν` carried by `Σ_Z`.
  The planar formula `FengLedrappierYoung` then reads
  `dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`, for every
  box-like system, with neither rotations nor proximality
  (`System.isExactDim_map_projBar_of_fengLedrappierYoung`). Both clauses therefore follow from
  `PlanarFengLedrappierYoung` alone (`paper_4_2_11`).
- Lean uses closed balls of the supremum norm, which give the same
  pointwise dimensions as Euclidean balls. Feng's partitions on his admissible set have almost
  everywhere the same conditional measures as the library's, so the source statement for Feng's
  partitions implies the transcription (`planarFengLedrappierYoung_of_fengXi`).

### 4.3 `thm:entropy_eq_gibbs`

- The proof follows the two-to-one coding argument of the prose; the final equality with the
  conditional-past entropy is proved by the chain rule, Lévy's upward theorem and Cesàro averaging.

### 4.4 `thm:eq_state_proj_dim`

- For `0 < s < 2` the proof follows the normalised Gibbs decomposition and the exact-dimensional
  mixture argument; Feng–Hu is unnecessary under separation because Jordan–Rapaport already gives
  exact-dimensionality.
- For `s ≥ 2` the proof follows the prose; the mixing of the orientation lift is proved by an
  explicit parity computation, an added detail.

### 4.5 `ex:projection_double_dimensional`

- `μ_1` is identified with the Markov measure by a Bernoulli construction and a Gibbs uniqueness
  argument (cylinder comparability and ergodicity); the prose states the identification. The
  entropy of the Markov measure is obtained by comparing block entropies with a Bernoulli measure
  rather than by the Markov-chain entropy formula.

### 4.6 to 4.9, 4.11, 4.13 to 4.15

- These follow the prose. In 4.8 the separate invocation of Feng–Hu is unused, since
  Jordan–Rapaport already gives exact-dimensionality. In 4.15 the recurrence comes from Poincaré
  recurrence and ergodicity, which is what the prose invokes. 4.7 also has a shorter proof that
  transports the unnormalised restrictions (`System.conditional_two_ways`).

### 4.10 `thm:overline_h1_large`

- Same cylinder-preimage and information-limit proof. Lean uses the positivity of `τ(Σ^τ)` alone
  to identify the two constants, whereas the prose obtains the equality pointwise on each positive
  part.

### 4.12 `thm:eq_state_h1_large`

- Same Jordan–Rapaport and Feng comparison and substitution of 4.10; Lean equates the two
  expressions by the uniqueness of the exact dimension.

### 4.16 `thm:main_extended`

- For `s < 2` the proof follows the normalisation, the two entropy regimes, the strong open set
  case and the evaluation of Feng's formula.
- Feng's scalar formula, which the prose cites, is derived from the planar `FengLedrappierYoung`
  (`fengLedrappierYoungBar_of_fengLedrappierYoung`, see 4.2).
- For `s ≥ 2` Lean identifies the equilibrium state as Bernoulli from the equality case of the
  entropy bound and Gibbs' inequality, rather than citing 3.12, and proves Hutchinson's uniqueness
  of the invariant measure.

## Unnumbered material

The manifest also fingerprints 45 unnumbered spans: 44 formalised and 1 cited, the dimensions of
the projected Gibbs measures `eq:gibbs_proj_dim`, which is Jordan–Rapaport. The formalised spans
include the existence and uniqueness of the ergodic Gibbs measure of a Hölder potential on the
mixing sub-shift, Bowen's theorem, proved in `BoxLike/Bowen/` with no literature input;
`eq:simple_lyapunov`, proved along Morris–Shmerkin, Lemmas 3.4 and 3.5, for every proximal
box-like tuple with rotations, without the case split by a proximal diagonal generator and the
passage to `𝖠²` of tex lines 2363 to 2369 (`morrisShmerkinLyapunov_holds`); Rossi's bound
`eq:hausdorff_ergodic_lyapunov`, proved for every box-like system and every ergodic measure by a
covering argument (`System.rossiBound`, `prose_rossi_0`), which no proof of a numbered result
uses; and the squeeze `dimmaff(X) = dimaff(X)` of tex lines 548 to 550 for every box-like set with
`\dim_H X = dimaff(X)`, from the first part of `thm:fraser` (`System.dimmaff_eq_dimaff`,
`System.fraserBound_holds`, `prose_squeeze_0`). A fingerprint certifies the reviewed source
snapshot, not mathematical completeness. The declaration index below records the individual
library components; the numbered assessment above controls claims about the whole manuscript
statement.

The formulation of planar exponential separation in the norm on affine coefficients (tex lines
1535 to 1537) is not formalised. The library proves the lower bound on distances between distinct
cylinder images (`System.StrongSeparation.exists_le_dist_phiWord`).

## Declaration index

Every result of the paper with the declarations that certify it, by topic. Tex line numbers
are those of the manuscript at commit `2e45bb0`.

| Result | Declaration | Module | State |
|---|---|---|---|
| `eq:def_of_eps_mod2` | `eps`, `eps_add_one`, `eq_eps_of_succ` | `Orientation` | **done** |
| `eq:tau_omega_sigma_commutative1` | `eps_shift` | `Orientation` | **done** |
| matrix `Z`, `Z²` positive | `Trans`, `trans_iff`, `exists_trans_trans` | `Coding` | **done** |
| `Σ_Z` is topologically mixing (tex lines 898 to 899) | `IsTopologicallyMixing`, `transMatrix_sq_pos`, `isTopologicallyMixing_subshiftShift`, `isTopologicallyMixing_subshiftShift_iff` | `Support/SubshiftMixing` | **done**, exactly when both orientations occur |
| `eq:def_of_tau_omega` | `tau`, `omega`, `unCode` | `Coding` | **done** |
| `eq:tau_omega_partition` | `range_tau`, `range_omega`, `range_tau_union_range_omega`, `disjoint_range_tau_range_omega` | `Coding` | **done** |
| `thm:tau_omega_sigma_commutative` | `tau_shift_of_eps_eq_zero`, `omega_shift_of_eps_eq_zero`, `tau_shift_of_eps_eq_one`, `omega_shift_of_eps_eq_one` | `Coding` | **done** |
| continuity of `τ`, `ω`, `\overline{π}`, `π` | `System.continuous_tau`, `System.continuous_omega`, `System.Bounds.continuous_projBar`, `System.continuous_proj` | `Attractor` | **done** |
| `τ`, `ω` homeomorphisms onto their images (tex line 939); `Σ_Z`, `τ(Σ)`, `ω(Σ)` closed; `β` a homeomorphism with `β ∘ σ² = σ^(2) ∘ β` (tex lines 2313 to 2314) | `isClosedEmbedding_tau`, `isClosedEmbedding_omega`, `tauHomeomorph`, `omegaHomeomorph`, `isClosed_subshift`, `groupHomeomorph`, `groupHomeomorph_shift_two` | `CodingTopology` | **done**; the images are closed |
| the natural projection `η : Σ → Σ^+`, `η ∘ σ = σ^+ ∘ η`, the embedding `e` with `e ∘ σ^+ ≠ σ ∘ e` (tex lines 803 to 812) | `eta`, `shiftPlus`, `eta_shift`, `measurePreserving_shiftPlus_map_eta`, `embed`, `embed_comp_shiftPlus_ne` | `CodingTopology` | **done**; `e ∘ σ^+ ≠ σ ∘ e` needs `N ≥ 2` |
| `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is a bijection, `η_*μ` ergodic iff `μ` ergodic (tex lines 830 to 849) | `map_eta_injective`, `exists_map_eta_eq`, `existsUnique_map_eta_eq`, `exists_ergodic_map_eta_eq`, `mapEtaEquiv`, `ergodic_map_eta_iff`, `ergodic_mapEtaEquiv_symm_iff`, `isSigmaSubadditive_futureContent` | `CodingTopology`, `NaturalExtension` | **done**, by the Carathéodory extension of a content on the clopen future sets (Mathlib has no Kolmogorov extension theorem); `(π^+)_*μ^+ = π_*μ` (tex lines 850 to 851) is in `Support/OneSidedProjection` |
| `thm:box_like_sa` | `IsSquareIsometry`, `isSquareIsometry_iff`, `IsBoxLikeMatrix`, `isBoxLikeMatrix_iff`, `IsSquareIsometry.boxMat_zero_mul_orientation`, `IsBoxLikeWithRotations`, `box_like_sa`, `box_like_sa_of_contracting`, `PlanarSystem.box_like_sa`, `System.isBoxLikeWithRotations_iff`, `PlanarSystem.isBoxLikeWithRotations_iff_exists_system` | `BoxLikeMatrix`, `Aligned/BoxLikeSA` | **done**, for the whole tuple, with "rotating" read as exchanging the axes; the forward direction uses only `R([-1,1]²) ⊆ [-1,1]²` |
| `thm:A_classification` | `TupleIrreducible`, `TupleStronglyIrreducible`, `TupleProximal`, `tuple_classification`, `tuple_trichotomy`, `not_tupleIrreducible_iff_simultaneouslyTriangular`, `simultaneouslyBoxLike_of_proximal`, `simultaneouslyBoxLike_iff`, `tupleIrreducible_iff_lines`, `tupleStronglyIrreducible_iff_lines` | `Classification` | **done**, for arbitrary planar tuples, with no literature input; without proximality both directions of the "i.e." of item (2) fail (`not_tupleIrreducible_swap`, `not_simultaneouslyBoxLike_rotThree`) |
| a proximal box-like tuple with rotations is in case (2) of `thm:A_classification` | `System.irreducible_iff_tupleIrreducible`, `System.proximal_iff_tupleProximal`, `System.not_tupleStronglyIrreducible`, `System.tupleIrreducible_of_proximal`, `System.irreducible_and_not_stronglyIrreducible` | `Classification` | **done** |
| the all-anti-diagonal case (tex lines 744 to 746) and the reduction to box-like coordinates in a basis of unit vectors (tex lines 777 to 789) | `System.sq_o_of_forall_anti`, `antiDiagonalExample`, `antiDiagonalExample_proximal`, `antiDiagonalExample_irreducible`, `antiDiagonalExample_not_stronglyIrreducible`, `antiDiagonalExample_not_withRotations`, `irreducible_not_stronglyIrreducible_iff_unitBasis`, `PlanarSystem.exists_system_of_irreducible` | `Aligned/BoxLikeProximal`, `Planar/ChangeOfBasis` | **done**; the classification sentence of the introduction treats the all-anti-diagonal case through its diagonal second iterates, as `System.sq_o_of_forall_anti` does, and `antiDiagonalExample` shows that this case is not box-like with rotations in any basis |
| irreducible tuples; a tuple with rotations and a proximal diagonal generator is irreducible, and so is a proximal tuple with rotations | `System.Irreducible`, `System.irreducible_of_hasProximalDiagonal`, `System.irreducible_of_proximal` | `Proximal`, `SigmaMeasure` | **done** |
| proximal matrices and tuples (`sec:irreducibility`) | `IsProximalMatrix`, `isProximalMatrix_iff_trace_det`, `System.Proximal` | `Proximal` | **done**, through the characteristic polynomial |
| `thm:box_like_proximal` | `System.Proximal.box_like_proximal`, `System.Proximal.hasProximalDiagonal_or_sq`, `System.isProximalMatrix_matWord`, `System.absMat_matWord_eq_smul_pairs`, `System.prod_absMat_sq_mat_eq_smul`, `System.Proximal.hasProximalDiagonal_or_sq_of_cocycle` | `Proximal` | **done**, for every box-like tuple, by the argument of the prose; the weighted-cocycle proof is a second proof |
| product rule for diagonal and anti-diagonal matrices | `boxMat`, `boxMat_mul` | `System` | **done** |
| `eq:def_of_g_system` | `System.ratio`, `System.trans`, `System.g` | `System` | **done** |
| `eq:phi_def_by_g` | `System.coord_phi`, `System.phi_of_o_eq_zero`, `System.phi_of_o_eq_one`, `System.phi_eq_mulVec` | `System` | **done** |
| `A_𝐢` as a box matrix with entries `g'` along the path of `Σ_Z` | `System.matWord_eq` | `System` | **done** |
| `thm:matrix_products_g_derivatives` | `System.abs_matWord_pastWord_e1`, `System.abs_matWord_pastWord_e2` | `System` | **done**, with `|·|` written as the sum of the moduli of the two entries, one of which vanishes |
| `\overline{π}` | `System.projBar`, `System.Bounds.tendsto_gWord`, `System.Bounds.projBar_eq` | `Projection` | **done** |
| `eq:canonical_projection` | `System.proj`, `System.Bounds.tendsto_phiWord` | `Projection` | **done** |
| the one-sided projection `π^+` of an affine iterated function system, `π = π^+ ∘ η`, `π(Σ) = π^+(Σ^+) = X`, `(π^+)_*μ^+ = π_*μ` (tex lines 814 to 822, 850 to 851) | `MatrixTuple.canonicalProjPlus`, `MatrixTuple.canonicalProj`, `PlanarSystem.toPlane_proj` | `Support/OneSidedProjection`, `Support/PlanarProjection` | **done**, for every contracting affine system; invertibility is not used |
| `eq:commutative_diagram` | `System.fst_proj`, `System.snd_proj`, `System.coord_phiWord` | `Projection` | **done** |
| `π(𝐢) = φ_{i_0}(π(σ𝐢))`, `π = π^+ ∘ η` | `System.Bounds.proj_eq`, `System.proj_congr` | `Projection` | **done** |
| `eq:self_affine_set_def` for `X = π(Σ)` | `System.attractor`, `System.Bounds.attractor_eq_iUnion` | `Projection` | **done** |
| `X` compact, non-empty, unique (Hutchinson); `φ_i` Lipschitz and injective; `Φ^(2)` has attractor `X` | `System.isCompact_attractor`, `System.attractor_nonempty`, `System.eq_attractor`, `System.lipschitzWith_phi`, `System.injective_phi`, `System.attractor_sq` | `Attractor` | **done** |
| planar self-affine sets in general (tex lines 626 to 638): the systems, the projection, Hutchinson's theorem | `PlanarSystem`, `PlanarSystem.proj`, `PlanarSystem.attractor`, `PlanarSystem.isCompact_attractor`, `PlanarSystem.eq_attractor`, `System.toPlanar` | `Planar/System`, `Planar/FalconerBound` | **done**; a box-like system is a planar system through `System.toPlanar` |
| strong separation, strong open set and rectangular open set conditions; strong separation implies the strong open set condition; both pass to `Φ^(2)` | `System.StrongSeparation`, `System.StrongOpenSet`, `System.RectangularOpenSet`, `System.StrongSeparation.strongOpenSet`, `System.StrongSeparation.sq`, `System.StrongOpenSet.sq` | `SeparationConditions` | **done** |
| `Δ_n^Ψ`, projective exponential separation | `System.gap`, `System.ProjExpSeparation` | `Separation` | **done** |
| no exact overlaps, free semigroup (tex lines 1371 to 1372), compositions of similarities | `System.NoExactOverlaps`, `System.noExactOverlaps_iff`, `simWord`, `System.gWord_eq_simWord` | `Separation` | **done** |
| the absence of exact overlaps passes to `Φ^(2)` (proof of `thm:main2`, tex lines 3634 to 3636) | `System.NoExactOverlaps.sq` | `SecondIterate` | **done** |
| `Δ_{m+1}^Ψ ≤ Δ_m^Ψ` (proof of `thm:two-block-normalisation`) | `System.gap_succ_le` | `Separation` | **done** |
| `lem:proj_gap_dominated` | `System.diagGap`, `System.gap_le_diagGap` | `Separation` | **done** |
| `prop:ssc_no_overlap_not_pesc` | `NoOverlap.prop_ssc_no_overlap_not_pesc`, `NoOverlap.ssc_no_overlap_not_pesc'`, `NoOverlap.ssc_no_overlap_not_pesc`, `NoOverlap.exists_system_of_homFree`, `NoOverlap.BaranyKaenmakiTheorem`, `NoOverlap.BaranyKaenmakiPair`, `NoOverlap.exists_pair_of_baranyKaenmakiTheorem`, `System.FreeProjective`, `System.not_projExpSeparation_of_diagGap` | `Aligned/NoOverlapPESC`, `NoOverlapExample`, `NoOverlapExampleFree`, `Separation` | **done** from the `Prop` hypothesis `NoOverlap.BaranyKaenmakiTheorem`, Theorem 2.1 of the source, which the article uses; `NoOverlap.ssc_no_overlap_not_pesc` takes the stronger retained form `NoOverlap.BaranyKaenmakiPair`. "Not strongly irreducible" is `¬ TupleStronglyIrreducible` of `Classification` |
| freeness of the projective semigroup and the choice of parameters in the proof of `prop:ssc_no_overlap_not_pesc` (tex lines 1429 to 1443, 1482 to 1511) | `NoOverlap.exists_params_not_mem_exceptionalSet`, `NoOverlap.Params.mulIndependent`, `NoOverlap.Params.count_eq_of_gDeriv_eq`, `NoOverlap.eq_of_valPoly_eq`, `NoOverlap.Params.freeProjective_of_mulIndependent`, `NoOverlap.exists_algebraicIndependent_mem_Ioo`, `NoOverlap.exists_params`, `NoOverlap.genDeriv_transfer`, `NoOverlap.genVal_transfer`, `NoOverlap.eq_of_genDeriv_eq_of_genVal_eq`, `NoOverlap.Params.freeProjective` | `Aligned/NoOverlapPESCParams`, `Aligned/NoOverlapPESCFree`, `NoOverlapExampleFree`, `NoOverlapExample` | **done**, along the prose: parameters outside a countable union of proper algebraic hypersurfaces, multiplicative independence, symbol counts and coefficient extraction; the sequential transcendental choice is a second proof |
| the paragraph after `prop:ssc_no_overlap_not_pesc`: planar exponential separation does not imply projective exponential separation (tex lines 1527 to 1537) | `System.StrongSeparation.exists_le_dist_phiWord`, `NoOverlap.planar_separation_not_pesc` | `NoOverlapExample` | **done** from `NoOverlap.BaranyKaenmakiPair` |
| `φ^s`, sub-multiplicativity | `svf`, `svf_mul_le` | `SingularValue` | **done**, on all real `2 × 2` matrices with the `ℓ²` operator norm |
| `α_1 = max{|a|,|b|}`, `α_1 α_2 = |a||b|`, values of `φ^s` on box matrices | `norm_boxMat`, `abs_det_boxMat`, `svf_boxMat_of_le_one`, `svf_boxMat_of_le_two`, `svf_boxMat_of_two_lt` | `SingularValue` | **done** |
| `P(𝖠, s)`, existence of the limit by Fekete | `System.svfSum`, `System.svfSum_add_le`, `System.pressure`, `System.RatioLowerBound.tendsto_pressure` | `Pressure` | **done** |
| `s ↦ P(𝖠, s)` continuous, strictly decreasing, `P(𝖠, 0) = log N`, `P → -∞`, `dimaff` as its unique zero | `System.pressure_zero`, `System.exists_pressure_slope`, `System.strictAntiOn_pressure`, `System.continuousOn_pressure`, `System.tendsto_pressure_atTop`, `System.dimaff`, `System.pressure_dimaff`, `System.dimaff_eq`, `System.dimaff_pos` | `AffinityDim` | **done** |
| the pressure and the affinity dimension of an arbitrary tuple in `GL_2(ℝ)^N` and of a planar self-affine set (tex lines 2144 to 2157, 2171 to 2172): existence of the limit, continuity, convexity between consecutive integers, strict decrease under `max_i ‖A_i‖ < 1` | `MatrixTuple.pressure`, `MatrixTuple.tendsto_pressure`, `MatrixTuple.pressure_convexOn_Icc_nat`, `MatrixTuple.pressure_convexOn_Ici_two`, `PlanarSystem.existsUnique_pressure_eq_zero`, `PlanarSystem.dimaff`, `PlanarSystem.dimaff_eq`, `System.toPlanar_dimaff` | `MatrixTuple`, `TupleEquilibrium`, `Support/PressureConvexity`, `Planar/AffinityDim` | **done**, with no literature input |
| Minkowski and packing dimensions of sets (tex lines 2174 to 2175, Falconer, *Techniques*, §2) | `upperBoxDim`, `lowerBoxDim`, `packingDim`, `upperBoxDim_le_of_forall`, `le_lowerBoxDim_of_forall`, `upperBoxDim_image_eq`, `lowerBoxDim_image_eq`, `packingDim_image_eq`, `upperBoxDim_le_lowerBoxDim_of_superMul`, `dimH_le_lowerBoxDim`, `dimH_le_packingDim`, `packingDim_le_upperBoxDim`, `packingDim_eq_upperBoxDim` | `SetDimensions` | **done**, with values in `ℝ≥0∞`; the packing dimension is the modified upper Minkowski dimension |
| the modified affinity dimension `dimmaff(X)` (tex lines 2175 to 2189), Fraser's Lemma 2.1, the existence of the Minkowski dimensions of the projections (after Fraser's Lemma 2.7), `dimmaff(X) ≤ dimaff(X)` (tex lines 548 to 550 and 2184) | `System.projDim`, `System.modSvf`, `System.modSvf_append_le`, `System.le_modSvf_append`, `System.modPressure`, `System.tendsto_modPressure`, `System.dimmaff`, `System.dimmaff_eq`, `System.lowerBoxDim_coord_eq`, `System.projDim_eq_lowerBoxDim`, `System.upperBoxDim_coord_le_dimaff`, `System.projDim_le_dimaff`, `System.dimmaff_le_dimaff`, `System.dimmaff_eq_dimaff_of_full`, `System.dimaff_eq_dimmaff_of_projDim_eq_one` | `ModifiedAffinity` | **done**, with no literature input; `s(𝐢)` is the Minkowski dimension of the projection, the modified pressure is a limit, and `dimmaff(X) ≤ dimaff(X)` holds for every box-like set |
| `thm:fraser` | `System.FraserBound`, `System.FraserROSC`, `System.fraserBound_holds`, `System.fraserROSC_holds`, `System.packingDim_attractor`, `System.fraserBound_iff`, `System.fraserROSC_of_le`, `System.fraserROSC_of_fraserBound`, `System.FraserROSC.dimmaff_eq_dimaff`, `System.FraserROSC.dim_eq_dimaff`, `System.fraserBound_of_subsingleton`, `System.fraserROSC_of_subsingleton` | `FraserChain`, `Fraser/UpperBound`, `Fraser/Lower`, `Fraser/Main` | **done** for every box-like set, with no literature input: the first two parts are Fraser's Theorem 2.3 as the `Prop`s `System.FraserBound` and `System.FraserROSC`, compared with arXiv:1108.2639v1 and proved along his Section 5; the results that use them take them as hypotheses, and Solution passes the proofs; the third part (Fraser's Corollary 2.5) from `System.FraserROSC`, and without the rectangular open set condition when `dimaff(X) ≤ 2` (`System.dimmaff_eq_dimaff_of_full`) |
| `thm:fraser`: the upper bound `\overline{\dim}_M X ≤ dimmaff(X)` (Fraser, §5, "Upper bound (assuming no separation conditions)", Lemma 5.1 (1), (5.7) and (5.8)) | `FraserUpper.externalCoveringNumber_union_le`, `FraserUpper.exists_externalCoveringNumber_le`, `FraserUpper.externalCoveringNumber_le_mul_grid`, `FraserUpper.attractor_subset_iUnion`, `FraserUpper.externalCoveringNumber_phiWord_le`, `FraserUpper.exists_sum_modSvfSum_le`, `System.upperBoxDim_attractor_le_of_modPressure_neg`, `System.upperBoxDim_attractor_le_dimmaff` | `Fraser/Upper` | **done**, with no separation condition: the copies `φ_𝐢(X)` of the stopping words cover `X`, and each needs at most `C (D + 1) δ₀^{-s} ρ^{-(s+ε)} ψ^s(𝐢)` squares of side `2ρ` |
| `thm:fraser`: the `δ`-stoppings `I_δ` and Fraser's Lemma 5.1 (2) | `System.fraserStopSum`, `System.le_fraserStopSum`, `System.fraserStopSum_le`, `System.fraserTail`, `System.fraserModSvf_append_le`, `System.fraserTail_le_fraserStopSum`, `System.one_lt_fraserStopSum_of_le`, `System.exists_le_fraserStopSum_of_ge`, `System.exists_le_fraserStopSum` | `Fraser/LowerStop` | **done**: a sum over `I_δ` is a sum over a tree of words, and two tree inequalities take the place of the combinatorics of prefix codes; the super-multiplicative case uses a block sum ("Proof deviations", 1.1) |
| `thm:fraser`: the lower bound `dimmaff(X) ≤ \underline{\dim}_M X` under the rectangular open set condition (Fraser, §5, "Lower bound (assuming the ROSC)") | `System.fraserAttractor_subset`, `System.fraser_volume_le`, `System.fraserStopSum_meets_le`, `System.fraser_sum_volume_le`, `System.fraser_coveringNumber_le`, `System.fraser_exists_axis`, `System.dimmaff_le_lowerBoxDim` | `Fraser/LowerCover` | **done**: by an area count, a square of side `2δ` meets the closures of boundedly many of the disjoint rectangles `φ_𝐢(R)`, `𝐢 ∈ I_δ` |
| `eq:hausdorff_affinity_upper_bound` and Falconer's bound for the upper Minkowski dimension (tex lines 2159 to 2172, 542 to 544) | `PlanarSystem.upperBoxDim_attractor_le`, `PlanarSystem.dimH_attractor_le`, `PlanarSystem.packingDim_attractor_le`, `PlanarSystem.upperBoxDim_attractor_le_dimaff`, `Ellipse.exists_strip`, `Ellipse.exists_finset_cover`, `MatrixTuple.ContractionBound.upperBoxDim_le_of_pressure_neg`, `System.upperBoxDim_attractor_le_planar`, `System.dimH_attractor_le_planar`, `System.upperBoxDim_attractor_le`, `System.dimH_attractor_le`, `System.falconerBoxBound` | `Planar/FalconerBound`, `FalconerBound`, `FraserChain` | **done**, with no literature input, for every planar self-affine set by the Euclidean ellipse cover of tex lines 2162 to 2165; for box-like sets also by the covering in the supremum metric; no separation, rotations or proximality |
| the chain `\dim_H X = \dim_P X = \dim_M X = dimaff(X)` and the squeeze `dimmaff(X) = dimaff(X)` (tex lines 540 to 556) | `System.FalconerBoxBound`, `System.falconerBoxBound_iff`, `System.falconerBoxBound_iff_euclidean`, `System.FalconerBoxBound.dimH_le`, `System.FalconerBoxBound.dimmaff_le_dimaff`, `System.dim_chain`, `System.dimmaff_eq_dimaff`, `System.dim_chain_noExactOverlaps`, `System.dimmaff_eq_dimaff_noExactOverlaps`, `System.dim_chain_main2`, `System.dimmaff_eq_dimaff_main2` | `FraserChain`, `MainTwoFree` | **done**: the chain for every box-like set with `\dim_H X = dimaff(X)`, with no hypothesis beyond it; the squeeze from `System.FraserBound`, which holds (`System.fraserBound_holds`), so for every such set with no literature input; the `noExactOverlaps` forms take the hypotheses of `thm:main2`, the `main2` forms are the special case under projective exponential separation |
| `thm:irred_eq_state`: the Gibbs bounds for `0 < s < 2` | `System.HasGibbsBounds`, `FengKaenmakiGibbs`, `fengKaenmakiGibbs_holds`, `EquilibriumGibbsStatement`, `equilibriumGibbs` | `Thermodynamic`, `Literature`, `QuasiMultiplicative/Main`, `EquilibriumGibbsStatement`, `EquilibriumGibbs` | **done**, with no literature input: for tuples with rotations `equilibriumGibbs`; for irreducible tuples `FengKaenmakiGibbs` holds (`fengKaenmakiGibbs_holds`) |
| `thm:irred_eq_state`: uniqueness for every `s > 0`, for a box-like tuple with rotations | `System.unique_equilibrium_of_lt_two`, `System.unique_equilibrium_of_two_le`, `System.unique_equilibrium` | `UniqueEquilibrium` | **done**, with no literature hypothesis; for `0 < s < 2` both states are `q_*μ_1` (`System.IsEquilibriumState.eq_map_unCode`), for `s ≥ 2` both are the Bernoulli measure, with no hypothesis on the tuple |
| `thm:irred_eq_state` for `s ≥ 2`: existence, uniqueness, ergodicity | `System.isEquilibriumState_bernoulli`, `System.IsEquilibriumState.eq_bernoulli`, `System.existsUnique_isEquilibriumState_of_two_le`, `System.IsEquilibriumState.ergodic_of_two_le` | `BernoulliEquilibrium` | **done**, with no literature hypothesis: the equilibrium state is the Bernoulli measure with weights `|det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` |
| `thm:irred_eq_state`: existence, the weak-star infrastructure (tex lines 2217 to 2218, Käenmäki, Theorems 2.6 and 4.1) | `compactSpace_probabilityMeasure`, `InvariantMeasures`, `isCompact_invariantMeasures`, `invariantMeasures_nonempty`, `entropy_eq_iInf`, `System.energyLim_eq_iInf`, `upperSemicontinuousOn_entropy`, `System.upperSemicontinuousOn_energyLim`, `System.exists_maximiser` | `InvariantMeasures` | **done**, with no literature input: `h_0 + Λ(𝖠, ·, s)` attains its maximum on the compact set `ℳ_σ(Σ)` for every `s ≥ 0` |
| `thm:irred_eq_state`: existence, for every `s ≥ 0` | `System.log_svfSum_le_avgBlockMeasure`, `System.exists_invariant_pressure_le`, `System.exists_invariant_le_entropy_add_energy`, `System.exists_isEquilibriumState` | `EquilibriumExistence` | **done**, with no literature input, by the construction of Misiurewicz: the averaged block measures satisfy the two-parameter estimate, and a weak-star limit point is an equilibrium state. Irreducibility is not used; an ergodic equilibrium state exists for every tuple (below) |
| an ergodic `s`-equilibrium state exists for every tuple of invertible matrices and every `s ≥ 0` (tex lines 2217 to 2218) | `cylinderQuad`, `cylinderQuad_mix_lt`, `MatrixTuple.IsEquilibriumState.ergodic_of_extreme`, `MatrixTuple.isCompact_equilibriumStates`, `MatrixTuple.exists_ergodic_isEquilibriumState`, `System.exists_ergodic_isEquilibriumState` | `TupleErgodicEquilibrium` | **done**, with no literature input; the extreme point is the maximiser of a strictly convex weak-star continuous functional of the cylinder masses |
| `thm:irred_eq_state` for box-like tuples with rotations, irreducible or not: existence, uniqueness, ergodicity and the Gibbs bounds for every `s > 0` (tex lines 2225 to 2234) | `System.irred_eq_state_of_withRotations`, `System.existsUnique_isEquilibriumState_of_withRotations`, `System.unique_of_withRotations`, `System.IsEquilibriumState.ergodic_of_withRotations`, `System.IsEquilibriumState.hasGibbsBounds_of_withRotations`, `System.IsEquilibriumState.eq_map_unCode`, `System.IsEquilibriumState.eq_of_hasGibbsBounds`, `System.IsEquilibriumState.absolutelyContinuous_of_hasGibbsBounds`, `System.IsEquilibriumState.blockRelEntropy_le`, `EquilibriumGibbsStatement`, `equilibriumGibbs` | `EquilibriumGibbs`, `EquilibriumGibbsStatement` | **done**, with no literature input: for `0 < s < 2` every invariant equilibrium state is `q_*μ_1`, since `D_n(μ ‖ q_*μ_1) ≤ log K` for the cylinder partitions and `q_*μ_1` is ergodic; for `s ≥ 2` it is the Bernoulli measure |
| relative entropy of the cylinder partitions; bounded relative entropy implies absolute continuity | `blockRelEntropy`, `blockRelEntropy_eq`, `measureReal_window_preimage`, `mul_measureReal_window_le`, `absolutelyContinuous_of_blockRelEntropy_le` | `Support/RelativeEntropy` | **done**, for invariant probability measures on the two-sided shift over a finite alphabet, from Gibbs' inequality on the windows `{𝐢 : (i_{-m}, …, i_m) ∈ F}` |
| `thm:irred_eq_state` for irreducible box-like systems: existence, uniqueness, ergodicity and the Gibbs bounds for every `s > 0` | `System.irred_eq_state`, `System.unique_of_irreducible`, `System.IsEquilibriumState.ergodic_of_irreducible`, `System.IsEquilibriumState.hasGibbsBounds_of_irreducible` | `IrreducibleEquilibrium` | **done**, with no literature input: the hypotheses `FengKaenmakiGibbs`, `FengKaenmakiUnique`, for `0 < s < 2` only, follow from `FengKaenmakiNormEquilibrium` (`FengKaenmakiNormEquilibrium.fengKaenmakiGibbs`, `FengKaenmakiNormEquilibrium.fengKaenmakiUnique`) and hold (`fengKaenmakiGibbs_holds`, `fengKaenmakiUnique_holds`) |
| `thm:irred_eq_state` for arbitrary invertible tuples: existence, the case `s ≥ 2`, the norm and rescaled potentials, the reduction to the one-sided shift, ergodicity of a unique equilibrium state (tex lines 2225 to 2239) | `MatrixTuple.exists_isEquilibriumState`, `MatrixTuple.irred_eq_state_of_two_le`, `MatrixTuple.isEquilibriumState_iff_rescale`, `MatrixTuple.hasGibbsBounds_iff_rescale`, `MatrixTuple.isNormEquilibriumPlus_map_eta_iff`, `MatrixTuple.ergodic_of_unique` | `TupleEquilibrium`, `TupleEquilibriumExistence`, `TupleEquilibriumLarge`, `TupleEquilibriumNorm` | **done**, with no literature input; the Gibbs bounds and uniqueness for `0 < s < 2` come from `FengKaenmakiNormEquilibrium` (next row) |
| `thm:irred_eq_state` for every irreducible tuple of invertible planar matrices: existence, uniqueness, ergodicity and the Gibbs bounds for every `s > 0` | `MatrixTuple.irred_eq_state_of_fengKaenmaki`, `FengKaenmakiNormEquilibrium`, `FengKaenmakiNormEquilibrium.twoSided`, `FengKaenmakiNormEquilibrium.svf`, `FengKaenmakiNormEquilibrium.degenerate_quarterTurn` | `IrreducibleEquilibriumTuple`, `LiteratureFengKaenmaki` | **done**, at the article's scope, with no literature input: the hypothesis `FengKaenmakiNormEquilibrium`, for `0 < s < 2` only, holds (`fengKaenmakiNormEquilibrium_holds`, next rows) |
| Feng–Käenmäki, Proposition 1.2, behind `thm:irred_eq_state`: `FengKaenmakiNormEquilibrium` and its box-like specialisations hold | `fengKaenmakiNormEquilibrium_holds`, `fengKaenmakiGibbs_holds`, `fengKaenmakiUnique_holds`, `fengKaenmakiNormEquilibrium_of_normGibbsExistence`, `MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq` | `QuasiMultiplicative/Main` | **done**, with no literature input; the one-sided statement through the natural extension (`exists_map_eta_eq`, `MatrixTuple.isNormEquilibriumPlus_map_eta_iff`, `MatrixTuple.hasNormGibbsPlus_map_eta_iff`) |
| quasi-multiplicativity of the norm of an irreducible planar tuple | `MatrixTuple.NormQuasiMultiplicative`, `MatrixTuple.exists_pos_le_norm_mul_word_mul`, `MatrixTuple.normQuasiMultiplicative_of_tupleIrreducible`, `MatrixTuple.normQuasiMultiplicative_of_irreducible` | `QuasiMultiplicative/Defs`, `QuasiMultiplicative/Irreducible` | **done**, with connecting words of length at most one, by compactness of the unit sphere of the matrices; invertibility is not used |
| an ergodic Gibbs measure of `‖·‖^q` on `Σ` for a quasi-multiplicative tuple and `q > 0` | `NormGibbsExistenceStatement`, `normGibbsExistence`, `MatrixTuple.NormQMConstants.exists_normSum_le`, `MatrixTuple.normPeriodicMeasure`, `MatrixTuple.NormQMConstants.exists_eventually_gibbs`, `MatrixTuple.exists_hasNormGibbs_of_forall_normGibbsUpTo`, `MatrixTuple.NormQuasiMultiplicative.exists_ergodic_hasNormGibbs`, `MatrixTuple.HasNormGibbs.ergodic` | `QuasiMultiplicative/GibbsMeasurePressure`, `QuasiMultiplicative/GibbsMeasurePeriodic`, `QuasiMultiplicative/GibbsMeasure`, `QuasiMultiplicative/GibbsMeasureErgodic` | **done**, by Bowen's construction: `e^{nP} ≤ Z_n ≤ K e^{nP}`, periodic-orbit measures with uniform Gibbs bounds, a weak-star limit point, and ergodicity from a quasi-Bernoulli lower bound with gaps that vary with the words |
| every invariant `q`-equilibrium state of `‖·‖^q` on `Σ` equals every ergodic Gibbs measure, `q ≥ 0` | `MatrixTuple.lyapunov₁_le_div`, `MatrixTuple.IsNormEquilibrium.le_blockEntropy_add`, `MatrixTuple.IsNormEquilibrium.blockRelEntropy_le`, `MatrixTuple.IsNormEquilibrium.absolutelyContinuous_of_hasNormGibbs`, `MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs` | `QuasiMultiplicative/Uniqueness` | **done**: `D_n(μ ‖ ν) ≤ log C` on the cylinder partitions gives `μ ≪ ν` (`absolutelyContinuous_of_blockRelEntropy_le`), the argument of `EquilibriumGibbs` for the norm potential |
| sub-multiplicativity of the equilibrium state, `C⁻¹ φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C φ^s(A_𝐢)` at `s = dimaff` (tex lines 2241 to 2255) | `System.HasGibbsBounds.submultiplicative`, `System.HasGibbsBounds.cylinder_bounds_dimaff`, `System.IsEquilibriumState.submultiplicative`, `System.IsEquilibriumState.cylinder_bounds_dimaff` | `GibbsProperties` | **done**; the forms for the equilibrium state of an irreducible tuple take `FengKaenmakiGibbs`, which holds (`fengKaenmakiGibbs_holds`) |
| Bernoulli measures, their invariance and ergodicity (tex lines 2355 to 2362) | `bernoulli`, `measurePreserving_shift_bernoulli`, `ergodic_shift_bernoulli`, `eq_bernoulli_of_cylinder`, `eq_bernoulli_weightMeasure_of_measureReal_cylinder`, `entropy_bernoulli`, `IsBernoulli` | `BernoulliEquilibrium`, `GibbsProperties` | **done** |
| the equilibrium state for `0 < s < 2` is not quasi-Bernoulli and not Bernoulli (tex lines 517 to 525, 2362 to 2369); grouping a Bernoulli measure in pairs gives a Bernoulli measure (tex lines 2367 to 2368) | `System.exists_mul_svf_le`, `System.not_quasiBernoulli`, `System.not_isBernoulli`, `System.IsEquilibriumState.not_quasiBernoulli`, `System.IsEquilibriumState.not_isBernoulli`, `IsBernoulli.map_group`, `not_isBernoulli_of_map_group`, `System.IsEquilibriumState.not_isBernoulli_of_two_block` | `GibbsProperties`, `BernoulliGrouping`, `TwoBlockNormalisation` | **done**, from the Gibbs bounds alone, for every proximal box-like tuple with rotations; the forms for the equilibrium state take `EquilibriumGibbsStatement`, which holds; the route of the prose through `𝖠²` is also formalised |
| `thm:bernoulli_equilibrium` and `s ≥ 2` in `sec:normalisation` (tex lines 2376 to 2395): `φ^s = |det|^{s/2}`, `P(𝖠, s) = log ∑_i |det A_i|^{s/2}`, the equilibrium state is Bernoulli | `svf_of_two_le`, `System.pressure_of_two_le`, `System.lyapunov₁_add_lyapunov₂`, `System.IsEquilibriumState.log_sum_eq`, `entropy_le_blockEntropy_one`, `measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq`, `blockEntropy_one_add_sum_le`, `System.IsEquilibriumState.eq_bernoulli` | `PressureLarge`, `BernoulliEntropy`, `BernoulliEquilibrium` | **done**, for every box-like tuple, with no literature hypothesis |
| `eq:variational`, `\dim_L ≤ dimaff`, `\dim_L = dimaff` for an equilibrium state at `dimaff` | `System.entropy_add_energyLim_le_pressure`, `add_energy_lyapDim`, `System.pressure_lyapDim_nonneg`, `System.lyapDim_le_dimaff`, `System.IsEquilibriumState.lyapDim_eq_dimaff` | `Variational`, `AffinityMain` | **done** |
| `thm:main1` with `s = dimaff(X) < 2` | `System.main1_dimaff` | `AffinityMain` | **done**; hypotheses: the four of `System.main1` |
| `dim(π_*μ) ≤ \dim_H(X)`, the use of `eq:dimension_measure_def` in `thm:main2` | `IsExactDim.le_dimH`, `IsExactDim.le_dimH_of_map`, `System.le_dimH_attractor` | `MassDistribution`, `AffinityMain` | **done**, by the mass distribution principle |
| `φ^s(A_{𝐢|_n}) = max{exp S_n f_{1,s}(τ𝐢), exp S_n f_{2,s}(τ𝐢)}`, `eq:lyapunov_exp_for_psi` | `System.svf_matWord_futureWord`, `System.abs_gDeriv_futureWord` | `Variational` | **done** |
| `Φ^(2)`, `𝖠²`, `g^{(2)}_{(i,j),c} = g_{i,c} ∘ g_{j,c+o(i)}` (`thm:two-block-normalisation`) | `System.sq`, `System.sq_mat`, `System.sq_phi`, `System.sq_g` | `SecondIterate` | **done** |
| `Δ_n^{Ψ^(2)} ≥ Δ_{2n}^Ψ`, projective exponential separation passes to `Φ^(2)` | `System.gap_two_mul_le_gap_sq`, `System.gap_anti`, `System.projExpSeparation_iff_frequently`, `System.ProjExpSeparation.sq` | `SecondIterate` | **done** |
| `thm:two-block-normalisation`: `β`, `π^(2) ∘ β = π`, `P(𝖠², t) = 2P(𝖠, t)`, `h_0(μ^(2)) = 2h_0(μ)`, `λ_i(𝖠², μ^(2)) = 2λ_i(𝖠, μ)`, `π^(2)_*μ^(2) = π_*μ`, `μ^(2)` an equilibrium state of `𝖠²` | `group`, `System.proj_sq_group`, `System.pressure_sq`, `entropy_map_group`, `System.lyapunov₁_sq_map_group`, `System.lyapunov₂_sq_map_group`, `System.marginal_sq_map_group`, `System.sq_withRotations`, `System.IsEquilibriumState.map_group` | `Grouping`, `General` | **done** |
| `thm:two-block-normalisation`: uniqueness of `μ^(2)` | `System.unique_sq_equilibrium` | `NoSeparation` | **done**, for every box-like tuple with rotations and `s > 0`, with no literature hypothesis: `𝖠²` has rotations (`System.unique_of_withRotations`). Ergodicity of `μ^(2)` is proved from `thm:eq_state_is_sum` inside `System.main_extended_lt_two'` |
| `thm:two-block-normalisation`, assembled, and its consequences (tex lines 2349 to 2351) | `System.two_block_normalisation`, `System.two_block_normalisation_consequences`, `System.Proximal.sq_hasProximalDiagonal`, `System.sq_irreducible`, `System.map_proj_sq_map_group` | `TwoBlockNormalisation` | **done**; the uniqueness and ergodicity of `μ^(2)` come from `thm:irred_eq_state` for `𝖠²`, which has rotations, with no literature hypothesis (`System.unique_of_withRotations`, `System.IsEquilibriumState.ergodic_of_withRotations`) |
| invertible linear changes of coordinates preserve the pressure, the Lyapunov exponents and the dimensions of planar sets and measures (tex lines 2352 to 2353) | `MatrixTuple.conj`, `MatrixTuple.comparable_conj`, `MatrixTuple.Comparable.pressure_eq`, `PlanarSystem.ConjBy.dimH_attractor`, `PlanarSystem.ConjBy.isExactDim_iff`, `PlanarSystem.ConjBy.isEquilibriumState_iff`, `System.dimaff_eq_of_conjBy` | `Planar/ChangeOfBasis` | **done** |
| `eq:energy_def`, `eq:diml_min2` | `energy`, `lyapDim`, `lyapDim_eq` | `LyapunovDim` | **done**, as functions of real parameters `h_0`, `λ_1`, `λ_2` |
| threshold `h_0 < -λ_2 ↔ s < 2 - λ_1/λ_2` (proofs of `thm:main1`, `thm:main2`) | `entropy_lt_iff`, `entropy_le_iff` | `LyapunovDim` | **done** |
| `thm:main1` from `thm:eq_state_proj_dim`: the dichotomy | `min_ne_min_iff`, `min_eq_one_of_le` | `LyapunovDim` | **done** |
| `eq:main_extended1`, `eq:main_extended2` | `ledrappierYoung_small`, `ledrappierYoung_large`, `entropy_lt_of_lt_two` | `LyapunovDim` | **done** |
| pointwise dimension, exact- and double-dimensional measures | `HasLocalDim`, `IsExactDim`, `IsDoubleDim`, `HasLocalDim.unique` | `MeasureDim` | **done**, with closed balls and `Measure.real` |
| `thm:exact-dimensional-mixture` | `IsExactDim.ae_hasLocalDim_add_left`, `IsExactDim.ae_hasLocalDim_add_right`, `IsExactDim.isDoubleDim_add`, `IsExactDim.measure_hasLocalDim_add_left_pos`, `IsExactDim.measure_hasLocalDim_add_right_pos`, `isExactDim_add_iff` | `MeasureDim` | **done**, from `Besicovitch.ae_tendsto_rnDeriv` |
| `eq:restricted-projection-dimensions` | `ae_hasLocalDim_iff_of_le`, `IsExactDim.of_le` | `MeasureDim` | **done** |
| `\overline{\dim}_p`, `\underline{\dim}_H` of measures | `upperLocalDim`, `lowerLocalDim`, `upperPackingDim`, `lowerHausdorffDim`, `IsDoubleDim.upperPackingDim_eq`, `IsDoubleDim.lowerHausdorffDim_eq` | `MeasureDimBounds` | **done**, real-valued; on `ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere |
| `eq:haus_dim_sum` | `upperPackingDim_add`, `lowerHausdorffDim_add`, `IsExactDim.upperPackingDim_add`, `IsExactDim.lowerHausdorffDim_add`, `upperPackingDim_add_of_finiteDimensional` | `MeasureDimBounds`, `LocalDimBounds`, `Aligned/MeasureDimSets` | **done**, also by the set-based argument of tex lines 2674 to 2685; on a finite-dimensional space the first line holds for all finite Borel measures, the second needs non-zero measures |
| pointwise dimensions of a finite Borel measure on `ℝ^d` lie in `[0, d]`; exact-dimensional iff `\overline{\dim}_p = \underline{\dim}_H`, both directions (tex lines 2686 to 2687); double-dimensional iff the pointwise dimension takes only these two values (tex lines 2687 to 2688) | `upperLocalDim_nonneg`, `lowerLocalDim_nonneg`, `ae_upperLocalDim_le`, `ae_upperLocalDim_le_one`, `ae_upperLocalDim_le_two`, `IsExactDim.dim_mem_Icc`, `IsDoubleDim.dim_mem_Icc`, `isExactDim_iff_upperPackingDim_eq_lowerHausdorffDim`, `isDoubleDim_iff_upperPackingDim_lowerHausdorffDim` | `MeasureDimBounds`, `LocalDimBounds`, `Aligned/MeasureDimSets` | **done**; the lower bound `0` holds everywhere, the upper bound `d` almost everywhere; the equivalence needs `μ ≠ 0` |
| `eq:dimension_measure_def`, second line | `ofReal_lowerHausdorffDim_le_dimH`, `heavyBallSet`, `dimH_heavyBallSet_le`, `ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional`, `lowerHausdorffDim_eq_toReal_iInf_dimH` | `LocalDimBounds` | **done**, for a non-zero finite Borel measure on a finite-dimensional space |
| `eq:dimension_measure_def`, first line | `le_upperBoxDim_of_measure_pos`, `le_packingDim_of_measure_pos`, `ofReal_upperPackingDim_le_packingDim`, `exists_packingDim_le`, `ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional`, `upperPackingDim_eq_toReal_iInf_packingDim` | `PackingDimMeasure` | **done**, for every finite Borel measure on `ℝ^d`, including the zero measure; no literature input |
| `\overline{\dim}_p(μ + ν) ≥ \overline{\dim}_p(μ)` through `eq:dimension_measure_def` (tex lines 2674 to 2677) | `upperPackingDim_le_of_absolutelyContinuous` | `PackingDimMeasure` | **done**, as the article argues |
| `thm:feng1`: the first part for every planar self-affine set, both parts at the article's scope | `PlanarFengLedrappierYoung`, `PlanarSystem.feng1`, `planar_feng1`, `PlanarFengLedrappierYoung.fengLedrappierYoung`, `planarFengLedrappierYoung_of_fengXi`, `FengLedrappierYoung`, `FengLedrappierYoungBar` | `LiteraturePlanarFeng`, `Planar/FengOne`, `LiteratureFeng` | cited: hypothesis `PlanarFengLedrappierYoung`; the box-like `FengLedrappierYoung` follows from it, `FengLedrappierYoungBar` follows from `FengLedrappierYoung` (next row), and the source statement for Feng's partitions implies the transcription |
| `thm:feng1`: the second part from the first, for the projective system of every box-like system | `isExactDim_of_map_prodMk_zero`, `System.projectiveLineSystem`, `System.proj_projectiveLineSystem`, `System.map_proj_projectiveLineSystem`, `System.lyapunov₁_projectiveLineSystem`, `System.lyapunov₂_projectiveLineSystem`, `System.sigmaOmega_projectiveLineSystem`, `System.slowAxis_projectiveLineSystem`, `System.xi_two_projectiveLineSystem`, `System.dimEntropy_projectiveLineSystem`, `System.isExactDim_map_projBar_of_fengLedrappierYoung`, `fengLedrappierYoungBar_of_fengLedrappierYoung` | `ProjectiveLineSystem` | **done**, from `FengLedrappierYoung`, through the planar system `z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` on the horizontal axis; neither rotations nor proximality are assumed |
| measurability of `τ`, `ω`, `\overline{π}`, `π` | `measurable_tau`, `measurable_omega`, `System.Bounds.measurable_projBar`, `System.Bounds.measurable_proj` | `Measurable` | **done** |
| `H_μ(𝒫_0^{n-1})`, `h_0(μ)`, existence of the limit | `cylinder`, `blockEntropy`, `entropy`, `blockEntropy_add_le`, `tendsto_entropy` | `Entropy` | **done** |
| `λ_1`, `λ_2`, `\overline{λ}`, `Λ`, `eq:eq_state_def`, `f_{1,s}`, `f_{2,s}`, Gibbs measures, the marginals | `System.lyapunov₁`, `System.lyapunov₂`, `System.lyapBar`, `System.energyLim`, `System.IsEquilibriumState`, `System.potential₁`, `System.potential₂`, `IsGibbs`, `System.marginal` | `Thermodynamic` | **done** (definitions); `λ_1`, `λ_2`, `Λ`, `h_0` are literal limits and `eq:eq_state_def` is literal |
| existence of the limits defining `λ_1`, `λ_2`, `Λ`; `-∞ < λ_2 ≤ λ_1 < 0` | `System.tendsto_lyapunov₁`, `System.tendsto_lyapunov₂`, `System.tendsto_energyLim`, `System.lyapunov₁_neg`, `System.lyapunov₂_le_lyapunov₁`, `System.RatioLowerBound.log_le_lyapunov₂` | `Lyapunov` | **done**, by Fekete |
| the Lyapunov exponents of an arbitrary invertible tuple and of a planar self-affine set (tex lines 1572 to 1582) | `MatrixTuple.lyapunov₁`, `MatrixTuple.lyapunov₂`, `MatrixTuple.tendsto_lyapunov₁_of_det_ne_zero`, `MatrixTuple.tendsto_lyapunov₂_of_det_ne_zero`, `MatrixTuple.lyapunov₂_le_lyapunov₁_of_det_ne_zero`, `PlanarSystem.lyapunov₁_neg` | `MatrixTuple`, `Planar/Lyapunov` | **done**; the manuscript explicitly assumes `‖A_i‖ < 1` when asserting `λ_1 < 0` |
| `eq:energy_def` | `System.energyLim_eq`, `System.IsEquilibriumState.pressure_eq`, `System.IsEquilibriumState.of_pressure_eq` | `Lyapunov` | **done** |
| `\overline{λ}` as the limit of `sec:lyapunov_exponents` equals `∫ f_{1,1} dν` | `System.lyapBarLim`, `System.lyapBarLim_eq` | `Lyapunov` | **done** |
| `P_Z(f)` (tex lines 2484 to 2487), the existence of its limit, the Gibbs constant is `P_Z(f)` | `periodicPoints`, `bijOn_block_periodicPoints`, `periodicSum_eq_finsum`, `pressureZ`, `tendsto_pressureZ`, `tendsto_pressureZ_admissibleSum`, `periodicSum_eq_zero_of_odd`, `pressureZ_comp_flipSymbol`, `IsGibbsAt.pressure_eq`, `IsGibbs.pressure_eq` | `PressureZ` | **done**, literal to the article; the limit over periodic points needs a diagonal generator |
| `P_Z(f)` and Gibbs measures for Hölder potentials, the Gibbs constant is `P_Z(f)`, uniqueness of the ergodic Gibbs measure (tex lines 2480 to 2503) | `IsGibbsPotential`, `IsGibbsPotential.pressure_eq_of_isHolder`, `IsGibbsPotential.eq_of_ergodic_of_isHolder`, `IsGibbs.eq_of_ergodic` | `Support/HolderPressure`, `Support/GibbsUniqueness` | **done** |
| existence of an ergodic Gibbs measure for every Hölder potential on the mixing `Σ_Z` (Bowen's theorem, cited from Sarig in `sec:gibbs_measures`): partition sums, periodic-orbit measures, the limit, ergodicity | `le_mul_of_superadditive`, `periodicPartition`, `HasBoundedDistortion.exists_admissibleSumPot_le`, `HasBoundedDistortion.exists_periodic_cylinder_bounds`, `periodicMeasure`, `measurePreserving_periodicMeasure`, `GibbsUpTo`, `exists_gibbsUpTo_periodic`, `isClosed_setOf_gibbsUpTo`, `exists_isGibbsPotential_of_forall_gibbsUpTo`, `IsGibbsPotential.quasiBernoulli_cylinder`, `IsGibbsPotential.quasiBernoulli_invariant`, `IsGibbsPotential.ergodic`, `IsGibbsPotential.ergodic_of_isHolder`, `bowenGibbsExistence`, `existsUnique_ergodic_isGibbsPotential` | `Bowen/Defs`, `Bowen/PartitionBounds`, `Bowen/PeriodicMeasures`, `Bowen/Limit`, `Bowen/Ergodic`, `Bowen/Main` | **done**, with no literature input, when both orientations occur: `e^{nP} ≤ A_n ≤ K e^{nP}` for the partition sums, the weighted periodic-orbit measures satisfy the Gibbs bounds up to every length with one constant, a weak-star limit point is an invariant Gibbs measure, and an invariant Gibbs measure is ergodic by a quasi-Bernoulli lower bound |
| doubling of Gibbs measures (tex lines 2493 to 2501) | `IsGibbsWith`, `IsGibbsWith.measureReal_cylinder_le_succ`, `IsGibbsWith.doubling`, `IsGibbs.doubling`, `IsGibbsWith.measureReal_preimage_shift_cylinder_le`, `symDist`, `symBall`, `IsGibbsPotential.doubling`, `IsGibbs.doubling_symBall` | `GibbsProperties`, `Support/GibbsDoubling` | **done**, as the inequality of cylinder measures with its extension to the left, and as the doubling of the balls of the standard metric of the two-sided shift |
| `thm:eq_state_is_sum`: the four decompositions, `λ_1(𝖠, μ) = \overline{λ}(𝖠, μ_1)`, `λ_2(𝖠, μ) = \overline{λ}(𝖠, μ_2)` | `System.GibbsDecomposition`, `FraserJordanJurgaDecomposition`, `fraserJordanJurgaDecomposition_holds`, `System.gibbsDecomposition_map_unCode`, `System.exists_gibbsDecomposition_of_lyapunov` | `Thermodynamic`, `Literature`, `FraserJordanJurga/Main` | **done**, with no literature input, for every box-like system with rotations and `0 < s < 2`; the hypothesis `S.HasProximalDiagonal` of the predicate is not used |
| `thm:eq_state_is_sum`: the ergodic `s`-Gibbs measures `μ_1` and `μ_2 = flip_*μ_1` on `Σ_Z`, the Gibbs bounds of `q_*μ_1` | `System.exists_isGibbs_potential₁`, `System.isGibbs_potential₂_map_flipAxis`, `ergodic_map_flipAxis`, `ergodic_map_unCode`, `System.exists_isGibbsWith_pressure`, `System.hasGibbsBounds_map_unCode` | `FraserJordanJurga/Gibbs` | **done**, from Bowen's theorem; each word has the two lifts `τ(𝐢)|_n`, `ω(𝐢)|_n`, and `φ^s(A_w)` is the larger of the two exponentials (tex lines 2565 to 2570) |
| `thm:eq_state_is_sum`: every invariant measure with the Gibbs bounds equals `q_*μ_1`; the four decompositions of `q_*μ_1` | `System.measureReal_cylinder_le_of_hasGibbsBounds`, `System.eq_of_hasGibbsBounds`, `System.eq_map_unCode_of_hasGibbsBounds`, `preimage_flipAxis_range_tau`, `preimage_flipAxis_range_omega`, `restrict_range_tau_add_restrict_range_omega`, `map_unCode_eq_tau`, `map_unCode_eq_omega`, `map_unCode_eq₁`, `map_unCode_eq₂` | `FraserJordanJurga/Decomposition`, `FraserJordanJurga/Main` | **done**; an invariant measure with the Gibbs bounds is absolutely continuous with respect to the ergodic `q_*μ_1` and equals it; the decompositions follow from `Σ_Z = τ(Σ) ⊔ ω(Σ)` and the exchange of `τ(Σ)` and `ω(Σ)` by the exchange of the axes |
| `thm:eq_state_is_sum`: `λ_1(𝖠, q_*μ_1) = \overline{λ}(𝖠, μ_1)`, `λ_2(𝖠, q_*μ_1) = \overline{λ}(𝖠, flip_*μ_1)` | `integral_comp_apply_natCast`, `System.lyapunov_map_unCode_eq_max_min`, `System.lyapBar_map_flipAxis_le_of_isGibbs`, `System.lyapunov_map_unCode_of_isGibbs` | `FraserJordanJurga/Lyapunov` | **done**, for every box-like system and every ergodic Gibbs measure of `f_{1,s}` carried by `Σ_Z`, `0 < s < 2`; the rotations are not used. Birkhoff's theorem along the two lifts gives the maximum and the minimum of `\overline{λ}(𝖠, μ_1)`, `\overline{λ}(𝖠, μ_2)`, and the non-negativity of the relative entropy of the cylinder partitions orders them |
| `thm:eq_state_is_sum`: `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` | `System.svfSum_le_admissibleSum`, `System.pressure_eq_pressureZ₁`, `System.pressure_eq_pressureZ₂` | `PressureZ` | **done**, for every box-like system with a diagonal generator and `0 < s < 2`, with no literature hypothesis |
| `thm:eq_state_is_sum`: the integral formulas for `λ_1`, `λ_2`, `μ_2 = flip_*μ_1`, the Gibbs constants are `P(𝖠, s)`, the fourth decomposition follows from the other three | `System.GibbsDecomposition.lyapunov₁_eq_integral`, `System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂`, `System.GibbsDecomposition.lyapunov₂_eq_integral`, `System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂`, `System.GibbsDecomposition.map_flip`, `System.GibbsDecomposition.isGibbsAt₁`, `System.GibbsDecomposition.isGibbsAt₂`, `System.decomposition₂_of_decompositions` | `PressureZ` | **done**, from the decompositions, with no literature hypothesis |
| `μ_1 ≠ μ_2`, `μ_1 ⟂ μ_2` (tex lines 2581 to 2594), `eq:tau_cylinder`, `\overline{τ}_*μ_1 = \overline{ω}_*μ_2` and `\overline{τ}_*μ_2 = \overline{ω}_*μ_1` (tex lines 2606 to 2607), absolute continuity (tex lines 2634 to 2636) | `System.not_isGibbs_potential₁_and_potential₂`, `System.GibbsDecomposition.ne`, `mutuallySingular_of_ergodic_of_ne`, `System.GibbsDecomposition.mutuallySingular`, `cylinder_tau_inter_subshift`, `System.GibbsDecomposition.map_tau_eq_map_omega`, `System.GibbsDecomposition.map_absolutelyContinuous` | `GibbsProperties` | **done**, with no literature hypothesis; `eq:tau_cylinder` needs `n ≥ 1` |
| `f_{1,2} = f_{2,2}` and the Gibbs measures coincide at `s = 2` (tex line 2637) | `System.potential₁_two`, `System.potential₂_two`, `System.potential₁_two_eq_potential₂_two`, `System.GibbsDecomposition.mu₁_eq_mu₂_of_two` | `Support/PotentialsAtTwo` | **done**, with the formula of the case `1 ≤ s < 2` |
| `thm:entropy_eq_gibbs` | `blockEntropy_map_unCode`, `entropy_map_unCode`, `map_unCode_of_decomposition`, `System.GibbsDecomposition.entropy_eq₁`, `System.GibbsDecomposition.entropy_eq₂` | `EntropyFactor`, `Main` | **done** |
| `eq:proj_eq_is_sum`, `eq:gibbs_proj_dim`, normalised tuple | `map_comp_coding`, `System.exists_decomposition_of_coding`, `System.marginal_decomposition_normalised` | `Main` | **done**; hypotheses: `JordanRapaportDimension`, and for the normalised tuple also `EquilibriumGibbsStatement` and `FraserJordanJurgaDecomposition`, which hold |
| `eq:proj_eq_is_sum`, `eq:gibbs_proj_dim` for every proximal mixed tuple | `System.marginal_decomposition` | `General` | **done** |
| `eq:simple_lyapunov` (tex lines 2362 to 2373); Morris–Shmerkin, Lemma 3.4 | `morrisShmerkinLyapunov_holds`, `System.IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_withRotations`, `System.IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds`, `System.IsEquilibriumState.isBernoulli_of_lyapunov_eq`, `System.IsEquilibriumState.eq_bernoulli_of_lyapunov_eq`, `abs_det_rpow_le_svf`, `System.log_sum_abs_det_rpow_le_pressure`, `morrisShmerkinLyapunov_of_equilibriumGibbs`, `System.simple_lyapunov` | `MorrisShmerkin`, `General` | **done**, with no literature input, for every proximal box-like tuple with rotations: Lemma 3.4 (an equilibrium state with `λ_1 = λ_2` is Bernoulli, by Gibbs' inequality, for every `s ≥ 0`), Lemma 3.5 (`System.not_isBernoulli`) and the Gibbs bounds of `equilibriumGibbs`; `MorrisShmerkinLyapunov` holds. `System.simple_lyapunov` derives the inequality from `MorrisShmerkinLyapunov`, through `𝖠²` when no generator is proximal |
| `thm:eq_state_proj_dim` | `System.eq_state_proj_dim`, `System.eq_state_proj_dim_of_two_le`, `System.eq_state_proj_dim_all` | `General`, `ProjectionLarge` | **done** for every `s > 0`, in the article's form with `\overline{\dim}_p` and `\underline{\dim}_H`; hypotheses: `JordanRapaportDimension`, and `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, which hold; for `s ≥ 2` only `JordanRapaportDimension` |
| the orientation lift `(τ_*μ + ω_*μ)/2` of a Bernoulli measure in the proof of `thm:eq_state_proj_dim` for `s ≥ 2` (tex lines 2855 to 2872): stationary Markov measure, mixing, ergodic, `\overline{h}_0 = h_0`, `λ_1 = λ_2`, projection `(ν_x + ν_y)/2` | `orientationLift`, `orientationLift_bernoulli_cylinder`, `tendsto_bernoulli_parity`, `tendsto_orientationLift_bernoulli_cylinder_inter`, `ergodic_orientationLift_bernoulli`, `entropy_orientationLift`, `System.lyapunov_eq_of_ergodic_orientationLift`, `System.map_projBar_orientationLift`, `System.IsEquilibriumState.lyapunov_eq_of_two_le`, `System.isExactDim_marginal_of_two_le` | `OrientationLift`, `ProjectionLarge` | **done**; the final dimension takes `JordanRapaportDimension` |
| `thm:main1` | `System.main1`, `System.main1_of_two_le`, `System.main1_all`, `System.main1_dimaff_all` | `General`, `MainOneFull` | **done** for every affinity parameter and every invariant equilibrium state; hypotheses: `JordanRapaportDimension`, and `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, which hold; for `s ≥ 2` only `JordanRapaportDimension` |
| the remark before `thm:eq_state_proj_dim`: the coordinate marginals are double-dimensional without separation | `System.exists_exactDim_decomposition_of_coding`, `System.marginal_isDoubleDim_normalised`, `System.marginal_isDoubleDim` | `NoSeparation` | **done**, for every proximal box-like tuple with rotations and `0 < s < 2`; hypotheses: `FengHuExactDim`, and `EquilibriumGibbsStatement` and `FraserJordanJurgaDecomposition`, which hold |
| `ex:projection_double_dimensional` | `PrescribedExample.projection_double_dimensional`, `PrescribedExample.projection_double_dimensional_of_geometry`, `PrescribedExample.existsUnique_p`, `PrescribedExample.pressure_eq`, `PrescribedExample.exists_geometry`, `PrescribedExample.exists_translation`, `PrescribedExample.volume_badSet_le`, `PrescribedExample.equilibrium_spec`, `PrescribedExample.Gibbs.isEquilibriumState_spec`, `PrescribedExample.Gibbs.marginal_spec` | `PrescribedExample` | **done** for every `0 < s_2 < s_1 ≤ 1`; hypotheses: `JordanRapaportDimension`, and `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, which hold, through the Gibbs bounds and `thm:eq_state_proj_dim`; `FengKaenmakiUnique` is not used |
| the separate rational two-map system: `thm:main1`, `thm:main2` for `0 < s ≤ 1`; the common-prefix bound for `Δ_n^Ψ`; `P(𝖠, s) = log ρ` for a positive eigenvector | `System.main1_of_le_one`, `System.main2_of_le_one`, `System.le_gap`, `System.projExpSeparation_of_le_abs`, `System.pressure_le`, `System.transfer`, `System.pressure_eq_log_of_eigenvector` | `Example` | **done** |
| Birkhoff's pointwise ergodic theorem, maximal ergodic theorem | `birkhoff_ae`, `birkhoff_ergodic`, `maximal_ergodic` | `Birkhoff` | **done** |
| `sec:conditional`: `\widehat{ξ}`, conditional measures, Rokhlin's properties | `saturated`, `saturated_eq_comap`, `condMeas`, `setLIntegral_condMeas`, `condMeas_unique`, `condMeas_atom` | `Conditional`, `ConditionalMeasures` | **done**, with `condExpKernel` on a standard Borel space |
| `thm:conditional_measures_of_a_conditional_measure`, `thm:double_conditional`, `thm:finer_partition_dirac_mass` | `condMeas_cond`, `condMeas_cond_of_saturated`, `double_conditional`, `finer_partition_dirac_mass` | `ConditionalLemmas` | **done** |
| conditional information and entropies, `eq:ergodic_entropy_constant` | `condInfo`, `condEntropy`, `localEntropy`, `integrable_condInfo`, `localEntropy_ae_eq` | `Conditional`, `ConditionalMeasures` | **done** |
| `Σ'`, `Σ^τ`, `Σ^ω`, `eq:tau_omega_partition2`, `thm:lyapunov_exponents_via_g_system` | `System.SigmaPrime`, `System.SigmaTau`, `System.SigmaOmega`, `System.slowAxis`, `System.lyapunov_exponents_via_g_system` | `SlowAxis` | **done**; `Σ'` in the box-like form, no Oseledets |
| the article's `Σ'` and Oseledets filtration (tex lines 1585 to 1630), its existence for box-like tuples, `thm:lyapunov_exponents_via_g_system` for every choice | `MatrixTuple.OseledetsSet`, `System.oseledetsSet`, `System.V_one_eq_axis`, `System.V_eq_oseledetsSub`, `System.sigmaTau_ae_eq`, `System.sigmaOmega_ae_eq`, `System.lyapunov_exponents_via_g_system_oseledets`, `System.lyapunov_exponents_via_g_system_manuscript` | `OseledetsFiltration` | **done**, by the prose proof; the rate-defined `Σ^τ`, `Σ^ω` agree with the article's modulo null sets |
| the partitions of the article's and of Feng's `Σ'` compared with the box-like ones (tex lines 1854 to 1871) | `condMeas_ae_eq_of_cut`, `System.fengXi`, `System.condMeas_fengXi_ae_eq`, `System.infoSum_fengXi_iff`, `System.condMeas_oseledetsXi_ae_eq`, `System.condEntropy_oseledetsXi_eq`, `PlanarSystem.condMeas_fengXi_ae_eq`, `PlanarSystem.infoSum_fengXi_iff` | `OseledetsBridge`, `Planar/FengPartitions` | **done**: almost everywhere equal conditional measures, hence equal entropies and equivalent information-sum identities |
| Oseledets' theorem for invertible planar cocycles (tex lines 1585 to 1607): the regular set `Σ'`, the filtration and `eq:V_lyapunov`, Furstenberg–Kesten, the convergence of the slow directions, `μ(Σ') = 1` | `MatrixTuple.regularSet`, `MatrixTuple.slowLine`, `MatrixTuple.filtration`, `MatrixTuple.image_slowLine`, `MatrixTuple.tendsto_log_norm_pastProd`, `MatrixTuple.tendsto_log_alpha₂_pastProd`, `MatrixTuple.exists_slow_fast_of_tendsto`, `MatrixTuple.ae_mem_regularSet`, `MatrixTuple.measure_regularSet_compl_of_ergodic`, `MatrixTuple.oseledetsSetOfErgodic`, `PlanarSystem.measure_SigmaPrime_compl_of_ergodic` | `Planar/Oseledets`, `FurstenbergKesten`, `Planar/OseledetsTheoremDirection`, `Planar/OseledetsTheorem` | **done**, with no literature input, from Kingman's theorem |
| Kingman's subadditive ergodic theorem | `IsSubadditiveCocycle`, `kingman_ae`, `kingman_ergodic`, `kingman_ergodic_of_tendsto`, `tendsto_pastWord_of_subadditive` | `Kingman`, `FurstenbergKesten` | **done**, from Birkhoff's theorem by the stopping-time method of Katznelson–Weiss and Steele |
| the partitions and entropies of `sec:entropies` for a planar self-affine set and their box-like specialisation (tex lines 1853 to 1906) | `PlanarSystem.SigmaPrime`, `PlanarSystem.xi`, `PlanarSystem.dimEntropy`, `System.toPlanar_SigmaPrime`, `System.toPlanar_xi`, `System.toPlanar_dimEntropy` | `Planar/Partitions`, `Planar/Specialisation` | **done** |
| partitions `ξ_i`, `ξ_1^⊥`, `\overline{ξ}_i`; measurable (Feng, Lemma 4.2); `h_i`, `\overline{h}_i`; `\overline{μ}` | `System.xi`, `System.xiPerp`, `System.xiBar`, `System.isMeasurablePartition_xi`, `…_xiPerp`, `…_xiBar`, `System.dimEntropy`, `System.dimEntropyBar`, `avgMeasure` | `DimPartitions`, `MeasurablePartitions` | **done** |
| `eq:sigma_tau_omega_positive_eq_measure1`, `thm:partitions_xi1`, `thm:partition_tau_conj` | `System.shift_mem_SigmaTau_iff`, `System.partitions_xi1`, `System.partition_tau_conj` | `PartitionIdentities` | **done** |
| ergodicity of the equilibrium state | `System.ergodic_of_gibbsDecomposition`, `System.ergodic_of_hasProximalDiagonal`, `System.IsEquilibriumState.ergodic_of_two_le`, `System.IsEquilibriumState.ergodic_of_withRotations` | `DimPartitions`, `BernoulliEquilibrium`, `EquilibriumGibbs` | **done**; for `0 < s < 2` from `thm:eq_state_is_sum` (hypotheses `EquilibriumGibbsStatement` and `FraserJordanJurgaDecomposition`, which hold), for `s ≥ 2` from the Bernoulli form, and for every `s > 0` from `thm:irred_eq_state` for tuples with rotations; no citation of ergodicity is used |
| `μ(Σ') = 1`, `eq:lyapunov_exponent_gsystem`, `thm:sigma_tau_omega_positive_eq_measure` | `System.measure_SigmaPrime_compl`, `System.lyapunov_exponent_gsystem`, `System.sigma_tau_omega_positive`, `System.sigma_tau_omega_positive_eq_measure` | `SigmaMeasure`, `Aligned/SigmaTauOmega` | **done**; `thm:sigma_tau_omega_positive_eq_measure` for every box-like tuple with rotations by the counting argument of the prose, with the integrated bound as a second proof; proximality is not used |
| `thm:gibbs_tau_omega_positive`, `eq:orientation-restrictions` | `System.gibbs_tau_omega_positive`, `System.orientation_restrictions` | `GibbsOrientation` | **done** |
| `h_0(μ) = h(μ)`, `\overline{h}_0(ν) = h(ν)` (tex lines 1989 to 1991) | `integral_sum_negMulLog_condExp_past`, `System.dimEntropy_zero_eq_entropy`, `System.dimEntropyBar_zero_eq_entropy`, `System.dimEntropy_zero_eq_ksEntropy`, `System.dimEntropyBar_zero_eq_ksEntropy` | `PastEntropy`, `CylinderEntropy` | **done**, for the entropy rate by the chain rule, Lévy's upward theorem and Cesàro averaging, and for the Kolmogorov–Sinai entropy through the generator theorem |
| `thm:feng_entropy_as_limit`, `thm:feng_entropy_zero` | `System.feng_entropy_as_limit`, `…_bar`, `System.feng_entropy_zero`, `…_bar`, `feng_entropy_as_limit_boxLike_holds`, `feng_entropy_zero_boxLike_holds`, `feng_entropy_as_limit_general`, `feng_entropy_zero_general` | `FengEntropy`, `Planar/FengEntropy`, `Planar/FengIdentity`, `Planar/FengGeneral` | **done**, for every planar self-affine set, from Feng's identity and Birkhoff's theorem, with `μ(Σ') = 1` from the planar Oseledets theorem |
| Feng, Lemma 4.6, first identity of (4.16), for the box-like, the projective and the planar partitions | `refineZero`, `pullShift`, `condMeas_refineZero`, `condMeas_pullShift`, `condMeas_cylinder_eq_prod`, `infoSum_of_pullShift`, `System.infoSum_xi`, `System.infoSum_xiBar`, `PlanarSystem.infoSum_xi`, `fengInfoSum_holds`, `fengInfoSumBar_holds` | `FengIdentity`, `FengIdentityBar`, `Planar/FengIdentity` | **done**, along Feng's Lemmas 4.4 and 4.5, with neither ergodicity nor his (4.7); `FengInfoSum` and `FengInfoSumBar` hold |
| `thm:feng_entropy_kolmogorov_sinai` | `System.feng_entropy_kolmogorov_sinai`, `System.feng_entropy_kolmogorov_sinai_bar`, `System.feng_entropy_kolmogorov_sinai_toPlanar`, `PlanarSystem.feng_entropy_kolmogorov_sinai_of_oseledetsSet`, `PlanarSystem.feng_entropy_kolmogorov_sinai_general`, `PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_ergodic` | `CylinderEntropy`, `Planar/CylinderEntropy`, `Planar/OseledetsTheorem` | **done**, for every planar self-affine set, by Feng's (4.17) route through the Shannon–McMillan–Breiman theorem |
| the Shannon–McMillan–Breiman theorem (tex lines 1973 to 1977): Maker's theorem, the informations of the finite pasts, Chung's maximal inequality, the theorem for every invariant measure, typical words | `maker_ae`, `maker_ergodic`, `pastInfo`, `measure_inter_iUnion_pastCondProb_lt_le`, `integrable_pastInfoSup`, `tendsto_pastInfo`, `tendsto_neg_log_cylinder_localEntropy`, `tendsto_neg_log_cylinder_entropy`, `shannonMcMillanBreiman`, `ShannonMcMillanBreimanStatement`, `typicalWords` | `SMB/Maker`, `SMB/PastInformation`, `ShannonMcMillanBreiman`, `SMBStatement` | **done**, by Breiman's argument, with no literature input |
| the Kolmogorov–Sinai entropy as a supremum over finite Borel partitions and the generator theorem (tex lines 1965 to 1972) | `partEntropy`, `condPartEntropy`, `partEntropyRate`, `ksEntropy`, `partEntropyRate_le_entropy`, `isGreatest_partEntropyRate`, `ksEntropy_shift_eq_entropy`, `tendsto_neg_log_cylinder_ksEntropy` | `KolmogorovSinai` | **done**; the supremum is attained at the time-zero partition |
| `thm:conditional_two_ways` | `System.conditional_two_ways_normalised`, `condMeas_transport`, `System.conditional_two_ways` | `Aligned/ConditionalTwoWays`, `ConditionalTwoWays` | **done**, along the prose; the transport of the unnormalised restrictions is a second proof |
| `thm:overline_h1_zero`, `thm:overline_h1_zero_large` | `System.overline_h1_zero`, `System.overline_h1_zero_large` | `AverageEntropy` | **done** |
| `thm:overline_h1_large`, `thm:eq_state_h1_large` | `System.overline_h1_large`, `System.eq_state_h1_large` | `EquilibriumEntropyLarge` | **done** |
| `thm:eq_state_h1_zero`, `thm:eq_state_h2_zero`, `thm:orto_partition_dirac` | `System.eq_state_h1_zero`, `System.eq_state_h2_zero`, `System.orto_partition_dirac` | `EquilibriumEntropySmall` | **done** |
| `thm:SOSC_h2_zero` | `System.future_eq_of_proj_eq`, `System.SOSC_h2_zero` | `StrongOpenSetEntropy` | **done**, with Poincaré recurrence |
| `thm:main_extended`, `0 < s < 2` | `System.main_extended_normalised`, `System.main_extended_lt_two'`, `System.main_extended_dimaff` | `MainTwo` | **done**; hypotheses: `hjr`, `hly`, and `hlyb`, `hms`, `hfk`, `hfjj`, `hfi`, `hfib`, which hold |
| `thm:main2` under projective exponential separation | `System.main2_of_bounds`, `System.main2` | `MainTwo` | **done**: the special case deduced from the dimension of the equilibrium state, with the hypotheses of `thm:main_extended`; the upper bound is the theorem `System.dimH_attractor_le` |
| `thm:main2` along the prose (tex lines 3625 to 3738): the endpoint at two, the reduction to a proximal diagonal generator, typical words by the Shannon–McMillan–Breiman theorem with returns to horizontal orientation, the pigeonhole, the diagonal subsystems, Kittle–Kogler, the entropy threshold, strong separation in the open-set branch, past independence, the limit | `System.main2_prose`, `System.main2_prose_all`, `System.main2_noExactOverlaps_prose`, `System.StrongOpenSet.dimaff_eq_two`, `System.exists_typical_words_prose`, `exists_class_smb`, `frequently_measure_inter_shift_ge`, `log_card_le_log_card_class_add`, `System.isHomDiag_subsystem`, `System.IsHomDiag.isExactDim_map_proj`, `condEntropyPoint_eq_zero_of_le`, `System.subsystem_strongSeparation`, `System.le_dimH_attractor_of_family` | `MainTwoProse`, `MainTwoEndpoint` | **done**; hypotheses `hly`, `hkk`, and `hms`, `hfk`, `hfjj`, which hold, and the theorem `shannonMcMillanBreiman`; the scalar formula comes from `FengLedrappierYoung` on an auxiliary box-like system |
| the second proof of `thm:main2`: the typical words (tex lines 3648 to 3683): families `W_n` of diagonal words of a common length with `A_w = diag(a_n, b_n)`, `log #W_n / n → h_0(μ)`, `log |a_n| / n → λ_1`, `log |b_n| / n → λ_2` | `System.exists_typical_words_of_gibbs`, `System.exists_typical_words` | `TypicalWords` | **done**, from the Gibbs bounds of `μ_1` with `P(𝖠, s) = 0`, Birkhoff's theorem for `f_{1,1}`, `f_{2,1}`, and the pigeonhole over symbol counts; hypotheses `EquilibriumGibbsStatement` and `FraserJordanJurgaDecomposition`, which hold |
| finite subsystems `(φ_{w_k})_k` (tex lines 3685 to 3707): the system, its coordinate maps, the concatenation of words, no exact overlaps of the coordinate maps, the attractor inside `φ_v(X)`, unique coding inside a feasible open set | `System.subsystem`, `System.subsystem_mat`, `System.subsystem_phi`, `System.subsystem_g`, `flatWords`, `flatWords_injective`, `System.subsystem_phiWord`, `System.subsystem_codeWord_gWord`, `System.matWord_eq_boxMat_zero_iff`, `System.NoExactOverlaps.simWord_injective`, `System.subsystem_attractor_subset`, `System.subsystem_attractor_subset_image`, `System.exists_phiWord_image_subset`, `System.pairwise_disjoint_image_phiWord`, `System.subsystem_future_eq_of_proj_eq` | `Subsystem` | **done** |
| the Bernoulli measure `ν_n` of the subsystem (tex lines 3697 to 3705): invariance, ergodicity, `h_0(ν_n) = H_n`, `λ_i(𝖠_n, ν_n) = log |a_n|, log |b_n|`, `Σ^τ` of full measure, the coded measures `τ_*ν_n`, `ω_*ν_n` on `Σ_Z` and their projections, the stationarity of the coordinate marginals | `optionBernoulli`, `ergodic_shift_optionBernoulli`, `entropy_optionBernoulli`, `System.IsHomogeneousOption`, `System.IsHomogeneousOption.lyapunov₁_optionBernoulli`, `System.IsHomogeneousOption.lyapunov₂_optionBernoulli`, `System.IsHomogeneousOption.mem_SigmaTau_of_forall_isSome`, `System.IsHomogeneousOption.dimEntropy_zero`, `System.IsHomogeneousOption.ergodic_shift_map_tau`, `System.IsHomogeneousOption.lyapBar_map_tau`, `System.map_projBar_map_tau`, `System.IsHomogeneousOption.marginal_eq_sum` | `HomogeneousSubsystem` | **done**; the symbol `none` is an anti-diagonal word of zero weight, which makes the subsystem box-like with rotations and proximal for the scalar part of `thm:feng1` |
| Kittle–Kogler and the scalar Ledrappier–Young formula for the marginals of `ν_n` (tex lines 3702 to 3721) | `System.IsHomogeneousOption.marginal_isExactDim`, `System.IsHomogeneousOption.dimEntropyBar_map_tau`, `System.IsHomogeneousOption.dimEntropyBar_map_omega_eq_zero` | `SubsystemEntropy` | **done**; hypotheses `KittleKoglerDimension` and `FengLedrappierYoungBar`, which follows from `FengLedrappierYoung` |
| the entropies `h_1(ν_n) = q_{x,n}`, `h_2(ν_n) = 0` (tex lines 3714 to 3728) | `System.IsHomogeneousOption.dimEntropy_one_eq`, `System.IsHomogeneousOption.condMeas_xiPerp_eq_dirac`, `System.IsHomogeneousOption.dimEntropy_eq_zero_of_condMeas_xi_eq_dirac`, `System.IsHomogeneousOption.dimEntropy_two_eq_zero_of_le`, `System.IsHomogeneousOption.dimEntropy_two_eq_zero_of_unique_coding` | `SubsystemEntropy` | **done**; `h_1` by transport along `τ`, `h_2 = 0` by Dirac conditional measures transported along `ω` (hypothesis `FengInfoSumBar`) or by unique coding |
| `dim ν_n` (tex lines 3728 to 3737) and the limit `dim ν_n → s` | `subsystemDim`, `System.IsHomogeneousOption.isExactDim_map_proj`, `subsystemDim_eq_lyapDim`, `subsystemDim_div`, `tendsto_subsystemDim`, `tendsto_add_div_add`, `le_dimH_of_subsystemDim` | `SubsystemEntropy`, `MainTwoFree` | **done**; hypothesis `FengLedrappierYoung` for the planar formula |
| `thm:main2`: the trimming to `min{#W_n, ⌊|b_n|⁻¹⌋}` words, the prefix `v` with `φ_v(X) ⊆ U`, the lower bound for one family, the reduction to a proximal diagonal generator | `System.le_dimH_attractor_of_words`, `System.main2_noExactOverlaps_normalised`, `System.main2_noExactOverlaps_of_pressure`, `System.main2_noExactOverlaps` | `MainTwoFree` | **done** (second proof); hypotheses: `hly`, `hkk`, and `hlyb`, `hms`, `hfk`, `hfjj`, `hfib`, which hold |
| the example of `prop:ssc_no_overlap_not_pesc` satisfies the hypotheses of `thm:main2` (tex lines 1522 to 1525) | `NoOverlap.Params.sum_abs_det_lt_one`, `System.dimaff_lt_of_pressure_neg`, `System.dimaff_lt_two_of_sum_abs_det_lt_one`, `NoOverlap.dimH_eq_dimaff'` | `NoOverlapExample`, `MainTwoEndpoint` | **done**, with `NoOverlap.BaranyKaenmakiTheorem` and the hypotheses of `thm:main2` |
| invariant measures `ν = ∑_i p_i (φ_i)_*ν`, Hutchinson's uniqueness, invariance of the projection of a Bernoulli measure (tex lines 3570 to 3579) | `System.IsInvariantMeasure`, `System.IsInvariantMeasure.unique`, `System.IsInvariantMeasure.sum_eq_one`, `System.isInvariantMeasure_map_proj`, `System.map_proj_eq_of_isInvariantMeasure` | `SelfAffineMeasure`, `InvariantMeasure` | **done**; uniqueness among all Borel probability measures |
| `∑_i |det A_i| ≤ 1` under the strong open set condition, normalised Lebesgue measure on the open set (tex lines 3557 to 3581) | `System.volume_image_phi`, `System.StrongOpenSet.exists_isBounded`, `System.StrongOpenSet.sum_abs_det_le_one`, `System.StrongOpenSet.exists_isInvariantMeasure_isExactDim` | `LebesgueOpenSet` | **done** |
| `thm:main_extended`, `s ≥ 2` | `System.StrongOpenSet.sum_abs_det_eq_one`, `System.main_extended_ge_two` | `MainExtended` | **done**, with no literature hypothesis; rotations, proximality and the projective exponential separation condition are not used; the full `thm:main2` uses it at the endpoint |
| `thm:main_extended` | `System.main_extended`, `System.main_extended_min` | `MainExtended` | **done**; hypotheses: those of `System.main_extended_dimaff` |
| `\dim_H X = min{2, dimaff(X)}` under the hypotheses of `thm:main_extended` (paragraph after `eq:hausdorff_ergodic_lyapunov`) | `System.dimH_attractor_eq_min`, `System.dimH_attractor_of_strongOpenSet`, `System.dimH_attractor_of_two_le` | `DimensionFormula` | **done**; hypotheses: those of `thm:main_extended`, and none for `dimaff(X) ≥ 2` under the strong open set condition, with no measure assumed |
| `eq:hausdorff_ergodic_lyapunov` (Rossi) | `upperHausdorffDim`, `System.RossiBound`, `System.rossiBound`, `IsExactDim.upperHausdorffDim_eq`, `System.upperHausdorffDim_map_proj_eq` | `DimensionFormula`, `RossiBound` | **done** for every box-like system and every ergodic `μ`, with no literature input (`System.rossiBound`); no theorem takes `System.RossiBound`; equality for the equilibrium state of `thm:main_extended` **done** |
| Rossi's covering argument for `eq:hausdorff_ergodic_lyapunov`: the Furstenberg–Kesten limits along the forward products, the rectangles of the typical words and their covers by squares, the mass distribution principle | `add_energy_neg_of_lyapDim_lt`, `ae_lowerLocalDim_le_of_dimH_le`, `System.ae_tendsto_log_norm_matWord`, `System.ae_tendsto_log_alpha₂_matWord`, `System.wordRect`, `System.wordGrid`, `System.cover_cost_le`, `System.hausdorffMeasure_iInter_wordRect_le`, `System.exists_dimH_le_of_add_energy_neg`, `System.ae_lowerLocalDim_map_proj_le`, `System.essSup_lowerLocalDim_map_proj_le` | `Rossi` | **done**: for `t ≤ 2` with `h_0(μ) + Λ(𝖠, μ, t) < 0` a Borel set of full `π_*μ`-measure has Hausdorff dimension at most `t` |

## Fidelity boundary

Five kinds of assumption are kept apart. The library declares no axiom; the completed proofs
depend on `propext`, `Classical.choice` and `Quot.sound` only, and the comparator permits no other
for the headline results.

| Kind | Form in Lean |
|---|---|
| Standing assumptions of a theorem: proximal, with rotations, projective exponential separation, strong open set condition | hypotheses of the statement, as in the article |
| Literature theorems the article cites without proof | `Prop`-valued definitions in `BoxLike/Literature.lean` or `BoxLike/LiteratureFeng.lean`, in `BoxLike/LiteratureFengKaenmaki.lean` and `BoxLike/LiteraturePlanarFeng.lean` for the general forms behind `thm:irred_eq_state` and `thm:feng1`, and in `BoxLike/LiteratureRemarks.lean` when no main result depends on it, quantified over every alphabet and every system, with the exact citation in the doc comment; every result that uses one takes it as an explicit hypothesis, and `Challenge.lean` restates those the headline results take |
| Literature theorems behind claims off the main line | `Prop`-valued definitions beside the results that use them, taken as hypotheses: `NoOverlap.BaranyKaenmakiPair`, `NoOverlap.BaranyKaenmakiTheorem` in `NoOverlapExample`; `System.FraserBound`, `System.FraserROSC` in `FraserChain` and `System.RossiBound` in `DimensionFormula` have the same form and are theorems of the library |
| Proposed premises awaiting authorisation | `Prop`-valued definitions in `BoxLike/Proposals/`, each with its source, hypotheses, specialisation and degenerate-instance test; nothing outside that directory imports them. None is pending |
| Results of the article | proved, or recorded as open: Question 1.4 is the proposition `CoincidentProjectionDimensionsQuestion` with no proof; results of the article never become literature hypotheses or axioms |

A literature statement that the library proves keeps its `Prop`-valued definition: the results
that use it take it as a hypothesis, and Solution passes the proof. These are
`MorrisShmerkinLyapunov`, `FengKaenmakiGibbs`, `FengKaenmakiUnique`, `FengKaenmakiNormEquilibrium`,
`FraserJordanJurgaDecomposition`, `FengInfoSum`, `FengInfoSumBar`, `System.FalconerBoxBound`,
`System.FraserBound`, `System.FraserROSC` and `System.RossiBound`. `FengLedrappierYoungBar` keeps
its definition in the same way and follows from the cited `FengLedrappierYoung`
(`fengLedrappierYoungBar_of_fengLedrappierYoung`). The cited theorems that remain hypotheses are
`JordanRapaportDimension`, `FengLedrappierYoung`, `PlanarFengLedrappierYoung`,
`KittleKoglerDimension`, `FengHuExactDim`, `NoOverlap.BaranyKaenmakiTheorem` and
`NoOverlap.BaranyKaenmakiPair`.

Rules for a literature statement:

- It is a statement about defined objects only, never about an opaque constant, so that a
  reader can compare it with the cited theorem.
- It carries every hypothesis of the cited theorem. Lean's total functions (`x / 0 = 0`,
  `Real.log 0 = 0`, junk values of limits that do not exist) make an under-hypothesised
  transcription false in a degenerate case.
- It is tested against a degenerate instance (`N = 1`, `λ_1 = λ_2`, all translations zero)
  before it is admitted. A false statement makes every result that takes it vacuous, and
  neither the build nor the comparator shows a trace of it.
- A statement of the `Literature` modules quantifies over every alphabet `ι : Type u`
  with the instances `[Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]`, and over
  every system or tuple, as the cited theorem does. The cited theorems concern the discrete
  `σ`-algebra on the alphabet, which is the instance `MeasurableSingletonClass ι`; without it
  `MorrisShmerkinLyapunov` and `FengKaenmakiGibbs` would be false with the trivial
  `σ`-algebra on `ι`.
- A result that uses it takes it as an explicit hypothesis with the binder of the table below
  and the universe named, `(hfk : FengKaenmakiGibbs.{u})` (section 8).
- A statement that no main result depends on lives in `BoxLike/LiteratureRemarks.lean`, except
  the general forms `FengKaenmakiNormEquilibrium` and `PlanarFengLedrappierYoung`, which live in
  their own modules beside their reductions to the box-like predicates.
- A statement that a headline result takes is restated in `Challenge.lean`, whose definition
  block stays identical to `Solution/Definitions.lean`.
- New literature statements need explicit authorisation; a proposal awaiting it goes in
  `BoxLike/Proposals/`.

Ergodicity of the equilibrium state is a theorem and no literature hypothesis: for a tuple with
rotations and every `s > 0` it is `System.IsEquilibriumState.ergodic_of_withRotations`; for
`0 < s < 2` it also follows from `thm:eq_state_is_sum` (`System.ergodic_of_hasProximalDiagonal`)
and, for an irreducible tuple, from uniqueness (`System.IsEquilibriumState.ergodic_of_irreducible`,
`MatrixTuple.ergodic_of_unique`); for `s ≥ 2` it follows from the Bernoulli form
(`System.IsEquilibriumState.ergodic_of_two_le`).

| Literature theorem | `Prop` (binder) | State |
|---|---|---|
| Morris–Shmerkin, Theorem 3.1 (arXiv:1602.08789v3), for `eq:simple_lyapunov` | `MorrisShmerkinLyapunov` (`hms`) | a theorem: `morrisShmerkinLyapunov_holds` (`MorrisShmerkin`), with no literature input, along Morris–Shmerkin, Lemmas 3.4 and 3.5, with the Gibbs bounds of `equilibriumGibbs`. The `Prop` in `Literature` is the statement the library proves; library results that take `hms` receive this proof in Solution, and no headline takes it. Compared with the source: faithful. Reductions: two-sided to one-sided shift; transposed tuple for the order of products; the conclusion drops full support |
| Feng–Käenmäki, Proposition 1.2 (arXiv:1009.3129), with `q = s` for `0 < s ≤ 1` and for `1 < s < 2` with `q = 2 - s` for the rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i`: the Gibbs bounds of `thm:irred_eq_state` | `FengKaenmakiGibbs` (`hfk`) | a theorem: `fengKaenmakiGibbs_holds` (`QuasiMultiplicative/Main`), with no literature input, from `FengKaenmakiNormEquilibrium` (`FengKaenmakiNormEquilibrium.fengKaenmakiGibbs`). The `Prop`, declared in `Literature`: hypothesis `System.Irreducible`, range `0 < s < 2`, conclusion `System.HasGibbsBounds`. For `1 < s < 2`, `‖A'_𝐢‖^{2-s} = φ^s(A_𝐢)` and `A'` is irreducible when `𝖠` is, which justifies the range. Uniqueness is `FengKaenmakiUnique`; ergodicity is a theorem. Taken by the results for irreducible tuples (`System.irred_eq_state`, `System.IsEquilibriumState.hasGibbsBounds_of_irreducible`, `System.IsEquilibriumState.submultiplicative`, `System.IsEquilibriumState.cylinder_bounds_dimaff`), which receive this proof in Solution, and by no headline result; for tuples with rotations its conclusion is the theorem `EquilibriumGibbsStatement` (next row) |
| `thm:irred_eq_state` for box-like tuples with rotations: the Gibbs bounds of every invariant `s`-equilibrium state for `0 < s < 2` | `EquilibriumGibbsStatement` (`hfk`) | a theorem: `equilibriumGibbs` (`EquilibriumGibbs`), with no literature input. The `Prop` in `EquilibriumGibbsStatement` is the statement the library proves; the main line takes it with the binder `hfk` and receives this proof in Solution, and no headline takes it. Hypotheses: `System.WithRotations`, `0 < s < 2`, an invariant probability measure that is an `s`-equilibrium state; conclusion `System.HasGibbsBounds`. A tuple with rotations need not be irreducible, and the statement does not assume it |
| Feng–Käenmäki, Proposition 1.2 (arXiv:1009.3129v1 and Discrete Contin. Dyn. Syst. 30 (2011), p. 700): the uniqueness part of `thm:irred_eq_state` | `FengKaenmakiUnique` (`hfku`) | a theorem: `fengKaenmakiUnique_holds` (`QuasiMultiplicative/Main`), with no literature input, from `FengKaenmakiNormEquilibrium` (`FengKaenmakiNormEquilibrium.fengKaenmakiUnique`). The `Prop` is declared in `LiteratureRemarks`; compared with the source on 2026-09-21: faithful. The source allows `F = ℝ` and every `q > 0`; its irreducibility, no common invariant proper subspace, is `System.Irreducible` for `d = 2`. For `1 < s < 2` it applies to the rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` with `q = 2 - s`. Reduction: two-sided to one-sided shift. Taken by the results for irreducible tuples (`System.unique_of_irreducible`, `System.IsEquilibriumState.ergodic_of_irreducible`, `System.irred_eq_state`), which receive this proof in Solution, by no headline result; for tuples with rotations uniqueness is the theorem `System.unique_of_withRotations`, and for `s ≥ 2` uniqueness is proved without it |
| Feng–Käenmäki, Proposition 1.2 (Discrete Contin. Dyn. Syst. 30 (2011); read in arXiv:1009.3129v1, p. 3, with the setting on pp. 1–2), in the form of the source, for `thm:irred_eq_state` | `FengKaenmakiNormEquilibrium` (`h`) | a theorem: `fengKaenmakiNormEquilibrium_holds` (`QuasiMultiplicative/Main`), with no literature input, by the quasi-multiplicativity of the norm (`MatrixTuple.normQuasiMultiplicative_of_irreducible`), Bowen's construction of an ergodic Gibbs measure of `‖·‖^q` (`normGibbsExistence`) and the relative-entropy argument for uniqueness (`MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs`). The `Prop` is declared in `LiteratureFengKaenmaki`, authorised by the project owner. The source: `F = ℝ` or `ℂ`, a family of `d × d` matrices over `F` irreducible over `F^d` (their Definition 1.1), the one-sided full shift, the pressure `P(q)` of the norm potential (their (1.1)), `M_*(μ)` (their (1.2)) and the `q`-equilibrium states of their (1.4); for each `q > 0` there is a unique `q`-equilibrium state, it has the Gibbs property (1.6), and `P'(q) = M_*(μ_q)`. Specialisation: `F = ℝ`, `d = 2`, invertible matrices, irreducibility `TupleIrreducible`, the `ℓ²` operator norm (all norms give the same `P`, `M_*` and equilibrium states, and the Gibbs property with another constant), the entropy `entropyPlus` of the generating partition, and `P`, `M_*` as `limUnder` of sequences that converge (`MatrixTuple.tendsto_normPressure`, `MatrixTuple.tendsto_normLyapPlus`, `tendsto_entropyPlus`). It is weaker than the source: it omits the existence of `μ_q`, which the library proves (`MatrixTuple.exists_isEquilibriumState`), the Gibbs property for `n = 0`, the differentiability of `P` and singular matrices, for which `P(q) = -∞` is possible and `Real.log 0 = 0` would make a transcription false. Degenerate tests: the empty alphabet is not irreducible, so the statement is silent; for the one-letter tuple of the quarter turn the conclusion is proved (`FengKaenmakiNormEquilibrium.degenerate_quarterTurn`). Reductions: the two-sided shift (`FengKaenmakiNormEquilibrium.twoSided`); the singular value potential for `0 < s < 2`, by `q = s` for `s ≤ 1` and the rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` with `q = 2 - s` for `1 < s < 2` (`FengKaenmakiNormEquilibrium.svf`). It implies `FengKaenmakiGibbs` and `FengKaenmakiUnique`. Taken by `MatrixTuple.irred_eq_state_of_fengKaenmaki`, which is `thm:irred_eq_state` at the article's scope and receives this proof in Solution, and by no headline result |
| Fraser–Jordan–Jurga, Lemma 1.3, Corollaries 1.5 and 1.6 (arXiv:1706.06833), `thm:eq_state_is_sum` | `FraserJordanJurgaDecomposition` (`hfjj`) | a theorem: `fraserJordanJurgaDecomposition_holds` (`FraserJordanJurga/Main`), with no literature input. The `Prop` in `Literature` is the statement the library proves; library results that take `hfjj` receive this proof in Solution, and no headline takes it. Hypothesis: an invariant probability measure with `System.HasGibbsBounds`, which is their characterisation of the Käenmäki measure; every invariant measure with these bounds is absolutely continuous with respect to the ergodic image `q_*μ_1` of Bowen's Gibbs measure `μ_1` and equals it (`System.eq_of_hasGibbsBounds`, `System.hasGibbsBounds_map_unCode`). The proof starts from Bowen's ergodic Gibbs measures on the mixing `Σ_Z` (`bowenGibbsExistence`, `existsUnique_ergodic_isGibbsPotential`) and uses neither proximality nor the hypothesis `S.HasProximalDiagonal`. Reductions: signed entries to moduli; one-sided to two-sided; three of the four decompositions from the symmetry exchanging the axes. The parts of the source it omits are theorems: the Gibbs constants are `P(𝖠, s)` (`System.GibbsDecomposition.isGibbsAt₁`, `System.GibbsDecomposition.isGibbsAt₂`), `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` (`System.pressure_eq_pressureZ₁`, `System.pressure_eq_pressureZ₂`), and the `f_{2,1}` identities (`System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂`, `System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂`) |
| Jordan–Rapaport, Theorem 1.1 (arXiv:1908.00271), in `eq:gibbs_proj_dim` | `JordanRapaportDimension` (`hjr`) | declared in `Literature`; compared with the source: faithful. `System.ProjExpSeparation` is their Definition 1 verbatim; ratios of either sign are allowed; reductions: two-sided to one-sided shift |
| Feng–Käenmäki, `thm:irred_eq_state`: ergodicity of the equilibrium state | | not declared and not needed: for `0 < s < 2` ergodicity follows from `thm:eq_state_is_sum`, since `μ = q_*μ_1` is a factor of the ergodic `μ_1` (`System.ergodic_of_hasProximalDiagonal`, `System.IsEquilibriumState.ergodic_of_withRotations`); for `s ≥ 2` the equilibrium state is Bernoulli (`System.IsEquilibriumState.ergodic_of_two_le`) |
| Falconer (1988), cited as Theorem 5.4: `eq:hausdorff_affinity_upper_bound` and the bound for the upper Minkowski dimension (tex lines 2159 to 2172, 542 to 544) | `System.FalconerBoxBound` | a theorem: proved for every planar self-affine set in `Planar/FalconerBound` (`PlanarSystem.upperBoxDim_attractor_le`, `PlanarSystem.dimH_attractor_le`) and for every box-like set in `FalconerBound` (`System.upperBoxDim_attractor_le`, `System.dimH_attractor_le`); the `Prop` `System.FalconerBoxBound` of `FraserChain` states the bound and holds (`System.falconerBoxBound`). The theorem number is not checked against the source |
| Fraser, Theorem 2.3 and Corollary 2.5 (arXiv:1108.2639v1), `thm:fraser` | `System.FraserBound`, `System.FraserROSC` | a theorem: `System.fraserBound_holds` (`Fraser/UpperBound`) and `System.fraserROSC_holds` (`Fraser/Main`), along Fraser's Section 5, with no literature input. Declared in `FraserChain`, as the two parts of Theorem 2.3: `System.FraserBound` for every box-like set and `System.FraserROSC` under the rectangular open set condition, stated as in the source; the results that use them take them as hypotheses, and Solution passes the proofs. The first equality `\dim_P X = \overline{\dim}_M X` is proved without them (`System.packingDim_attractor`), and Corollary 2.5 follows from `System.FraserROSC` (`System.FraserROSC.dim_eq_dimaff`) |
| Bárány–Käenmäki, Theorem 2.1 (Adv. Math. 379 (2021), arXiv:1910.04623v4), in `prop:ssc_no_overlap_not_pesc` | `NoOverlap.BaranyKaenmakiTheorem`, `NoOverlap.BaranyKaenmakiPair` | declared in `NoOverlapExample`. `NoOverlap.BaranyKaenmakiTheorem` is the form of the source, compared with arXiv v4 word for word, and `NoOverlap.ssc_no_overlap_not_pesc'` derives the proposition from it. `NoOverlap.BaranyKaenmakiPair` is an older, stronger form retained in the library, taken by `NoOverlap.ssc_no_overlap_not_pesc`; applied to `η_n = exp(-n²)` the source's form gives a pair with all its properties except the transcendence of `λ`, which the proof does not use (`NoOverlap.exists_pair_of_baranyKaenmakiTheorem`). The current manuscript and the prime endpoints use the source theorem directly |
| Rossi, Theorem 2.2, `eq:hausdorff_ergodic_lyapunov` | `System.RossiBound` | a theorem: `System.rossiBound` (`RossiBound`), by the covering argument of `Rossi`, with no literature input. Declared in `DimensionFormula`; no theorem takes it, since the proof of `thm:main_extended` evaluates the Ledrappier–Young formula to an equality. `System.upperHausdorffDim_map_proj_eq` shows equality in the bound for the equilibrium state |
| Feng, Theorems 1.2 and 1.3 (arXiv:1901.01691v2), `thm:feng1` | `FengLedrappierYoung` (`hly`) | declared in `LiteratureFeng`; compared with the source: faithful, the case `s = 2`, `k_1 = k_2 = 1`. Feng's order of the filtration, of the matrix products and the signs of the formula agree with the Lean definitions. Reductions: Feng's `Σ'` inside the box-like `Σ'`, with almost everywhere equal conditional measures (`System.condMeas_fengXi_ae_eq`); supremum versus Euclidean balls. `FengLedrappierYoung` follows from `PlanarFengLedrappierYoung` (`PlanarFengLedrappierYoung.fengLedrappierYoung`) |
| Feng, Theorems 1.2 and 1.3 (arXiv:1901.01691v2), `thm:feng1`, second part: the case `d = 1` for the projective system `Ψ` | `FengLedrappierYoungBar` (`hlyb`) | follows from `FengLedrappierYoung`: `fengLedrappierYoungBar_of_fengLedrappierYoung` (`ProjectiveLineSystem`), through the planar system `z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` of `Ψ`, whose attractor lies on the horizontal axis; the scalar formula holds for every box-like system, with neither rotations nor proximality (`System.isExactDim_map_projBar_of_fengLedrappierYoung`). The `Prop` in `LiteratureFeng` keeps the hypotheses `S.WithRotations` and `S.Proximal` of the article; library results that take `hlyb` receive this proof in Solution, and no headline takes it. Compared with the source: faithful, the case `d = 1` |
| Feng, Theorems 1.2 (ii) and 1.3, formula (1.6) (Duke Math. J. 172 (2023); compared with arXiv:1901.01691v2), the first part of `thm:feng1` for every planar self-affine set | `PlanarFengLedrappierYoung` (`hly`) | declared in `LiteraturePlanarFeng`; authorised by the project owner. The source: an affine iterated function system on `ℝ^d`, not necessarily invertible or contracting; an ergodic `m` on the two-sided full shift for which the system is average contracting; the distinct Lyapunov exponents `λ_1 > ⋯ > λ_s` with multiplicities `k_i`; local dimensions with closed Euclidean balls; the entropies `h_i = H_m(𝒫 \| \widehat{ξ}_i)` of their (1.5). Specialisation: `d = 2`, invertible contractions (`PlanarSystem`), `μ` ergodic with `λ_2 < λ_1`, so that `s = 2`, `k_1 = k_2 = 1` and (1.6) reads `(h_1 - h_0)/λ_1 + (h_2 - h_1)/λ_2`. Feng's entropies for his partitions on a Borel set of full measure inside the library's `Σ'` are the library's (`PlanarSystem.condEntropy_fengXi_eq`), so the source statement implies the transcription (`planarFengLedrappierYoung_of_fengXi`, proved); closed balls of the supremum norm give the same pointwise dimension as Euclidean balls; the order of the matrix products and the signs agree with Feng's (1.3), Section 1.2 and (1.6). Degenerate tests, by hand: one letter with `A = diag(1/2, 1/4)`; zero translations with a Bernoulli measure; scaled rotations, where `λ_1 = λ_2` and the statement is silent. It implies `FengLedrappierYoung`. Taken by `PlanarSystem.feng1` and `planar_feng1`, which are `thm:feng1` at the article's scope, and by no headline result |
| Feng, Lemma 4.6, first identity of (4.16) | `FengInfoSum` (`hfi`), `FengInfoSumBar` (`hfib`) | a theorem: `fengInfoSum_holds` (`FengIdentity`) and `fengInfoSumBar_holds` (`FengIdentityBar`), along Feng's Lemmas 4.4 and 4.5, with neither ergodicity nor his (4.7) in the general identity `infoSum_of_pullShift`. The `Prop`s in `LiteratureFeng` are the statements the library proves; library results that take `hfi`, `hfib` receive these proofs, and no headline takes them. |
| Kittle–Kogler, Theorem 1.1 (arXiv:2610.10511, 7 October 2026), in the proof of `thm:main2` | `KittleKoglerDimension` (`hkk`) | declared in `Literature`; compared with the arXiv version on 2026-10-17. The source: for a probability measure `μ = ∑_j p_j δ_{g_j}` on finitely many distinct contracting similarities `g_j(x) = r_j x + t_j` of `ℝ`, `0 < |r_j| < 1`, `p_j > 0`, the self-similar measure `ν` is exact-dimensional with `dim ν = min{1, h_μ / |χ_μ|}`, `h_μ` the random walk entropy and `χ_μ = ∑_j p_j log |r_j|`. The statement takes the hypothesis that the similarities generate a free semigroup, under which the source notes `h_μ = H(p)`, and concludes `dim ν = min{1, H(p) / |χ_μ|}`, the form the article uses; it quantifies over every solution of the stationarity equation, which is the self-similar measure by Hutchinson's uniqueness. Exact-dimensionality is the source's convention for `dim ν`, with closed intervals |
| Birkhoff's pointwise ergodic theorem | | proved: `birkhoff_ae`, `birkhoff_ergodic` in `Birkhoff`, through the maximal ergodic theorem |
| Shannon–McMillan–Breiman, cited from Petersen (tex lines 1973 to 1977); Feng (4.17), `thm:feng_entropy_kolmogorov_sinai` | | proved: `shannonMcMillanBreiman` (`ShannonMcMillanBreiman`), by Breiman's argument through Maker's theorem and Chung's maximal inequality; Feng's (4.17) is `System.feng_entropy_kolmogorov_sinai` and `PlanarSystem.feng_entropy_kolmogorov_sinai_general` |
| Kolmogorov–Sinai entropy and the generator theorem (Bowen, §2, tex lines 1965 to 1972) | | proved: `ksEntropy`, `ksEntropy_shift_eq_entropy` in `KolmogorovSinai` |
| Oseledets' multiplicative ergodic theorem and Froyland–Lloyd–Quas, Theorem 4.1 (tex lines 1585 to 1607) | | proved for invertible planar cocycles: `MatrixTuple.measure_regularSet_compl_of_ergodic` in `Planar/OseledetsTheorem`, from Kingman's theorem (`kingman_ergodic`) and the Furstenberg–Kesten limits (`MatrixTuple.tendsto_log_norm_pastProd`, `MatrixTuple.tendsto_log_alpha₂_pastProd`) |
| Käenmäki, Theorems 2.6 and 4.1 (tex lines 2217 to 2218): existence of ergodic equilibrium states | | proved for every invertible tuple and every `s ≥ 0`: `MatrixTuple.exists_ergodic_isEquilibriumState` in `TupleErgodicEquilibrium` |
| Käenmäki–Vilppolainen, Lemma 2.1 (tex lines 2153 to 2156): monotonicity of the pressure | | proved: `System.strictAntiOn_pressure`, `BoxLike/Support/PressureConvexity.lean`, `PlanarSystem.existsUnique_pressure_eq_zero` |
| Hutchinson (tex lines 633 to 638 and 3578 to 3579): the attractor and the uniqueness of the invariant measure | | proved: `PlanarSystem.eq_attractor`, `System.IsInvariantMeasure.unique` |
| Walters, Theorem 1.31 (tex line 899): mixing of `Σ_Z` | | proved: `isTopologicallyMixing_subshiftShift_iff` |
| Sarig, Theorem 4.7 and Corollary 4.2 (tex lines 2501 to 2503): existence and uniqueness of the ergodic Gibbs measure of a Hölder potential | | proved, with no literature input, when both orientations occur: existence by Bowen's construction (`bowenGibbsExistence` in `Bowen/Main`, after Bowen, LNM 470, Chapter 1), uniqueness and the constant `P_Z(f)` (`existsUnique_ergodic_isGibbsPotential`, `IsGibbsPotential.eq_of_ergodic_of_isHolder`, `IsGibbsPotential.pressure_eq_of_isHolder`) |
| Morris–Shmerkin, Theorem 4.2 (tex lines 1583 to 1584) | | not used by any proof |
| Einsiedler–Ward, Proposition 5.20 and Theorem 5.14, in `thm:double_conditional` | | proved: `double_conditional` |
| Bárány–Käenmäki–Rossi and Bárány–Käenmäki–Yu, in `thm:A_classification` | | not used: the classification is proved directly (`tuple_classification`) |
| Hochman, proof of Theorem 1.5 (tex lines 1375 to 1377): algebraic parameters give projective exponential separation | | not formalised and not used by any proof |
| Feng–Hu, Theorem 2.8 (arXiv:1002.2036v1 and Comm. Pure Appl. Math. 62 (2009), same number): exact-dimensionality of `\overline{π}_*ν` without separation | `FengHuExactDim` (`hfh`) | declared in `LiteratureRemarks`; compared with the source on 2026-09-21: faithful. The source treats `m`-conformal `C^1` systems on the one-sided full shift with closed balls, with no separation condition, maps that need not be distinct and any ergodic `m`; the similarities of `Ψ` are `m`-conformal for every `m`. Reduction: two-sided to one-sided shift, by restriction to the coordinates `k ≥ 0`. Taken only by the remark that the marginals are double-dimensional without separation (`System.marginal_isDoubleDim`) |

The numbering of Morris–Shmerkin and Jordan–Rapaport is that of the arXiv versions; their
journal versions are not checked. Fraser–Jordan–Jurga is compared with the published version,
Feng–Hu and Feng–Käenmäki with the arXiv and the published versions, except that
`FengKaenmakiNormEquilibrium` is compared with arXiv:1009.3129v1 only; Feng's theorems are
compared with arXiv:1901.01691v2.

Checks made on the literature statements, by inspection and not by machine:

- `JordanRapaportDimension` at a Dirac mass on a constant sequence gives entropy `0`,
  dimension `0`, and a Dirac push-forward, which has local dimension `0`; with all
  translations zero the projective exponential separation condition fails, so the statement
  is silent there.
- The four decompositions of `FraserJordanJurgaDecomposition` are mutually consistent exactly
  when `\overline{ω}_*μ_1 = \overline{τ}_*μ_2` and `\overline{τ}_*μ_1 = \overline{ω}_*μ_2`,
  which is the symmetry noted in `sec:gibbs_measures`.
- The quantities in the statements are literal limits (`entropy`, `System.lyapunov₁`,
  `System.lyapunov₂`, `System.energyLim`). They exist for invariant measures: `tendsto_entropy`,
  `System.tendsto_lyapunov₁`, `System.tendsto_lyapunov₂`, `System.tendsto_energyLim`.
- `System.gap n = ⊤` is possible only for `n ≤ 1`, since two letters in either order have the
  same derivative; the projective exponential separation condition is therefore the condition
  `Δ_n ≥ c^n` for infinitely many `n` of Jordan–Rapaport.
- `FengHuExactDim` and `FengKaenmakiUnique` pass the degenerate tests: for the empty
  alphabet `System.Irreducible` is false; one letter; Dirac measures.
- `FengKaenmakiNormEquilibrium` at the one-letter tuple of the quarter turn
  `J = [[0, -1], [1, 0]]`, which is irreducible and orthogonal: `‖J^n‖ = 1`, `P(q) = 0`, and
  every invariant probability measure on `Σ^+` has the Gibbs property with `C = 1`, which the
  library proves (`FengKaenmakiNormEquilibrium.degenerate_quarterTurn`); for the empty alphabet
  `TupleIrreducible` fails and the statement is silent.
- `PlanarFengLedrappierYoung` at one letter with `A = diag(1/2, 1/4)`: `π_*μ` is a Dirac mass,
  of pointwise dimension `0`, and all `h_i` vanish since `𝒫` has one atom; with all translations
  zero and a Bernoulli measure, `π_*μ = δ_0` and `h_0 = h_1 = h_2`, so both sides vanish; for
  scaled rotations `λ_1 = λ_2` and the statement is silent.
- `KittleKoglerDimension` at one similarity `g(x) = r x + t` with weight `1`: the semigroup is
  free since `g^n ≠ g^m` for `n ≠ m`, the stationary measure is the Dirac mass at the fixed
  point, of exact dimension `0 = min{1, 0 / |log |r||}`; for the empty index type the
  weights do not sum to `1`, so the statement is silent.

`LyapunovDim` is arithmetic in real parameters and takes no literature hypothesis.
