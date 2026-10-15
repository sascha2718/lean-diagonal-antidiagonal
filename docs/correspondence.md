# Correspondence with the paper

The manuscript `diagonal-antidiagonal.tex` has 40 numbered statements: the theorem-like
environments share one counter, numbered within sections. Every one of them has an entry in
[`paper-correspondence.yaml`](../paper-correspondence.yaml), with its printed number, a
fingerprint of its LaTeX source, its status and the Lean declarations that correspond to it,
and an assessment below. Of the 40, 33 are formalised, 4 are theorems the paper quotes from the
literature without proof and enter as `Prop`-valued hypotheses, 1 is formalised apart from
numerical values, and 2 are intentionally not formalised. The manifest also fingerprints 40
prose spans with the unnumbered definitions and claims the library certifies.
`scripts/check_paper_correspondence.py` checks that the manifest, this file, the comparator
configuration, `Challenge.lean`, `Solution.lean` and `formalization.yaml` agree with the
manuscript and with each other.

The library declares no axiom: every constant depends on `propext`, `Classical.choice` and
`Quot.sound` only. The literature theorems the article cites without proof are `Prop`-valued
definitions, and every result that uses one takes it as an explicit hypothesis; the section
"Fidelity boundary" lists them, the rules they obey and their comparison with the sources.

## Statement layer

`Challenge.lean` states the seven headline results over Mathlib alone, with the eight literature
`Prop`s of the main line restated in it and an intentional `sorry` for each proof. Its definition
block is identical to `Solution/Definitions.lean`. `Solution.lean` and `Solution/` prove the
statements from the library, and `comparator-config.json` lists the seven theorems and permits
only the three standard axioms.

| `Challenge` | Article | Library | Literature hypotheses |
|---|---|---|---|
| `audit_main1` | Theorem 1.2, `thm:main1` | `System.main1_dimaff` | `hms`, `hfk`, `hfjj`, `hjr` |
| `audit_eq_state_proj_dim` | Theorem 4.4, `thm:eq_state_proj_dim` | `System.eq_state_proj_dim` | `hms`, `hfk`, `hfjj`, `hjr` |
| `audit_main2` | Theorem 1.3, `thm:main2` | `System.main2` | the eight of the main line |
| `audit_main_extended` | Theorem 4.16, `thm:main_extended` | `System.main_extended_min` | the eight of the main line |
| `audit_main_extended_ge_two` | Theorem 4.16, the case `s ≥ 2` | `System.main_extended_ge_two` | none |
| `audit_dimH_eq_min` | `\dim_H X = min{2, dimaff(X)}`, paragraph after `eq:hausdorff_ergodic_lyapunov` | `System.dimH_attractor_eq_min` | the eight of the main line |
| `audit_dimH_of_two_le` | the same for `dimaff(X) ≥ 2` under the strong open set condition | `System.dimH_attractor_of_two_le` | none |

The audited statements hold for every shift-invariant `s`-equilibrium state: uniqueness and
ergodicity of the equilibrium state are not assumed. The plane is `ℝ × ℝ` with the supremum
norm, and pointwise dimensions of measures use its closed balls. `Challenge.audit_main_extended`
states Theorem 4.16 as exact-dimensionality of `π_*μ` with dimension `min{2, dimaff(X)}`.

## The numbered statements

Lean names omit the root namespace `BoxLike`. The literature hypotheses are named by their
binders: `hms` Morris–Shmerkin, `hfk` Feng–Käenmäki (Gibbs bounds), `hfku` Feng–Käenmäki
(uniqueness), `hfjj` Fraser–Jordan–Jurga, `hjr` Jordan–Rapaport, `hfi`, `hfib` Feng's (4.16),
`hly`, `hlyb` Feng's Ledrappier–Young formula, `hfh` Feng–Hu.

| No. | Label | Kind | Assessment |
|---|---|---|---|
| 1.1 | `thm:fraser` | theorem | **Cited.** Fraser's Theorem 2.3 is the `Prop`s `System.FraserBound` and `System.FraserROSC`. `\dim_P X = \overline{\dim}_M X` is proved for every box-like set (`System.packingDim_attractor`); Corollary 2.5 is derived from `System.FraserROSC` (`System.FraserROSC.dim_eq_dimaff`), and holds without the rectangular open set condition when `dimaff(X) ≤ 2`. The first display of the theorem should read upper Minkowski dimension. |
| 1.2 | `thm:main1` | theorem | **Proved.** `Challenge.audit_main1` from `System.main1_dimaff`, with `hms`, `hfk`, `hfjj`, `hjr`; for every invariant equilibrium state at `s = dimaff(X) < 2`. |
| 1.3 | `thm:main2` | theorem | **Proved.** `Challenge.audit_main2` from `System.main2`, with the eight hypotheses of the main line. The upper bound is Falconer's, proved in the library. |
| 1.4 | `q:coincident-projection-dimensions` | question | **Not formalised.** A question, not a statement. Its hypotheses are consistent by Proposition 2.7; whether the two marginal dimensions can coincide is open. |
| 2.1 | `thm:box_like_sa` | lemma | **Proved** for a single matrix, as the equivalence `IsBoxLikeMatrix` iff diagonal or anti-diagonal with entries in `(-1, 1)` (`isBoxLikeMatrix_iff`). |
| 2.2 | `thm:A_classification` | lemma | **Proved** for every planar tuple of invertible matrices, with no literature input (`tuple_classification`, `tuple_trichotomy`); the second equivalence needs proximality, and both directions fail without it. |
| 2.3 | `thm:box_like_proximal` | lemma | **Proved** (`System.Proximal.hasProximalDiagonal_or_sq`); the hypothesis with rotations is not used. |
| 2.4 | `thm:tau_omega_sigma_commutative` | lemma | **Proved**, as the four cases `tau_shift_of_eps_eq_zero`, `omega_shift_of_eps_eq_zero`, `tau_shift_of_eps_eq_one`, `omega_shift_of_eps_eq_one`. |
| 2.5 | `thm:matrix_products_g_derivatives` | lemma | **Proved**, as `System.abs_matWord_pastWord_e1`, `System.abs_matWord_pastWord_e2`. |
| 2.6 | `lem:proj_gap_dominated` | lemma | **Proved** in greater generality (`System.gap_le_diagGap`): a common first-row entry suffices, and the maps need not be diagonal. |
| 2.7 | `prop:ssc_no_overlap_not_pesc` | proposition | **Proved** in two forms, from Bárány–Käenmäki's Theorem 2.1 as a `Prop` hypothesis (`NoOverlap.ssc_no_overlap_not_pesc`, `NoOverlap.ssc_no_overlap_not_pesc'`); the transcendence of `λ` is not needed. |
| 3.1 | `thm:lyapunov_exponents_via_g_system` | lemma | **Proved** (`System.lyapunov_exponents_via_g_system`); the content is `μ(Σ') = 1`, from Birkhoff's theorem without Oseledets. |
| 3.2 | `thm:conditional_measures_of_a_conditional_measure` | lemma | **Proved** (`condMeas_cond`, `condMeas_cond_of_saturated`), with Mathlib's `condExpKernel`. |
| 3.3 | `thm:double_conditional` | lemma | **Proved** (`double_conditional`). |
| 3.4 | `thm:finer_partition_dirac_mass` | lemma | **Proved** (`finer_partition_dirac_mass`). |
| 3.5 | `thm:feng_entropy_as_limit` | lemma | **Proved** from Birkhoff's theorem and Feng's (4.16), which enters as `hfi`, `hfib` (`System.feng_entropy_as_limit`, `System.feng_entropy_as_limit_bar`). |
| 3.6 | `thm:feng_entropy_kolmogorov_sinai` | lemma | **Not formalised, not needed.** The identity `h_0(μ) = h(μ)` it serves is proved directly (`System.dimEntropy_zero_eq_entropy`, `System.dimEntropyBar_zero_eq_entropy`). |
| 3.7 | `thm:feng_entropy_zero` | lemma | **Proved** (`System.feng_entropy_zero`, `System.feng_entropy_zero_bar`), with `hfi`, `hfib`; the scalar form assumes no ergodicity. |
| 3.8 | `thm:partitions_xi1` | lemma | **Proved** (`System.partitions_xi1`); only `λ_2 < λ_1` and past saturation are used. |
| 3.9 | `thm:partition_tau_conj` | lemma | **Proved** (`System.partition_tau_conj`). |
| 3.10 | `thm:irred_eq_state` | proposition | **Cited.** The Gibbs bounds are `hfk` and uniqueness is `hfku`, both from Feng–Käenmäki, Proposition 1.2, applied for `1 < s < 2` to a rescaled tuple. Existence is proved for every `s ≥ 0` (`System.exists_isEquilibriumState`); for `s ≥ 2` existence, uniqueness and ergodicity are proved with no hypothesis; for `0 < s < 2` ergodicity is proved from Proposition 3.13 (`System.ergodic_of_hasProximalDiagonal`). The main results use only the Gibbs bounds. |
| 3.11 | `thm:two-block-normalisation` | lemma | **Proved**, part by part (`System.attractor_sq`, `System.pressure_sq`, `System.IsEquilibriumState.map_group`, `System.ProjExpSeparation.sq`, ...); uniqueness of `μ^(2)` takes `hfku`. |
| 3.12 | `thm:sigma_tau_omega_positive_eq_measure` | lemma | **Proved** (`System.sigma_tau_omega_positive`) with `hfk` for the full support; the counting inequality is integrated against `μ`, without Birkhoff's theorem. |
| 3.13 | `thm:eq_state_is_sum` | proposition | **Cited.** The four decompositions and the Lyapunov identities are `hfjj`. `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})`, the integral formulas, `μ_2 = flip_*μ_1` and the fourth decomposition from the other three are proved (`System.pressure_eq_pressureZ₁`, `System.GibbsDecomposition.map_flip`, `System.decomposition₂_of_decompositions`). |
| 4.1 | `thm:exact-dimensional-mixture` | lemma | **Proved** from Besicovitch's differentiation theorem (`IsExactDim.isDoubleDim_add`, `isExactDim_add_iff`). |
| 4.2 | `thm:feng1` | theorem | **Cited.** Feng's Theorems 1.2 and 1.3 are `hly` for the plane and `hlyb` for the projective system. |
| 4.3 | `thm:entropy_eq_gibbs` | proposition | **Proved** (`System.GibbsDecomposition.entropy_eq₁`, `System.GibbsDecomposition.entropy_eq₂`). |
| 4.4 | `thm:eq_state_proj_dim` | theorem | **Proved.** `Challenge.audit_eq_state_proj_dim` from `System.eq_state_proj_dim`, with `hms`, `hfk`, `hfjj`, `hjr`; for every invariant equilibrium state with `0 < s < 2`. |
| 4.5 | `ex:projection_double_dimensional` | example | **Partially formalised.** The system, its hypotheses, `P(𝖠, t) = log ρ(M(t))`, the characteristic equation for `dimaff(X)`, the double-dimensional and mutually singular marginals and `\dim_H X = dimaff(X)` are proved (`Example.dimaff_charEq`, `Example.marginal_doubleDim`, `Example.dimH_attractor`). The explicit Lyapunov exponents and the numerical values are not. |
| 4.6 | `thm:gibbs_tau_omega_positive` | lemma | **Proved** (`System.gibbs_tau_omega_positive`, `System.orientation_restrictions`), with the dependence of `Σ^τ`, `Σ^ω` on `μ` made explicit. |
| 4.7 | `thm:conditional_two_ways` | lemma | **Proved** (`System.conditional_two_ways`); one application of uniqueness of conditional measures suffices. |
| 4.8 | `thm:overline_h1_zero` | lemma | **Proved** (`System.overline_h1_zero`); the argument needs only `-h_0/λ_2 ≤ 1`. |
| 4.9 | `thm:overline_h1_zero_large` | lemma | **Proved** (`System.overline_h1_zero_large`), with the conditional measures as Dirac masses almost everywhere; the lower bound `-λ_1 ≤ h_0` is not used. |
| 4.10 | `thm:overline_h1_large` | lemma | **Proved** (`System.overline_h1_large`). |
| 4.11 | `thm:eq_state_h1_zero` | proposition | **Proved** (`System.eq_state_h1_zero`). |
| 4.12 | `thm:eq_state_h1_large` | proposition | **Proved** (`System.eq_state_h1_large`). |
| 4.13 | `thm:eq_state_h2_zero` | proposition | **Proved** (`System.eq_state_h2_zero`). |
| 4.14 | `thm:orto_partition_dirac` | proposition | **Proved** (`System.orto_partition_dirac`); the lower bound `-λ_1 ≤ h_0` is not used, so the proposition contains 4.13. |
| 4.15 | `thm:SOSC_h2_zero` | proposition | **Proved** (`System.SOSC_h2_zero`), with Poincaré recurrence in place of Birkhoff's theorem. |
| 4.16 | `thm:main_extended` | theorem | **Proved.** `Challenge.audit_main_extended` from `System.main_extended_min`, with the eight hypotheses of the main line, and `Challenge.audit_main_extended_ge_two` for `s ≥ 2` from `System.main_extended_ge_two`, with none. The appeal to Rossi's bound in the paper's proof is unused. |

## Unnumbered definitions and claims

The manifest fingerprints 40 prose spans. The claims among them: the dimension chain
`\dim_H X = \dim_P X = \dim_M X = dimaff(X)` with the squeeze `dimmaff(X) = dimaff(X)` (proved,
the squeeze from `System.FraserBound`); Falconer's bound `eq:hausdorff_affinity_upper_bound`
(proved for every box-like set); Rossi's bound `eq:hausdorff_ergodic_lyapunov` (cited, as
`System.RossiBound`, taken by no theorem); the reduction of `\dim_H X = min{2, dimaff(X)}` to the
projected equilibrium state (proved, the headline `Challenge.audit_dimH_eq_min` and
`Challenge.audit_dimH_of_two_le`); the decomposition `eq:proj_eq_is_sum` of the marginals and
their double-dimensionality without separation (proved, the latter from `hfh`);
`eq:gibbs_proj_dim` (cited, `hjr`); `eq:simple_lyapunov` (cited, `hms`); Bernoulli measures
and the non-quasi-Bernoulli equilibrium state (proved); the Bernoulli equilibrium state for
`s ≥ 2` (proved); the existence of ergodic equilibrium states (existence proved for every
`s ≥ 0`, ergodicity of the constructed state only for `0 < s < 2` and `s ≥ 2`); the natural
extension `η_*` (proved); the doubling of Gibbs measures (the cylinder form proved, the metric
form not); the uniqueness of ergodic Gibbs measures on the mixing sub-shift (cited, through
`hfjj`); the Shannon–McMillan–Breiman theorem (not formalised, not needed). The definitions
among them are listed in the manifest with status `formalized` and relation `representation`;
[`mathlib-gaps.md`](mathlib-gaps.md) describes the representation.

## Declaration index

Every result of the paper with the declarations that certify it, by topic. Tex line numbers
refer to the manuscript at the time of the entry.

| Result | Declaration | Module | State |
|---|---|---|---|
| `eq:def_of_eps_mod2` | `eps`, `eps_add_one`, `eq_eps_of_succ` | `Orientation` | **done** |
| `eq:tau_omega_sigma_commutative1` | `eps_shift` | `Orientation` | **done** |
| matrix `Z`, `Z²` positive | `Trans`, `trans_iff`, `exists_trans_trans` | `Coding` | **done** |
| `eq:def_of_tau_omega` | `tau`, `omega`, `unCode` | `Coding` | **done** |
| `eq:tau_omega_partition` | `range_tau`, `range_omega`, `range_tau_union_range_omega`, `disjoint_range_tau_range_omega` | `Coding` | **done** |
| `thm:tau_omega_sigma_commutative` | `tau_shift_of_eps_eq_zero`, `omega_shift_of_eps_eq_zero`, `tau_shift_of_eps_eq_one`, `omega_shift_of_eps_eq_one` | `Coding` | **done** |
| continuity of `τ`, `ω`, `\overline{π}`, `π` | `System.continuous_tau`, `System.continuous_omega`, `System.Bounds.continuous_projBar`, `System.continuous_proj` | `Attractor` | **done** |
| `τ`, `ω` homeomorphisms onto their images (tex lines 983 to 992); `Σ_Z`, `τ(Σ)`, `ω(Σ)` closed; `β` a homeomorphism with `β ∘ σ² = σ^(2) ∘ β` (tex lines 2402 to 2403) | `isClosedEmbedding_tau`, `isClosedEmbedding_omega`, `tauHomeomorph`, `omegaHomeomorph`, `isClosed_subshift`, `groupHomeomorph`, `groupHomeomorph_shift_two` | `CodingTopology` | **done**; the images are closed |
| the natural projection `η : Σ → Σ^+`, `η ∘ σ = σ^+ ∘ η`, the embedding `e` with `e ∘ σ^+ ≠ σ ∘ e` (tex lines 850 to 853) | `eta`, `shiftPlus`, `eta_shift`, `measurePreserving_shiftPlus_map_eta`, `embed`, `embed_comp_shiftPlus_ne` | `CodingTopology` | **done**; `e ∘ σ^+ ≠ σ ∘ e` needs `N ≥ 2` |
| `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is a bijection, `η_*μ` ergodic iff `μ` ergodic (tex lines 883 to 894) | `map_eta_injective`, `exists_map_eta_eq`, `existsUnique_map_eta_eq`, `exists_ergodic_map_eta_eq`, `mapEtaEquiv`, `ergodic_map_eta_iff`, `ergodic_mapEtaEquiv_symm_iff`, `isSigmaSubadditive_futureContent` | `CodingTopology`, `NaturalExtension` | **done**, by the Carathéodory extension of a content on the clopen future sets (Mathlib has no Kolmogorov extension theorem); `(π^+)_*μ^+ = π_*μ` (tex lines 896 to 897) is not formalised |
| `thm:box_like_sa` | `IsSquareIsometry`, `isSquareIsometry_iff`, `IsBoxLikeMatrix`, `isBoxLikeMatrix_iff`, `IsSquareIsometry.boxMat_zero_mul_orientation` | `BoxLikeMatrix` | **done**; the forward direction uses only `R([-1,1]²) ⊆ [-1,1]²` |
| `thm:A_classification` | `TupleIrreducible`, `TupleStronglyIrreducible`, `TupleProximal`, `tuple_classification`, `tuple_trichotomy`, `not_tupleIrreducible_iff_simultaneouslyTriangular`, `simultaneouslyBoxLike_of_proximal`, `simultaneouslyBoxLike_iff`, `tupleIrreducible_iff_lines`, `tupleStronglyIrreducible_iff_lines` | `Classification` | **done**, for arbitrary planar tuples, with no literature input; without proximality both directions of the "i.e." of item (2) fail (`not_tupleIrreducible_swap`, `not_simultaneouslyBoxLike_rotThree`) |
| a proximal box-like tuple with rotations is in case (2) of `thm:A_classification` | `System.irreducible_iff_tupleIrreducible`, `System.proximal_iff_tupleProximal`, `System.not_tupleStronglyIrreducible`, `System.tupleIrreducible_of_proximal`, `System.irreducible_and_not_stronglyIrreducible` | `Classification` | **done** |
| irreducible tuples; a tuple with rotations and a proximal diagonal generator is irreducible | `System.Irreducible`, `System.irreducible_of_hasProximalDiagonal` | `Proximal` | **done** |
| proximal matrices and tuples (`sec:irreducibility`) | `IsProximalMatrix`, `isProximalMatrix_iff_trace_det`, `System.Proximal` | `Proximal` | **done**, through the characteristic polynomial |
| `thm:box_like_proximal` | `System.Proximal.hasProximalDiagonal_or_sq` | `Proximal` | **done**, for every box-like tuple |
| product rule for diagonal and anti-diagonal matrices | `boxMat`, `boxMat_mul` | `System` | **done** |
| `eq:def_of_g_system` | `System.ratio`, `System.trans`, `System.g` | `System` | **done** |
| `eq:phi_def_by_g` | `System.coord_phi`, `System.phi_of_o_eq_zero`, `System.phi_of_o_eq_one`, `System.phi_eq_mulVec` | `System` | **done** |
| `A_𝐢` as a box matrix with entries `g'` along the path of `Σ_Z` | `System.matWord_eq` | `System` | **done** |
| `thm:matrix_products_g_derivatives` | `System.abs_matWord_pastWord_e1`, `System.abs_matWord_pastWord_e2` | `System` | **done**, with `|·|` written as the sum of the moduli of the two entries, one of which vanishes |
| `\overline{π}` | `System.projBar`, `System.Bounds.tendsto_gWord`, `System.Bounds.projBar_eq` | `Projection` | **done** |
| `eq:canonical_projection` | `System.proj`, `System.Bounds.tendsto_phiWord` | `Projection` | **done** |
| `eq:commutative_diagram` | `System.fst_proj`, `System.snd_proj`, `System.coord_phiWord` | `Projection` | **done** |
| `π(𝐢) = φ_{i_0}(π(σ𝐢))`, `π = π^+ ∘ η` | `System.Bounds.proj_eq`, `System.proj_congr` | `Projection` | **done** |
| `eq:self_affine_set_def` for `X = π(Σ)` | `System.attractor`, `System.Bounds.attractor_eq_iUnion` | `Projection` | **done** |
| `X` compact, non-empty, unique (Hutchinson); `φ_i` Lipschitz and injective; `Φ^(2)` has attractor `X` | `System.isCompact_attractor`, `System.attractor_nonempty`, `System.eq_attractor`, `System.lipschitzWith_phi`, `System.injective_phi`, `System.attractor_sq` | `Attractor` | **done** |
| strong separation, strong open set and rectangular open set conditions; strong separation implies the strong open set condition; both pass to `Φ^(2)` | `System.StrongSeparation`, `System.StrongOpenSet`, `System.RectangularOpenSet`, `System.StrongSeparation.strongOpenSet`, `System.StrongSeparation.sq`, `System.StrongOpenSet.sq` | `SeparationConditions` | **done** |
| `Δ_n^Ψ`, projective exponential separation | `System.gap`, `System.ProjExpSeparation` | `Separation` | **done** |
| `Δ_{m+1}^Ψ ≤ Δ_m^Ψ` (proof of `thm:two-block-normalisation`) | `System.gap_succ_le` | `Separation` | **done** |
| `lem:proj_gap_dominated` | `System.diagGap`, `System.gap_le_diagGap` | `Separation` | **done** |
| `prop:ssc_no_overlap_not_pesc` | `NoOverlap.ssc_no_overlap_not_pesc`, `NoOverlap.ssc_no_overlap_not_pesc'`, `NoOverlap.exists_system_of_homFree`, `NoOverlap.BaranyKaenmakiPair`, `NoOverlap.BaranyKaenmakiTheorem`, `NoOverlap.exists_pair_of_baranyKaenmakiTheorem`, `System.FreeProjective`, `System.not_projExpSeparation_of_diagGap` | `NoOverlapExample`, `NoOverlapExampleFree`, `Separation` | **done** from the `Prop` hypothesis `NoOverlap.BaranyKaenmakiPair` (the form the article uses); the primed form assumes Theorem 2.1 of the source, `NoOverlap.BaranyKaenmakiTheorem`. "Not strongly irreducible" is `¬ TupleStronglyIrreducible` of `Classification` |
| freeness of the projective semigroup and the choice of parameters in the proof of `prop:ssc_no_overlap_not_pesc` (tex lines 1490 to 1504, 1543 to 1572) | `NoOverlap.exists_algebraicIndependent_mem_Ioo`, `NoOverlap.exists_params`, `NoOverlap.genDeriv_transfer`, `NoOverlap.genVal_transfer`, `NoOverlap.eq_of_genDeriv_eq_of_genVal_eq`, `NoOverlap.Params.freeProjective` | `NoOverlapExampleFree`, `NoOverlapExample` | **done** |
| the paragraph after `prop:ssc_no_overlap_not_pesc`: planar exponential separation does not imply projective exponential separation (tex lines 1583 to 1593) | `System.StrongSeparation.exists_le_dist_phiWord`, `NoOverlap.planar_separation_not_pesc` | `NoOverlapExample` | **done** from `NoOverlap.BaranyKaenmakiPair` |
| `φ^s`, sub-multiplicativity | `svf`, `svf_mul_le` | `SingularValue` | **done**, on all real `2 × 2` matrices with the `ℓ²` operator norm |
| `α_1 = max{|a|,|b|}`, `α_1 α_2 = |a||b|`, values of `φ^s` on box matrices | `norm_boxMat`, `abs_det_boxMat`, `svf_boxMat_of_le_one`, `svf_boxMat_of_le_two`, `svf_boxMat_of_two_lt` | `SingularValue` | **done** |
| `P(𝖠, s)`, existence of the limit by Fekete | `System.svfSum`, `System.svfSum_add_le`, `System.pressure`, `System.RatioLowerBound.tendsto_pressure` | `Pressure` | **done** |
| `s ↦ P(𝖠, s)` continuous, strictly decreasing, `P(𝖠, 0) = log N`, `P → -∞`, `dimaff` as its unique zero | `System.pressure_zero`, `System.exists_pressure_slope`, `System.strictAntiOn_pressure`, `System.continuousOn_pressure`, `System.tendsto_pressure_atTop`, `System.dimaff`, `System.pressure_dimaff`, `System.dimaff_eq`, `System.dimaff_pos` | `AffinityDim` | **done** |
| Minkowski and packing dimensions of sets (tex lines 2267 to 2268, Falconer, *Techniques*, §2) | `upperBoxDim`, `lowerBoxDim`, `packingDim`, `upperBoxDim_le_of_forall`, `le_lowerBoxDim_of_forall`, `upperBoxDim_image_eq`, `lowerBoxDim_image_eq`, `packingDim_image_eq`, `upperBoxDim_le_lowerBoxDim_of_superMul`, `dimH_le_lowerBoxDim`, `dimH_le_packingDim`, `packingDim_le_upperBoxDim`, `packingDim_eq_upperBoxDim` | `SetDimensions` | **done**, with values in `ℝ≥0∞`; the packing dimension is the modified upper Minkowski dimension |
| the modified affinity dimension `dimmaff(X)` (tex lines 2267 to 2282), Fraser's Lemma 2.1, the existence of the Minkowski dimensions of the projections (after Fraser's Lemma 2.7), `dimmaff(X) ≤ dimaff(X)` (tex lines 578 to 579) | `System.projDim`, `System.modSvf`, `System.modSvf_append_le`, `System.le_modSvf_append`, `System.modPressure`, `System.tendsto_modPressure`, `System.dimmaff`, `System.dimmaff_eq`, `System.lowerBoxDim_coord_eq`, `System.projDim_eq_lowerBoxDim`, `System.upperBoxDim_coord_le_dimaff`, `System.projDim_le_dimaff`, `System.dimmaff_le_dimaff`, `System.dimmaff_eq_dimaff_of_full`, `System.dimaff_eq_dimmaff_of_projDim_eq_one` | `ModifiedAffinity` | **done**, with no literature input; `s(𝐢)` is the Minkowski dimension of the projection, the modified pressure is a limit, and `dimmaff(X) ≤ dimaff(X)` holds for every box-like set |
| `thm:fraser` | `System.FraserBound`, `System.FraserROSC`, `System.packingDim_attractor`, `System.fraserBound_iff`, `System.fraserROSC_of_le`, `System.FraserROSC.dimmaff_eq_dimaff`, `System.FraserROSC.dim_eq_dimaff`, `System.fraserBound_of_subsingleton`, `System.fraserROSC_of_subsingleton` | `FraserChain` | `\dim_P X = \overline{\dim}_M X` **done** for every box-like set; the first two parts are Fraser's Theorem 2.3 as the `Prop`s `System.FraserBound` and `System.FraserROSC`, hypotheses of the results that use them, compared with arXiv:1108.2639v1; the third part (Fraser's Corollary 2.5) **done** from `System.FraserROSC`, and without the rectangular open set condition when `dimaff(X) ≤ 2` (`System.dimmaff_eq_dimaff_of_full`) |
| `eq:hausdorff_affinity_upper_bound` and Falconer's bound for the upper Minkowski dimension (tex lines 2255 to 2265, 573 to 574) | `System.upperBoxDim_attractor_le_of_pressure_neg`, `System.upperBoxDim_attractor_le_dimaff`, `System.upperBoxDim_attractor_le`, `System.dimH_attractor_le`, `System.falconerBoxBound` | `FalconerBound`, `FraserChain` | **done**, with no literature input, for every box-like system; no separation, rotations or proximality |
| the chain `\dim_H X = \dim_P X = \dim_M X = dimaff(X)` and the squeeze `dimmaff(X) = dimaff(X)` (tex lines 571 to 581) | `System.FalconerBoxBound`, `System.falconerBoxBound_iff`, `System.falconerBoxBound_iff_euclidean`, `System.FalconerBoxBound.dimH_le`, `System.FalconerBoxBound.dimmaff_le_dimaff`, `System.dim_chain`, `System.dimmaff_eq_dimaff`, `System.dim_chain_main2`, `System.dimmaff_eq_dimaff_main2` | `FraserChain` | **done**: the chain for every box-like set with `\dim_H X = dimaff(X)`, with no hypothesis beyond it; the squeeze from the `Prop` `System.FraserBound`; the `main2` forms add the hypotheses of `System.main2` |
| `thm:irred_eq_state`: the Gibbs bounds for `0 < s < 2` | `System.HasGibbsBounds`, `FengKaenmakiGibbs` | `Thermodynamic`, `Literature` | hypothesis (section 6) |
| `thm:irred_eq_state`: uniqueness for every `s > 0`, for a proximal box-like tuple with rotations | `System.unique_equilibrium_of_lt_two`, `System.unique_equilibrium_of_two_le`, `System.unique_equilibrium` | `UniqueEquilibrium` | **done**; for `0 < s < 2` from the hypothesis `FengKaenmakiUnique` and irreducibility, for `s ≥ 2` with no literature hypothesis and no hypothesis on the tuple |
| `thm:irred_eq_state` for `s ≥ 2`: existence, uniqueness, ergodicity | `System.isEquilibriumState_bernoulli`, `System.IsEquilibriumState.eq_bernoulli`, `System.existsUnique_isEquilibriumState_of_two_le`, `System.IsEquilibriumState.ergodic_of_two_le` | `BernoulliEquilibrium` | **done**, with no literature hypothesis: the equilibrium state is the Bernoulli measure with weights `|det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` |
| `thm:irred_eq_state`: existence, the weak-star infrastructure (tex lines 2322 to 2323, Käenmäki, Theorems 2.6 and 4.1) | `compactSpace_probabilityMeasure`, `InvariantMeasures`, `isCompact_invariantMeasures`, `invariantMeasures_nonempty`, `entropy_eq_iInf`, `System.energyLim_eq_iInf`, `upperSemicontinuousOn_entropy`, `System.upperSemicontinuousOn_energyLim`, `System.exists_maximiser` | `InvariantMeasures` | **done**, with no literature input: `h_0 + Λ(𝖠, ·, s)` attains its maximum on the compact set `ℳ_σ(Σ)` for every `s ≥ 0` |
| `thm:irred_eq_state`: existence, for every `s ≥ 0` | `System.log_svfSum_le_avgBlockMeasure`, `System.exists_invariant_pressure_le`, `System.exists_invariant_le_entropy_add_energy`, `System.exists_isEquilibriumState` | `EquilibriumExistence` | **done**, with no literature input, by the construction of Misiurewicz: the averaged block measures satisfy the two-parameter estimate, and a weak-star limit point is an equilibrium state. Irreducibility is not used. Ergodicity of the measure produced is not formalised |
| sub-multiplicativity of the equilibrium state, `C⁻¹ φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C φ^s(A_𝐢)` at `s = dimaff` (tex lines 2330 to 2345) | `System.HasGibbsBounds.submultiplicative`, `System.HasGibbsBounds.cylinder_bounds_dimaff`, `System.IsEquilibriumState.submultiplicative`, `System.IsEquilibriumState.cylinder_bounds_dimaff` | `GibbsProperties` | **done**; the forms for the equilibrium state take `FengKaenmakiGibbs` |
| Bernoulli measures, their invariance and ergodicity (tex lines 2451 to 2456) | `bernoulli`, `measurePreserving_shift_bernoulli`, `ergodic_shift_bernoulli`, `eq_bernoulli_of_cylinder`, `eq_bernoulli_weightMeasure_of_measureReal_cylinder`, `entropy_bernoulli`, `IsBernoulli` | `BernoulliEquilibrium`, `GibbsProperties` | **done** |
| the equilibrium state for `0 < s < 2` is not quasi-Bernoulli and not Bernoulli (tex lines 555 to 560, 2457 to 2463) | `System.exists_mul_svf_le`, `System.not_quasiBernoulli`, `System.not_isBernoulli`, `System.IsEquilibriumState.not_quasiBernoulli`, `System.IsEquilibriumState.not_isBernoulli` | `GibbsProperties` | **done**, from the Gibbs bounds alone, for every proximal box-like tuple with rotations; "grouping a Bernoulli measure in pairs gives a Bernoulli measure" (tex line 2462) is not formalised and not needed |
| `s ≥ 2` in `sec:normalisation` (tex lines 2471 to 2480): `φ^s = |det|^{s/2}`, `P(𝖠, s) = log ∑_i |det A_i|^{s/2}`, the equilibrium state is Bernoulli | `svf_of_two_le`, `System.pressure_of_two_le`, `System.lyapunov₁_add_lyapunov₂`, `System.IsEquilibriumState.log_sum_eq`, `entropy_le_blockEntropy_one`, `measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq`, `blockEntropy_one_add_sum_le`, `System.IsEquilibriumState.eq_bernoulli` | `PressureLarge`, `BernoulliEntropy`, `BernoulliEquilibrium` | **done**, for every box-like tuple, with no literature hypothesis |
| `eq:variational`, `\dim_L ≤ dimaff`, `\dim_L = dimaff` for an equilibrium state at `dimaff` | `System.entropy_add_energyLim_le_pressure`, `add_energy_lyapDim`, `System.pressure_lyapDim_nonneg`, `System.lyapDim_le_dimaff`, `System.IsEquilibriumState.lyapDim_eq_dimaff` | `Variational`, `AffinityMain` | **done** |
| `thm:main1` with `s = dimaff(X) < 2` | `System.main1_dimaff` | `AffinityMain` | **done**; hypotheses: the four of `System.main1` |
| `dim(π_*μ) ≤ \dim_H(X)`, the use of `eq:dimension_measure_def` in `thm:main2` | `IsExactDim.le_dimH`, `IsExactDim.le_dimH_of_map`, `System.le_dimH_attractor` | `MassDistribution`, `AffinityMain` | **done**, by the mass distribution principle |
| `φ^s(A_{𝐢|_n}) = max{exp S_n f_{1,s}(τ𝐢), exp S_n f_{2,s}(τ𝐢)}`, `eq:lyapunov_exp_for_psi` | `System.svf_matWord_futureWord`, `System.abs_gDeriv_futureWord` | `Variational` | **done** |
| `Φ^(2)`, `𝖠²`, `g^{(2)}_{(i,j),c} = g_{i,c} ∘ g_{j,c+o(i)}` (`thm:two-block-normalisation`) | `System.sq`, `System.sq_mat`, `System.sq_phi`, `System.sq_g` | `SecondIterate` | **done** |
| `Δ_n^{Ψ^(2)} ≥ Δ_{2n}^Ψ`, projective exponential separation passes to `Φ^(2)` | `System.gap_two_mul_le_gap_sq`, `System.gap_anti`, `System.projExpSeparation_iff_frequently`, `System.ProjExpSeparation.sq` | `SecondIterate` | **done** |
| `thm:two-block-normalisation`: `β`, `π^(2) ∘ β = π`, `P(𝖠², t) = 2P(𝖠, t)`, `h_0(μ^(2)) = 2h_0(μ)`, `λ_i(𝖠², μ^(2)) = 2λ_i(𝖠, μ)`, `π^(2)_*μ^(2) = π_*μ`, `μ^(2)` an equilibrium state of `𝖠²` | `group`, `System.proj_sq_group`, `System.pressure_sq`, `entropy_map_group`, `System.lyapunov₁_sq_map_group`, `System.lyapunov₂_sq_map_group`, `System.marginal_sq_map_group`, `System.sq_withRotations`, `System.IsEquilibriumState.map_group` | `Grouping`, `General` | **done** |
| `thm:two-block-normalisation`: uniqueness of `μ^(2)` | `System.unique_sq_equilibrium` | `NoSeparation` | **done**, for `0 < s < 2` and `𝖠²` with a proximal diagonal generator; hypothesis: `FengKaenmakiUnique`. Ergodicity of `μ^(2)` is proved from `thm:eq_state_is_sum` inside `System.main_extended_lt_two'` |
| `eq:energy_def`, `eq:diml_min2` | `energy`, `lyapDim`, `lyapDim_eq` | `LyapunovDim` | **done**, as functions of real parameters `h_0`, `λ_1`, `λ_2` |
| threshold `h_0 < -λ_2 ↔ s < 2 - λ_1/λ_2` (proofs of `thm:main1`, `thm:main2`) | `entropy_lt_iff`, `entropy_le_iff` | `LyapunovDim` | **done** |
| `thm:main1` from `thm:eq_state_proj_dim`: the dichotomy | `min_ne_min_iff`, `min_eq_one_of_le` | `LyapunovDim` | **done** |
| `eq:main_extended1`, `eq:main_extended2` | `ledrappierYoung_small`, `ledrappierYoung_large`, `entropy_lt_of_lt_two` | `LyapunovDim` | **done** |
| pointwise dimension, exact- and double-dimensional measures | `HasLocalDim`, `IsExactDim`, `IsDoubleDim`, `HasLocalDim.unique` | `MeasureDim` | **done**, with closed balls and `Measure.real` |
| `thm:exact-dimensional-mixture` | `IsExactDim.ae_hasLocalDim_add_left`, `IsExactDim.ae_hasLocalDim_add_right`, `IsExactDim.isDoubleDim_add`, `IsExactDim.measure_hasLocalDim_add_left_pos`, `IsExactDim.measure_hasLocalDim_add_right_pos`, `isExactDim_add_iff` | `MeasureDim` | **done**, from `Besicovitch.ae_tendsto_rnDeriv` |
| `eq:restricted-projection-dimensions` | `ae_hasLocalDim_iff_of_le`, `IsExactDim.of_le` | `MeasureDim` | **done** |
| `\overline{\dim}_p`, `\underline{\dim}_H` of measures | `upperLocalDim`, `lowerLocalDim`, `upperPackingDim`, `lowerHausdorffDim`, `IsDoubleDim.upperPackingDim_eq`, `IsDoubleDim.lowerHausdorffDim_eq` | `MeasureDimBounds` | **done**, real-valued; on `ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere |
| `eq:haus_dim_sum` | `upperPackingDim_add`, `lowerHausdorffDim_add`, `IsExactDim.upperPackingDim_add`, `IsExactDim.lowerHausdorffDim_add`, `upperPackingDim_add_of_finiteDimensional` | `MeasureDimBounds`, `LocalDimBounds` | **done**; on a finite-dimensional space the first line holds for all finite Borel measures, the second needs non-zero measures |
| pointwise dimensions of a finite Borel measure on `ℝ^d` lie in `[0, d]` (tex lines 2744 to 2749); exact-dimensional iff `\overline{\dim}_p = \underline{\dim}_H`, both directions (tex lines 2796 to 2797) | `upperLocalDim_nonneg`, `lowerLocalDim_nonneg`, `ae_upperLocalDim_le`, `ae_upperLocalDim_le_one`, `ae_upperLocalDim_le_two`, `IsExactDim.dim_mem_Icc`, `IsDoubleDim.dim_mem_Icc`, `isExactDim_iff_upperPackingDim_eq_lowerHausdorffDim` | `MeasureDimBounds`, `LocalDimBounds` | **done**; the lower bound `0` holds everywhere, the upper bound `d` almost everywhere; the equivalence needs `μ ≠ 0` |
| `eq:dimension_measure_def`, second line | `ofReal_lowerHausdorffDim_le_dimH`, `heavyBallSet`, `dimH_heavyBallSet_le`, `ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional`, `lowerHausdorffDim_eq_toReal_iInf_dimH` | `LocalDimBounds` | **done**, for a non-zero finite Borel measure on a finite-dimensional space |
| `eq:dimension_measure_def`, first line | `le_upperBoxDim_of_measure_pos`, `le_packingDim_of_measure_pos`, `ofReal_upperPackingDim_le_packingDim`, `exists_packingDim_le`, `ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional`, `upperPackingDim_eq_toReal_iInf_packingDim` | `PackingDimMeasure` | **done**, for every finite Borel measure on `ℝ^d`, including the zero measure; no literature input |
| `\overline{\dim}_p(μ + ν) ≥ \overline{\dim}_p(μ)` through `eq:dimension_measure_def` (tex lines 2769 to 2772) | `upperPackingDim_le_of_absolutelyContinuous` | `PackingDimMeasure` | **done**, as the article argues |
| measurability of `τ`, `ω`, `\overline{π}`, `π` | `measurable_tau`, `measurable_omega`, `System.Bounds.measurable_projBar`, `System.Bounds.measurable_proj` | `Measurable` | **done** |
| `H_μ(𝒫_0^{n-1})`, `h_0(μ)`, existence of the limit | `cylinder`, `blockEntropy`, `entropy`, `blockEntropy_add_le`, `tendsto_entropy` | `Entropy` | **done** |
| `λ_1`, `λ_2`, `\overline{λ}`, `Λ`, `eq:eq_state_def`, `f_{1,s}`, `f_{2,s}`, Gibbs measures, the marginals | `System.lyapunov₁`, `System.lyapunov₂`, `System.lyapBar`, `System.energyLim`, `System.IsEquilibriumState`, `System.potential₁`, `System.potential₂`, `IsGibbs`, `System.marginal` | `Thermodynamic` | **done** (definitions); `λ_1`, `λ_2`, `Λ`, `h_0` are literal limits and `eq:eq_state_def` is literal |
| existence of the limits defining `λ_1`, `λ_2`, `Λ`; `-∞ < λ_2 ≤ λ_1 < 0` | `System.tendsto_lyapunov₁`, `System.tendsto_lyapunov₂`, `System.tendsto_energyLim`, `System.lyapunov₁_neg`, `System.lyapunov₂_le_lyapunov₁`, `System.RatioLowerBound.log_le_lyapunov₂` | `Lyapunov` | **done**, by Fekete |
| `eq:energy_def` | `System.energyLim_eq`, `System.IsEquilibriumState.pressure_eq`, `System.IsEquilibriumState.of_pressure_eq` | `Lyapunov` | **done** |
| `\overline{λ}` as the limit of `sec:lyapunov_exponents` equals `∫ f_{1,1} dν` | `System.lyapBarLim`, `System.lyapBarLim_eq` | `Lyapunov` | **done** |
| `P_Z(f)` (tex lines 2575 to 2578), the existence of its limit, the Gibbs constant is `P_Z(f)` | `periodicPoints`, `bijOn_block_periodicPoints`, `periodicSum_eq_finsum`, `pressureZ`, `tendsto_pressureZ`, `tendsto_pressureZ_admissibleSum`, `periodicSum_eq_zero_of_odd`, `pressureZ_comp_flipSymbol`, `IsGibbsAt.pressure_eq`, `IsGibbs.pressure_eq` | `PressureZ` | **done**, literal to the article; the limit over periodic points needs a diagonal generator |
| doubling of Gibbs measures (tex lines 2584 to 2588) | `IsGibbsWith`, `IsGibbsWith.measureReal_cylinder_le_succ`, `IsGibbsWith.doubling`, `IsGibbs.doubling`, `IsGibbsWith.measureReal_preimage_shift_cylinder_le` | `GibbsProperties` | **done**, as the inequality of cylinder measures with its extension to the left; the metric form is not formalised |
| `thm:eq_state_is_sum`: the four decompositions, `λ_1(𝖠, μ) = \overline{λ}(𝖠, μ_1)`, `λ_2(𝖠, μ) = \overline{λ}(𝖠, μ_2)` | `System.GibbsDecomposition`, `FraserJordanJurgaDecomposition` | `Thermodynamic`, `Literature` | hypothesis (section 6) |
| `thm:eq_state_is_sum`: `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` | `System.svfSum_le_admissibleSum`, `System.pressure_eq_pressureZ₁`, `System.pressure_eq_pressureZ₂` | `PressureZ` | **done**, for every box-like system with a diagonal generator and `0 < s < 2`, with no literature hypothesis |
| `thm:eq_state_is_sum`: the integral formulas for `λ_1`, `λ_2`, `μ_2 = flip_*μ_1`, the Gibbs constants are `P(𝖠, s)`, the fourth decomposition follows from the other three | `System.GibbsDecomposition.lyapunov₁_eq_integral`, `System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂`, `System.GibbsDecomposition.lyapunov₂_eq_integral`, `System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂`, `System.GibbsDecomposition.map_flip`, `System.GibbsDecomposition.isGibbsAt₁`, `System.GibbsDecomposition.isGibbsAt₂`, `System.decomposition₂_of_decompositions` | `PressureZ` | **done**, from the decompositions, with no literature hypothesis |
| `μ_1 ≠ μ_2`, `μ_1 ⟂ μ_2` (tex lines 2671 to 2683), `eq:tau_cylinder`, `\overline{τ}_*μ_1 = \overline{ω}_*μ_2` and `\overline{τ}_*μ_2 = \overline{ω}_*μ_1` (tex lines 2695 to 2696), absolute continuity (tex lines 2723 to 2725) | `System.not_isGibbs_potential₁_and_potential₂`, `System.GibbsDecomposition.ne`, `mutuallySingular_of_ergodic_of_ne`, `System.GibbsDecomposition.mutuallySingular`, `cylinder_tau_inter_subshift`, `System.GibbsDecomposition.map_tau_eq_map_omega`, `System.GibbsDecomposition.map_absolutelyContinuous` | `GibbsProperties` | **done**, with no literature hypothesis; `eq:tau_cylinder` needs `n ≥ 1` |
| `thm:entropy_eq_gibbs` | `blockEntropy_map_unCode`, `entropy_map_unCode`, `map_unCode_of_decomposition`, `System.GibbsDecomposition.entropy_eq₁`, `System.GibbsDecomposition.entropy_eq₂` | `EntropyFactor`, `Main` | **done** |
| `eq:proj_eq_is_sum`, `eq:gibbs_proj_dim`, normalised tuple | `map_comp_coding`, `System.exists_decomposition_of_coding`, `System.marginal_decomposition_normalised` | `Main` | **done**; hypotheses: `JordanRapaportDimension`, and for the normalised tuple also `FengKaenmakiGibbs` and `FraserJordanJurgaDecomposition` |
| `eq:proj_eq_is_sum`, `eq:gibbs_proj_dim` for every proximal mixed tuple | `System.marginal_decomposition` | `General` | **done** |
| `eq:simple_lyapunov` | `System.simple_lyapunov` | `General` | **done**, from `MorrisShmerkinLyapunov`, transferred through `𝖠²` when no generator is proximal |
| `thm:eq_state_proj_dim` | `System.eq_state_proj_dim` | `General` | **done**, in the article's form with `\overline{\dim}_p` and `\underline{\dim}_H`; hypotheses: the four of `Literature` |
| `thm:main1` | `System.main1` | `General` | **done**, with the article's hypotheses, `s = dimaff` entering as `0 < s < 2` and `P(𝖠, s) = 0`; hypotheses: the four of `Literature` |
| the remark before `thm:eq_state_proj_dim`: the coordinate marginals are double-dimensional without separation | `System.exists_exactDim_decomposition_of_coding`, `System.marginal_isDoubleDim_normalised`, `System.marginal_isDoubleDim` | `NoSeparation` | **done**, for every proximal box-like tuple with rotations and `0 < s < 2`; hypotheses: `FengHuExactDim`, `FengKaenmakiGibbs`, `FraserJordanJurgaDecomposition` |
| `ex:projection_double_dimensional` | `Example.sys`, `Example.withRotations`, `Example.proximal`, `Example.irreducible`, `Example.strongSeparation`, `Example.projExpSeparation`, `Example.dimaff_pos_lt_one`, `Example.marginal_doubleDim`, `Example.dimH_attractor`, `Example.mutuallySingular_marginal`, `Example.pressure_eq_log_spectralRadius`, `Example.dimaff_charEq`, `Example.eq_dimaff_of_charEq` | `Example` | **done**, including `P(𝖠, t) = log ρ(M(t))` and the characteristic equation; the explicit Lyapunov exponents through the Markov measure and the numerical values (tex lines 3111 to 3154) are not formalised. Hypotheses: `Example.marginal_doubleDim` the four of `Literature`, `Example.dimH_attractor` the eight of the main line |
| `thm:main1`, `thm:main2` for `0 < s ≤ 1`; the common-prefix bound for `Δ_n^Ψ`; `P(𝖠, s) = log ρ` for a positive eigenvector | `System.main1_of_le_one`, `System.main2_of_le_one`, `System.le_gap`, `System.projExpSeparation_of_le_abs`, `System.pressure_le`, `System.transfer`, `System.pressure_eq_log_of_eigenvector` | `Example` | **done** |
| Birkhoff's pointwise ergodic theorem, maximal ergodic theorem | `birkhoff_ae`, `birkhoff_ergodic`, `maximal_ergodic` | `Birkhoff` | **done** |
| `sec:conditional`: `\widehat{ξ}`, conditional measures, Rokhlin's properties | `saturated`, `saturated_eq_comap`, `condMeas`, `setLIntegral_condMeas`, `condMeas_unique`, `condMeas_atom` | `Conditional`, `ConditionalMeasures` | **done**, with `condExpKernel` on a standard Borel space |
| `thm:conditional_measures_of_a_conditional_measure`, `thm:double_conditional`, `thm:finer_partition_dirac_mass` | `condMeas_cond`, `condMeas_cond_of_saturated`, `double_conditional`, `finer_partition_dirac_mass` | `ConditionalLemmas` | **done** |
| conditional information and entropies, `eq:ergodic_entropy_constant` | `condInfo`, `condEntropy`, `localEntropy`, `integrable_condInfo`, `localEntropy_ae_eq` | `Conditional`, `ConditionalMeasures` | **done** |
| `Σ'`, `Σ^τ`, `Σ^ω`, `eq:tau_omega_partition2`, `thm:lyapunov_exponents_via_g_system` | `System.SigmaPrime`, `System.SigmaTau`, `System.SigmaOmega`, `System.slowAxis`, `System.lyapunov_exponents_via_g_system` | `SlowAxis` | **done**; `Σ'` in the box-like form, no Oseledets |
| partitions `ξ_i`, `ξ_1^⊥`, `\overline{ξ}_i`; measurable (Feng, Lemma 4.2); `h_i`, `\overline{h}_i`; `\overline{μ}` | `System.xi`, `System.xiPerp`, `System.xiBar`, `System.isMeasurablePartition_xi`, `…_xiPerp`, `…_xiBar`, `System.dimEntropy`, `System.dimEntropyBar`, `avgMeasure` | `DimPartitions`, `MeasurablePartitions` | **done** |
| `eq:sigma_tau_omega_positive_eq_measure1`, `thm:partitions_xi1`, `thm:partition_tau_conj` | `System.shift_mem_SigmaTau_iff`, `System.partitions_xi1`, `System.partition_tau_conj` | `PartitionIdentities` | **done** |
| ergodicity of the equilibrium state | `System.ergodic_of_gibbsDecomposition`, `System.ergodic_of_hasProximalDiagonal`, `System.IsEquilibriumState.ergodic_of_two_le` | `DimPartitions`, `BernoulliEquilibrium` | **done**; for `0 < s < 2` from `thm:eq_state_is_sum` (hypotheses `FengKaenmakiGibbs`, `FraserJordanJurgaDecomposition`), for `s ≥ 2` from the Bernoulli form; no citation of ergodicity is used |
| `μ(Σ') = 1`, `eq:lyapunov_exponent_gsystem`, `thm:sigma_tau_omega_positive_eq_measure` | `System.measure_SigmaPrime_compl`, `System.lyapunov_exponent_gsystem`, `System.sigma_tau_omega_positive`, `System.irreducible_of_proximal` | `SigmaMeasure` | **done** |
| `thm:gibbs_tau_omega_positive`, `eq:orientation-restrictions` | `System.gibbs_tau_omega_positive`, `System.orientation_restrictions` | `GibbsOrientation` | **done** |
| `h_0(μ) = h(μ)`, `\overline{h}_0(ν) = h(ν)` (tex lines 2087 to 2091) | `integral_sum_negMulLog_condExp_past`, `System.dimEntropy_zero_eq_entropy`, `System.dimEntropyBar_zero_eq_entropy` | `PastEntropy` | **done**, directly, without Shannon–McMillan–Breiman |
| `thm:feng_entropy_as_limit`, `thm:feng_entropy_zero` | `System.feng_entropy_as_limit`, `…_bar`, `System.feng_entropy_zero`, `…_bar` | `FengEntropy` | **done**, from Feng's (4.16) (`FengInfoSum`, `FengInfoSumBar`) and Birkhoff |
| `thm:feng_entropy_kolmogorov_sinai` | | | not formalised and not needed |
| `thm:conditional_two_ways` | `condMeas_transport`, `System.conditional_two_ways` | `ConditionalTwoWays` | **done** |
| `thm:overline_h1_zero`, `thm:overline_h1_zero_large` | `System.overline_h1_zero`, `System.overline_h1_zero_large` | `AverageEntropy` | **done** |
| `thm:overline_h1_large`, `thm:eq_state_h1_large` | `System.overline_h1_large`, `System.eq_state_h1_large` | `EquilibriumEntropyLarge` | **done** |
| `thm:eq_state_h1_zero`, `thm:eq_state_h2_zero`, `thm:orto_partition_dirac` | `System.eq_state_h1_zero`, `System.eq_state_h2_zero`, `System.orto_partition_dirac` | `EquilibriumEntropySmall` | **done** |
| `thm:SOSC_h2_zero` | `System.future_eq_of_proj_eq`, `System.SOSC_h2_zero` | `StrongOpenSetEntropy` | **done**, with Poincaré recurrence |
| `thm:main_extended`, `0 < s < 2` | `System.main_extended_normalised`, `System.main_extended_lt_two'`, `System.main_extended_dimaff` | `MainTwo` | **done**; hypotheses: the eight of the main line |
| `thm:main2` | `System.main2_of_bounds`, `System.main2` | `MainTwo` | **done**; hypotheses: the eight of the main line; the upper bound is the theorem `System.dimH_attractor_le` |
| invariant measures `ν = ∑_i p_i (φ_i)_*ν`, Hutchinson's uniqueness, invariance of the projection of a Bernoulli measure (tex lines 3718 to 3721) | `System.IsInvariantMeasure`, `System.IsInvariantMeasure.unique`, `System.IsInvariantMeasure.sum_eq_one`, `System.isInvariantMeasure_map_proj`, `System.map_proj_eq_of_isInvariantMeasure` | `SelfAffineMeasure`, `InvariantMeasure` | **done**; uniqueness among all Borel probability measures |
| `∑_i |det A_i| ≤ 1` under the strong open set condition, normalised Lebesgue measure on the open set (tex lines 3699 to 3723) | `System.volume_image_phi`, `System.StrongOpenSet.exists_isBounded`, `System.StrongOpenSet.sum_abs_det_le_one`, `System.StrongOpenSet.exists_isInvariantMeasure_isExactDim` | `LebesgueOpenSet` | **done** |
| `thm:main_extended`, `s ≥ 2` | `System.StrongOpenSet.sum_abs_det_eq_one`, `System.main_extended_ge_two` | `MainExtended` | **done**, with no literature hypothesis; rotations, proximality and the projective exponential separation condition are not used. `thm:main2` does not use it |
| `thm:main_extended` | `System.main_extended`, `System.main_extended_min` | `MainExtended` | **done**; hypotheses: those of `System.main_extended_dimaff` |
| `\dim_H X = min{2, dimaff(X)}` under the hypotheses of `thm:main_extended` (paragraph after `eq:hausdorff_ergodic_lyapunov`) | `System.dimH_attractor_eq_min`, `System.dimH_attractor_of_strongOpenSet`, `System.dimH_attractor_of_two_le` | `DimensionFormula` | **done**; hypotheses: the eight of the main line, and none for `dimaff(X) ≥ 2` under the strong open set condition, with no measure assumed |
| `eq:hausdorff_ergodic_lyapunov` (Rossi) | `upperHausdorffDim`, `System.RossiBound`, `IsExactDim.upperHausdorffDim_eq`, `System.upperHausdorffDim_map_proj_eq` | `DimensionFormula` | the bound is the `Prop` `System.RossiBound`, which no theorem takes; equality for the equilibrium state of `thm:main_extended` **done** |


## Remaining work, in order

The four main results are complete, `thm:main_extended` for every `s > 0`, and so is layer E,
whose design `docs/layer-e.md` documents. The comparator pair `Challenge.lean` / `Solution.lean`
audits the seven headline results (section 0).

1. Ergodicity of the equilibrium state produced by `System.exists_isEquilibriumState`: the
   construction gives an invariant measure, and the article's source states an ergodic one. For
   `0 < s < 2` ergodicity of the equilibrium state follows from `thm:eq_state_is_sum`
   (`System.ergodic_of_hasProximalDiagonal`) and for `s ≥ 2` from the Bernoulli form, so the
   gap is the ergodic decomposition of `h_0 + Λ(𝖠, ·, s)` in general.
2. Not formalised: the metric form of the doubling property (tex lines 2584 to 2588), which the
   article does not use; the explicit Lyapunov exponents of `ex:projection_double_dimensional`
   through the Markov measure (tex lines 3111 to 3154); `(π^+)_*μ^+ = π_*μ` (tex lines 896 to
   897), since the library has no one-sided `π^+`; "grouping a Bernoulli measure gives a
   Bernoulli measure" (tex line 2462), which no proof needs.
3. `Literature`: optionally weaken the hypothesis `FraserJordanJurgaDecomposition` to the
   measure `μ_1`, which strengthens every result that takes it; the restatement in
   `Challenge.lean` and `Solution/Definitions.lean` changes with it.
   `System.decomposition₂_of_decompositions` and `System.GibbsDecomposition.map_flip` support
   it: three decompositions and the finiteness of `μ_1` give the fourth and `μ_2 = flip_*μ_1`.
4. Facts proved twice under different names, to be merged:
   `System.GibbsDecomposition.map_unCode_tau₂` and `System.GibbsDecomposition.map_unCode_omega₂`
   in `PressureZ` and `System.GibbsDecomposition.map_tau_eq_map_omega` in `GibbsProperties`;
   `IsGibbsAt` in `PressureZ` and `IsGibbsWith` in `GibbsProperties`, related by `Iff.rfl`.
   `IsBernoulli` of `GibbsProperties` and `bernoulli` of `BernoulliEquilibrium` are not linked;
   `eq_bernoulli_weightMeasure_of_measureReal_cylinder` gives the link.


## Proof routes that differ from the paper

| Result | Paper | Lean |
|---|---|---|
| `thm:A_classification` | Bárány–Käenmäki–Rossi, proof of Lemma 2.2 | Direct proof for every planar tuple, with counterexamples for the implications that need proximality |
| `prop:ssc_no_overlap_not_pesc` | A pair with `λ` transcendental, Bárány–Käenmäki, Lemma 3.8 | Theorem 2.1 of the source applied to `η_n = exp(-n²)`; algebraic independence over `ℚ(λ, t)` |
| Existence of equilibrium states | Käenmäki, Theorems 2.6 and 4.1 | Misiurewicz's averaged block measures and the two-parameter estimate `System.log_svfSum_le_avgBlockMeasure` |
| Natural extension `η_*` | Hahn–Kolmogorov extension | Carathéodory extension of a content on the clopen future sets |
| `thm:sigma_tau_omega_positive_eq_measure` | Birkhoff's theorem | The counting inequality integrated against the invariant measure |
| `thm:feng_entropy_kolmogorov_sinai` | Shannon–McMillan–Breiman | `h_0(μ) = h(μ)` by the chain rule, Lévy's upward theorem and Cesàro averaging |
| `thm:SOSC_h2_zero` | Birkhoff's theorem | Poincaré recurrence |
| `eq:dimension_measure_def`, first line | Packing measure | Modified upper box dimension, dyadic scales and Borel–Cantelli |
| `eq:hausdorff_affinity_upper_bound` | Cited from Falconer | Stopping words in the supremum metric (`System.upperBoxDim_attractor_le`) |
| `thm:main_extended`, `s ≥ 2` | Bernoulli form from `sec:normalisation`, Hutchinson | The same route, with Hutchinson's uniqueness among all Borel probability measures proved |

## Fidelity boundary

Four kinds of assumption are kept apart. The library declares no axiom: every constant depends
on `propext`, `Classical.choice` and `Quot.sound` only, and the comparator permits no other for the headline results.

| Kind | Form in Lean |
|---|---|
| Standing assumptions of a theorem: proximal, with rotations, projective exponential separation, strong open set condition | hypotheses of the statement, as in the article |
| Literature theorems the article cites without proof | `Prop`-valued definitions in `BoxLike/Literature.lean` or `BoxLike/LiteratureFeng.lean`, and in `BoxLike/LiteratureRemarks.lean` when no main result depends on it, quantified over every alphabet and every system, with the exact citation in the doc comment; every result that uses one takes it as an explicit hypothesis, and `Challenge.lean` restates those the headline results take |
| Literature theorems behind claims off the main line | `Prop`-valued definitions beside the results that use them, taken as hypotheses: `System.FraserBound`, `System.FraserROSC` in `FraserChain`, `NoOverlap.BaranyKaenmakiPair`, `NoOverlap.BaranyKaenmakiTheorem` in `NoOverlapExample`; `System.RossiBound` in `DimensionFormula` is taken by no theorem |
| Results of the article not proved | `sorry` endpoints of a statement layer, open rows of section 3; they never become literature hypotheses or axioms |

Rules for a literature statement:

- It is a statement about defined objects only, never about an opaque constant, so that a
  reader can compare it with the cited theorem.
- It carries every hypothesis of the cited theorem. Lean's total functions (`x / 0 = 0`,
  `Real.log 0 = 0`, junk values of limits that do not exist) make an under-hypothesised
  transcription false in a degenerate case.
- It is tested against a degenerate instance (`N = 1`, `λ_1 = λ_2`, all translations zero)
  before it is admitted. A false statement makes every result that takes it vacuous, and
  neither the build nor the comparator shows a trace of it.
- A statement of the three `Literature` modules quantifies over every alphabet `ι : Type u`
  with the instances `[Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]`, and over
  every system, as the cited theorem does. The cited theorems concern the discrete
  `σ`-algebra on the alphabet, which is the instance `MeasurableSingletonClass ι`; without it
  `MorrisShmerkinLyapunov` and `FengKaenmakiGibbs` would be false with the trivial
  `σ`-algebra on `ι`.
- A result that uses it takes it as an explicit hypothesis with the binder of the table below
  and the universe named, `(hfk : FengKaenmakiGibbs.{u})` (section 8).
- A statement that no main result depends on lives in `BoxLike/LiteratureRemarks.lean`.
- A statement that a headline result takes is restated in `Challenge.lean`, whose definition
  block stays identical to `Solution/Definitions.lean`.
- New literature statements need explicit authorisation.

Ergodicity of the equilibrium state is a theorem and no literature hypothesis: for `0 < s < 2`
it follows from `thm:eq_state_is_sum` (`System.ergodic_of_hasProximalDiagonal`), for `s ≥ 2`
from the Bernoulli form (`System.IsEquilibriumState.ergodic_of_two_le`).

| Literature theorem | `Prop` (binder) | State |
|---|---|---|
| Morris–Shmerkin, Theorem 3.1 (arXiv:1602.08789v3), for `eq:simple_lyapunov` | `MorrisShmerkinLyapunov` (`hms`) | declared in `Literature`; compared with the source: faithful. Reductions: two-sided to one-sided shift; transposed tuple for the order of products; the conclusion drops full support |
| Feng–Käenmäki, Proposition 1.2 (arXiv:1009.3129), with `q = s` for `0 < s ≤ 1` and for `1 < s < 2` with `q = 2 - s` for the rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i`: the Gibbs bounds of `thm:irred_eq_state` | `FengKaenmakiGibbs` (`hfk`) | declared in `Literature`; hypothesis `System.Irreducible`, range `0 < s < 2`, conclusion `System.HasGibbsBounds`. For `1 < s < 2`, `‖A'_𝐢‖^{2-s} = φ^s(A_𝐢)` and `A'` is irreducible when `𝖠` is, which justifies the range. Uniqueness is `FengKaenmakiUnique`; ergodicity is a theorem |
| Feng–Käenmäki, Proposition 1.2 (arXiv:1009.3129v1 and Discrete Contin. Dyn. Syst. 30 (2011), p. 700): the uniqueness part of `thm:irred_eq_state` | `FengKaenmakiUnique` (`hfku`) | declared in `LiteratureRemarks`; compared with the source on 2026-09-21: faithful. The source allows `F = ℝ` and every `q > 0`; its irreducibility, no common invariant proper subspace, is `System.Irreducible` for `d = 2`. For `1 < s < 2` it applies to the rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` with `q = 2 - s`. Reduction: two-sided to one-sided shift. Taken by `System.unique_equilibrium_of_lt_two`, `System.unique_equilibrium` and `System.unique_sq_equilibrium`, by no main result; for `s ≥ 2` uniqueness is proved without it |
| Fraser–Jordan–Jurga, Lemma 1.3, Corollaries 1.5 and 1.6 (arXiv:1706.06833), `thm:eq_state_is_sum` | `FraserJordanJurgaDecomposition` (`hfjj`) | declared in `Literature`; hypothesis: an invariant probability measure with `System.HasGibbsBounds`, which is their characterisation of the Käenmäki measure; an invariant measure with these bounds is absolutely continuous with respect to the ergodic one and equals it. Includes Bowen's ergodic Gibbs measures on the mixing `Σ_Z`. Reductions: signed entries to moduli; one-sided to two-sided; three of the four decompositions from the symmetry exchanging the axes. The parts of the source it omits are theorems: the Gibbs constants are `P(𝖠, s)` (`System.GibbsDecomposition.isGibbsAt₁`, `System.GibbsDecomposition.isGibbsAt₂`), `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` (`System.pressure_eq_pressureZ₁`, `System.pressure_eq_pressureZ₂`), and the `f_{2,1}` identities (`System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂`, `System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂`) |
| Jordan–Rapaport, Theorem 1.1 (arXiv:1908.00271), in `eq:gibbs_proj_dim` | `JordanRapaportDimension` (`hjr`) | declared in `Literature`; compared with the source: faithful. `System.ProjExpSeparation` is their Definition 1 verbatim; ratios of either sign are allowed; reductions: two-sided to one-sided shift |
| Feng–Käenmäki, `thm:irred_eq_state`: ergodicity of the equilibrium state | | not declared and not needed: for `0 < s < 2` ergodicity follows from `thm:eq_state_is_sum`, since `μ = q_*μ_1` is a factor of the ergodic `μ_1` (`System.ergodic_of_hasProximalDiagonal`); for `s ≥ 2` the equilibrium state is Bernoulli (`System.IsEquilibriumState.ergodic_of_two_le`) |
| Falconer (1988), cited as Theorem 5.4: `eq:hausdorff_affinity_upper_bound` and the bound for the upper Minkowski dimension (tex lines 573 to 574) | `System.FalconerBoxBound` | a theorem: proved for every box-like system in `FalconerBound` (`System.upperBoxDim_attractor_le`, `System.dimH_attractor_le`); the `Prop` `System.FalconerBoxBound` of `FraserChain` states the bound and holds (`System.falconerBoxBound`) |
| Fraser, Theorem 2.3 and Corollary 2.5 (arXiv:1108.2639v1), `thm:fraser` | `System.FraserBound`, `System.FraserROSC` | declared in `FraserChain`, as the two parts of Theorem 2.3: `System.FraserBound` for every box-like set and `System.FraserROSC` under the rectangular open set condition, stated as in the source, which was read. The first equality `\dim_P X = \overline{\dim}_M X` is proved without them (`System.packingDim_attractor`), and Corollary 2.5 follows from `System.FraserROSC` (`System.FraserROSC.dim_eq_dimaff`) |
| Bárány–Käenmäki, Theorem 2.1 (Adv. Math. 379 (2021), arXiv:1910.04623v4), in `prop:ssc_no_overlap_not_pesc` | `NoOverlap.BaranyKaenmakiTheorem`, `NoOverlap.BaranyKaenmakiPair` | declared in `NoOverlapExample`. `NoOverlap.BaranyKaenmakiTheorem` is the form of the source, compared with arXiv v4 word for word, and `NoOverlap.ssc_no_overlap_not_pesc'` derives the proposition from it. `NoOverlap.BaranyKaenmakiPair` is the form the article uses (tex lines 1481 to 1490), taken by `NoOverlap.ssc_no_overlap_not_pesc`; applied to `η_n = exp(-n²)` the source's form gives a pair with all its properties except the transcendence of `λ`, which the proof does not use (`NoOverlap.exists_pair_of_baranyKaenmakiTheorem`) |
| Rossi, Theorem 2.2, `eq:hausdorff_ergodic_lyapunov` | `System.RossiBound` | declared in `DimensionFormula`; no theorem takes it, since the proof of `thm:main_extended` evaluates the Ledrappier–Young formula to an equality. `System.upperHausdorffDim_map_proj_eq` shows equality in the bound for the equilibrium state |
| Feng, Theorems 1.2 and 1.3 (arXiv:1901.01691v2), `thm:feng1` | `FengLedrappierYoung` (`hly`), `FengLedrappierYoungBar` (`hlyb`) | declared in `LiteratureFeng`; compared with the source: faithful, the cases `s = 2`, `k_1 = k_2 = 1` and `d = 1`. Feng's order of the filtration, of the matrix products and the signs of the formula were checked against the Lean definitions. Reductions: Feng's `Σ'` inside the box-like `Σ'` and partitions modulo null sets; supremum versus Euclidean balls |
| Feng, Lemma 4.6, first identity of (4.16) | `FengInfoSum` (`hfi`), `FengInfoSumBar` (`hfib`) | declared in `LiteratureFeng`; compared with the source: faithful; the identity needs Feng's (4.7) and not ergodicity, and the scalar form is stated without ergodicity. `thm:feng_entropy_as_limit` and `thm:feng_entropy_zero` are derived from it with Birkhoff |
| Birkhoff's pointwise ergodic theorem | | proved: `birkhoff_ae`, `birkhoff_ergodic` in `Birkhoff` |
| Shannon–McMillan–Breiman; Feng (4.17), `thm:feng_entropy_kolmogorov_sinai` | | not needed: `h_0(μ) = h(μ)` and `\overline{h}_0(ν) = h(ν)` are proved directly in `PastEntropy` |
| Feng–Hu, Theorem 2.8 (arXiv:1002.2036v1 and Comm. Pure Appl. Math. 62 (2009), same number): exact-dimensionality of `\overline{π}_*ν` without separation | `FengHuExactDim` (`hfh`) | declared in `LiteratureRemarks`; compared with the source on 2026-09-21: faithful. The source treats `m`-conformal `C^1` systems on the one-sided full shift with closed balls, with no separation condition, maps that need not be distinct and any ergodic `m`; the similarities of `Ψ` are `m`-conformal for every `m`. Reduction: two-sided to one-sided shift, by restriction to the coordinates `k ≥ 0`. Taken only by the remark that the marginals are double-dimensional without separation (`System.marginal_isDoubleDim`) |

The journal versions of Morris–Shmerkin and Jordan–Rapaport were not accessible; their
numbering is that of the arXiv versions. Fraser–Jordan–Jurga was read in the published version,
Feng–Hu and Feng–Käenmäki in the arXiv and the published versions.

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

`LyapunovDim` is arithmetic in real parameters and takes no literature hypothesis.

