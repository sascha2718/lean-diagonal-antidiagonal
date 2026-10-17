# Findings about the manuscript

Findings made while formalising `diagonal-antidiagonal.tex`: statements that need a repair,
hypotheses the proofs do not use, conventions the text leaves implicit, citations that need a
word, and arguments the library shortens. Each item names the label or the tex lines it concerns
and the Lean evidence. Tex line numbers refer to the manuscript revision fingerprinted in
`paper-correspondence.yaml` (SHA-256 `7e3b4a3f…`). This file records state, not history: an item
that the manuscript absorbs is deleted, and a new finding is added where it belongs.

## Statements that need a repair

- **Introduction, tex lines 549 to 551.** The sentence "the intermediate case, irreducible but
  not strongly irreducible, is, up to a linear change of coordinates, exactly the class of
  box-like self-affine sets with rotations" is false as stated. A proximal tuple of
  anti-diagonal matrices only is irreducible and not strongly irreducible, and no basis makes it
  a tuple with rotations, since the type of each matrix does not depend on the basis
  (`boxType_eq_of_conj`). The tuple `A_1 = [[0, 1/2], [1/3, 0]]`, `A_2 = [[0, 1/3], [1/2, 0]]`
  is a counterexample (`antiDiagonalExample`, with `antiDiagonalExample_proximal`,
  `antiDiagonalExample_irreducible`, `antiDiagonalExample_not_stronglyIrreducible`,
  `antiDiagonalExample_not_withRotations` in `BoxLike/Aligned/BoxLikeProximal.lean`). A correct
  wording is "... exactly the class of box-like self-affine sets with rotations, apart from
  tuples of anti-diagonal matrices, whose second iterates are diagonal." The corresponding
  passages of tex lines 447 to 453 and 813 to 815 state the exception and are correct
  (`irreducible_not_stronglyIrreducible_iff_unitBasis`).
- **"Rotating", tex lines 683 to 686 and `thm:box_like_sa` (tex lines 700 to 704).** The
  manuscript does not define a rotating isometry. The lemma holds when "rotating" means that
  `R_i` exchanges the coordinate axes, the convention of tex lines 429 to 432. Under the reading
  "a rotation other than the identity" it fails: `-I` is a diagonal rotation, and the swap
  `[[0, 1], [1, 0]]` is an anti-diagonal reflection. Lean reads "rotating" as exchanging the axes
  (`IsBoxLikeWithRotations`, `box_like_sa_of_contracting` in `BoxLike/Aligned/BoxLikeSA.lean`).
- **`sec:lyapunov_exponents`, tex line 1617.** "`-∞ < λ_2(𝖠, μ) ≤ λ_1(𝖠, μ) < 0`" is stated for
  an arbitrary `𝖠 ∈ GL_2(ℝ)^N`. The first two inequalities hold for every invertible tuple
  (`MatrixTuple.tendsto_lyapunov₂_of_det_ne_zero`,
  `MatrixTuple.lyapunov₂_le_lyapunov₁_of_det_ne_zero`); `λ_1 < 0` needs `‖A_i‖ < 1`
  (`PlanarSystem.lyapunov₁_neg`).
- **`eq:V_lyapunov`, tex lines 1637 to 1641.** The characterisation of `V_𝐢^1` by the rate
  `≤ λ_2` needs `λ_2 < λ_1`, which the surrounding text assumes: for `λ_1 = λ_2` every vector
  satisfies it. Feng's (4.6) has `lim sup` where the article has `lim`; on `Σ'` the limit exists
  for every vector, so the two sets agree there (`MatrixTuple.fengV_eq_filtration`).
- **tex lines 1649 to 1651.** "By (V3), `V_𝐢^1` is one of the coordinate axes" also uses (V2),
  `λ_2 < λ_1` and the identity of `thm:matrix_products_g_derivatives` for the norms of the
  products applied to `e_1`, `e_2` (`System.V_one_eq_axis`).
- **tex lines 1652 to 1653.** "We choose `Σ'` to contain every sequence sharing the past of one
  of its elements; this is possible because the defining growth conditions depend only on past
  coordinates." Saturating an arbitrary Oseledets set with respect to the past need not give a
  Borel or invariant set. The set of all points at which the growth conditions hold is Borel,
  invariant and saturated, and has full measure, which gives the required choice
  (`MatrixTuple.regularSet`, `PlanarSystem.measurableSet_SigmaPrime`,
  `PlanarSystem.shift_mem_SigmaPrime_iff`, `PlanarSystem.mem_SigmaPrime_of_samePast`,
  `MatrixTuple.measure_regularSet_compl_of_ergodic`).
- **`thm:irred_eq_state`, tex lines 2257 to 2274.** The proposition is credited to Feng–Käenmäki,
  Proposition 1.2, for every `s > 0`. That proposition concerns the norm potential `‖·‖^q`; the
  rescaling of tex lines 2270 to 2274 covers `0 < s < 2`, and for `s ≥ 2`, where
  `φ^s = |det|^{s/2}`, the statement is `thm:bernoulli_equilibrium`, which needs neither the
  citation nor irreducibility (`MatrixTuple.irred_eq_state_of_two_le`). The assertion "This
  measure is ergodic" (tex line 2262) is not part of Feng–Käenmäki, Proposition 1.2; it follows
  from uniqueness, as the remark after their (1.4) notes (`MatrixTuple.ergodic_of_unique`).
- **tex line 2387.** "invertible linear changes of coordinates `T` preserves" should read
  "preserve".
- **The potentials at `s = 2`, tex line 2673.** `f_{1,s}`, `f_{2,s}` are defined for
  `0 < s < 2` (tex lines 2541, 2558 and 2586), and the remark "At `s = 2`, the potentials
  coincide" uses them at `s = 2`. With the formula of the case `1 ≤ s < 2` the remark is correct
  (`System.potential₁_two_eq_potential₂_two`, `System.GibbsDecomposition.mu₁_eq_mu₂_of_two` in
  `BoxLike/Support/PotentialsAtTwo.lean`).
- **`thm:exact-dimensional-mixture`, tex line 2743.** The proof is omitted as straightforward,
  while tex lines 2882 and 2924 cite "the differentiation argument in the proof of" the lemma.
  The library supplies the proof from Besicovitch's differentiation theorem
  (`IsExactDim.ae_hasLocalDim_add_left`, `IsExactDim.isDoubleDim_add`).
- **`eq:haus_dim_sum`** is not cited anywhere in the manuscript. It is proved
  (`upperPackingDim_add`, `lowerHausdorffDim_add`).
- **`thm:overline_h1_large`** uses the positivity of one of the pieces `τ(Σ^τ)`, `ω(Σ^ω)`, which
  is `thm:sigma_tau_omega_positive_eq_measure`, without citing it.
- **`ex:projection_double_dimensional`, tex lines 3059 to 3060.** "Hence `Δ_n^Ψ ≥ C c^n` for
  every `n ≥ 1`, giving projective exponential separation and no exact overlaps." The bound
  concerns words of equal length; no exact overlaps between words of different lengths needs a
  further step, the cancellation of a common prefix and the comparison of `u u'` with `u' u`,
  which Lean supplies (`BoxLike/PrescribedExample/Separation.lean`). The prefactor `C ≤ 1` is
  absorbed into the constant.
- **`ex:projection_double_dimensional`, tex lines 3079 to 3081.** The identification of `μ_1`
  with the Markov measure of the matrix `Q` uses the uniqueness of the Gibbs measure and
  `P_Z(f_{1,s}) = 0`, neither of which the text mentions. The uniqueness of the equilibrium state
  of the example follows without `FengKaenmakiUnique`
  (`PrescribedExample.Gibbs.GibbsDecomposition.eq_markov`, `PrescribedExample.equilibrium_spec`).
  The final sentence (tex line 3111), "Each pointwise dimension value occurs on a set of positive
  measure in each projection", is attributed to `thm:eq_state_proj_dim`, whose statement does not
  contain it; it follows from the stated values with `s_2 < s_1` and the proof of that theorem
  (`PrescribedExample.Gibbs.marginal_spec`).

## Introduction

- tex lines 531 to 537 are correct. "When `s < 2`, the exponents are distinct" is
  Morris–Shmerkin through `eq:simple_lyapunov`; "for `s ≥ 2`, the exponents coincide" holds for
  box-like tuples with rotations (`System.IsEquilibriumState.lyapunov_eq_of_two_le`, which needs
  both matrix types); "the strong open set condition is needed only beyond the threshold"
  describes the hypotheses of `thm:main2` and is not a necessity claim
  (`BoxLike/Support/IntroductionClaims.lean`).
- `thm:fraser` uses the upper Minkowski dimension without separation, matching Fraser's
  Theorem 2.3 (arXiv:1108.2639v1). The equality `\dim_P X = \overline{\dim}_M X` is proved for
  every box-like set (`System.packingDim_attractor`), so only the bound by `dimmaff(X)` requires
  the `FraserBound` premise. Given `dim_H X = dimaff(X)`, the dimension chain of tex lines 579 to
  586 follows without a further premise (`System.dim_chain`); the squeeze of the modified
  affinity dimension (tex lines 587 to 589) uses `FraserBound` (`System.dimmaff_eq_dimaff`). The
  forms with suffix `noExactOverlaps` take the hypotheses of `thm:main2`
  (`System.dim_chain_noExactOverlaps`).
- tex lines 581 to 583: the bound of the upper Minkowski dimension by the affinity dimension has
  no citation at this point. It is proved for every planar self-affine set
  (`PlanarSystem.upperBoxDim_attractor_le`).
- tex lines 587 to 589 and 2219: Fraser states no result `dimmaff(X) ≤ dimaff(X)`; the closest
  is the discussion after his Corollary 2.5, which assumes `s_1, s_2 < min{1, d}`. The inequality
  holds for every box-like set and is proved through `s_1, s_2 ≤ dimaff(X)` and Falconer's
  covering argument for the projections (`System.dimmaff_le_dimaff`).
- tex lines 2215 to 2217: the article weights the longer side by the Minkowski dimension of the
  projection of `X` onto the coordinate axis parallel to it; Fraser uses the projection of
  `φ_𝐢(X)` onto the longer side, which for an anti-diagonal product is the other axis. The two
  agree because `s_1 = s_2` whenever an anti-diagonal map exists (`System.wordDim_eq_axis`).
  For a square the choice of side does not matter (`System.modSvf_of_wordBase_eq`).
- The third part of `thm:fraser` (tex lines 471 to 475) needs no rectangular open set condition
  once `dimaff(X) ≤ 2`: full projections give `dimmaff(X) = dimaff(X)`
  (`System.dimmaff_eq_dimaff_of_full`).
- Fraser assumes at least two maps, which `thm:fraser` omits; all three statements hold for a
  single map (`System.fraserBound_of_subsingleton`, `System.fraserROSC_of_subsingleton`).
- Fraser writes (arXiv:1108.2639v1, p. 6) that the zero of his pressure lies in
  `[0, s_1 + s_2]`; this needs the rectangular open set condition, since `∑_i |det A_i| > 1`
  gives `dimmaff(X) > s_1 + s_2`. The article does not use the remark.
- The algebraic-parameter criterion for projective exponential separation (tex lines 411 to 413
  and 497 to 498, after Hochman) is not formalised; no proof uses it.
- The double-dimensionality and the failure of exact-dimensionality in `thm:main1` need only
  `μ_k(τ(Σ)) > 0` and `μ_k(ω(Σ)) > 0` from the Gibbs property.
- `thm:main1` is stated for the unique `s`-equilibrium state; the Lean statement holds for every
  invariant `s`-equilibrium state. Ergodicity of `μ` is not a hypothesis; only the Gibbs
  measures `μ_1`, `μ_2` need to be ergodic, for Jordan–Rapaport. Of `thm:irred_eq_state` only
  the Gibbs bounds are used.
- The case `s ≥ 2` of `thm:main1` and `thm:eq_state_proj_dim` uses the rotations (both matrix
  types with positive weight) and the projective exponential separation condition, and neither
  proximality nor Morris–Shmerkin, Feng–Käenmäki or Fraser–Jordan–Jurga
  (`System.eq_state_proj_dim_of_two_le`, `System.main1_of_two_le`). The parity of the number of
  anti-diagonal symbols among `L` independent symbols has bias `r^L` with `|r| < 1`, which gives
  the mixing of the orientation lift (`tendsto_bernoulli_parity`,
  `tendsto_orientationLift_bernoulli_cylinder_inter`).
- `q:coincident-projection-dimensions` asks whether, below the threshold at `s = dimaff(X)`, the
  two Gibbs components can have equal positive dimension when the projective system has no exact
  overlaps. It imposes no strong separation condition. The question is open; it is recorded as
  the proposition `CoincidentProjectionDimensionsQuestion` (`BoxLike/OpenQuestion.lean`), with no
  answer claimed.
- The equivalence `h_0(μ) < -λ_2 ↔ s < 2 - λ_1/λ_2` in the proofs of `thm:main1` and `thm:main2`
  needs only `s < 2`, `λ_2 < λ_1 < 0` and the equilibrium identity; `0 < s` is not used
  (`entropy_lt_iff`, `entropy_le_iff`).

## Preliminaries: `sec:box_like_self_affine` to `sec:exponential_separation`

- Hutchinson's theorem (tex lines 672 to 677) is proved for every planar self-affine set
  (`PlanarSystem.isCompact_attractor`, `PlanarSystem.eq_attractor`).
- `sec:irreducibility`, the reduction of tex lines 813 to 815: the contraction `‖A_i‖ < 1` of
  tex line 671 is not invariant under conjugation; the basis of unit vectors the text prescribes
  is what keeps the conjugated matrices contracting (`norm_conj_le_of_isUnitBasis`,
  `PlanarSystem.exists_system_of_irreducible`).
- From `thm:A_classification`: "precisely one" of the three conditions holds for every tuple,
  without proximality or invertibility. The "i.e." of item (3) is an unconditional equivalence.
  The "i.e." of item (2) is an equivalence only under proximality, and both directions fail
  without it: the swap matrix `[[0,1],[1,0]]` is anti-diagonal and reducible; the matrix
  `[[0,-1],[1,-1]]` of order three is irreducible, not strongly irreducible and not box-like in
  any basis (`not_tupleIrreducible_swap`, `not_simultaneouslyBoxLike_rotThree`). For invertible
  matrices `A_i 𝒱 = 𝒱` is equivalent to `A_i 𝒱 ⊆ 𝒱`. The lemma needs no literature input. The
  irreducibility of a proximal box-like tuple needs only one anti-diagonal generator, no diagonal
  one, and not `thm:box_like_proximal`. The invariance of the union of the coordinate axes is
  stated at tex lines 434 to 436 and 1499 to 1500.
- `thm:box_like_proximal`: the step of tex lines 800 to 801, that the product contains an
  anti-diagonal matrix, is not needed for the conclusion. The prose proof is formalised
  (`System.Proximal.box_like_proximal`); the weighted-cocycle proof
  `System.Proximal.hasProximalDiagonal_or_sq_of_cocycle` is a second proof.
- `sec:two_sided_shift_space`:
  - `e ∘ σ^+ ≠ σ ∘ e` needs `N ≥ 2`; for the one-letter alphabet both maps coincide.
  - The one-sided projection `π^+` of tex lines 850 to 858 needs `‖A_i‖ < 1` and not the
    invertibility of `A_i` (`BoxLike/Support/OneSidedProjection.lean`).
  - The Hahn–Kolmogorov step (tex lines 872 to 881) suppresses the consistency and countable
    additivity of the cylinder premeasure. Consistency uses invariance of `μ^+`; countable
    additivity follows because cylinders are compact and open for a finite alphabet. Lean
    constructs a content on the algebra of clopen future sets and proves these facts before
    extending it. Passing from cylinders to Borel sets uses generation. The theorem also holds
    for finite invariant measures.
  - Preservation of ergodicity in both directions (tex lines 884 to 885) is stated without
    proof. The converse direction is not trivial; both directions are proved
    (`ergodic_map_eta_iff`), and the equivalence for an existing invariant lift does not need a
    finite alphabet.
- `sec:subshift`, tex lines 934 to 935: "Since `Z²` is a positive matrix, `Σ_Z` is mixing" holds
  exactly when both orientations occur: with diagonal generators only `Σ_Z` splits into two
  clopen invariant halves, with anti-diagonal generators only it has period two
  (`isTopologicallyMixing_subshiftShift_iff`, `not_isTopologicallyMixing_of_forall_eq_zero`,
  `not_isTopologicallyMixing_of_forall_eq_one`). The cited Walters, Theorem 1.31, concerns the
  mixing of Markov measures rather than topological mixing.
- `lem:proj_gap_dominated` uses a common first-row entry, as does `System.gap_le_diagGap`. The
  Lean statement also covers empty and singleton subfamilies. At `n = 0`, both minima use the
  empty-infimum convention `∞`.
- `prop:ssc_no_overlap_not_pesc` uses Bárány–Käenmäki, Theorem 2.1, with `η_n = exp(-n²)` and
  no transcendence assumption on `λ` (tex lines 1460 to 1465;
  `NoOverlap.prop_ssc_no_overlap_not_pesc`, premise `NoOverlap.BaranyKaenmakiTheorem`). The
  construction needs `0 < λ < 1/3`, `0 < t < λ/(1-λ)`, freeness of the homogeneous system and a
  gap eventually below every exponential `c^n` (`NoOverlap.exists_system_of_homFree`). The
  source gives the gap bound with constant one, which suffices for the prose bound with some
  `C_0 > 0` and `n ≥ 1`.
- tex lines 1466 to 1516: every numerical inequality is correct (the largest `x`-values of
  `φ_i(R)` are `8/3`, `19/6`, `11/3`, `9/5`, the largest `y`-value is `0.96`, the four `y`-bands
  are pairwise disjoint, `t < λ/(1-λ) < 4λ`, the `x`-images overlap). The choice of parameters
  outside a countable union of proper algebraic hypersurfaces (tex lines 1475 to 1477) is correct
  (`NoOverlap.exists_params_not_mem_exceptionalSet`). The freeness argument of tex lines 1518 to
  1547 has no gap: multiplicative independence (`NoOverlap.Params.mulIndependent`), equal symbol
  counts (`NoOverlap.Params.count_eq_of_gDeriv_eq`), and the coefficient extraction, which is
  the evaluation at `r_1 = ⋯ = r_5 = q = 0` (`NoOverlap.eq_of_valPoly_eq`). The final decay
  statement (tex lines 1549 to 1555) is used in the form: for every `c > 0`, eventually
  `Δ_n^Ψ < c^n`.
- The free semigroup of `prop:ssc_no_overlap_not_pesc` is over all words of the alphabet of
  `Ψ`, not only admissible ones, as the proof (tex line 1522) and `Δ_n^Ψ` require.
- tex lines 1558 to 1560: `∑_i |det A_i| = λ(r_1 + r_2 + r_3) + r_4 r_5 < 11/100` holds for
  every choice of parameters in the intervals of tex lines 1466 to 1474, and `dimaff(X) < 2`
  follows from `P(𝖠, 2) = log ∑_i |det A_i| < 0`; the example satisfies every hypothesis of
  `thm:main2` (`NoOverlap.dimH_eq_dimaff'`).
- The reformulation "in the norm on affine coefficients" (tex lines 1571 to 1573) is not
  formalised; the lower bound on the distance of distinct cylinder images is
  (`System.StrongSeparation.exists_le_dist_phiWord`).

## `sec:lyapunov_exponents`, `sec:conditional`, `sec:entropies`

- `thm:lyapunov_exponents_via_g_system` uses only (V3) of the filtration and the identity of
  `thm:matrix_products_g_derivatives`; the case split uses `λ_2 < λ_1`, existence of `Σ'` uses
  ergodicity, and proximality and rotations are not used
  (`System.lyapunov_exponents_via_g_system_manuscript`). For box-like tuples the existence of
  `Σ'` needs only Birkhoff's theorem for the lift `(τ_*μ + ω_*μ)/2` (`System.oseledetsSet`,
  `System.measure_SigmaPrime_compl`); for every invertible planar tuple it is Oseledets'
  theorem, proved from Kingman's theorem and the Furstenberg–Kesten limits
  (`MatrixTuple.measure_regularSet_compl_of_ergodic`).
- Feng's set `Σ'` (Duke Math. J. 172 (2023), Section 4) is an invariant Borel set of full
  measure on which his properties (4.1) to (4.4) hold, some of which concern forward time; it
  need not be saturated with respect to the past. His atoms are the article's atoms (tex lines
  1889 to 1906) cut down to his set, and differ from them pointwise in general. The conditional
  measures agree almost everywhere (`System.condMeas_fengXi_ae_eq`,
  `PlanarSystem.condMeas_fengXi_ae_eq`), hence so do the conditional informations, the pointwise
  entropies and the entropies, and the information-sum identity holds for one family exactly when
  it holds for the other (`System.infoSum_fengXi_iff`, `PlanarSystem.infoSum_fengXi_iff`). The
  citation of Feng at tex line 1980 for the article's partitions is therefore correct; one
  sentence to this effect after the definition of the partitions closes the point.
- tex lines 1764 to 1781: for a countable partition `𝒬` the conditional entropy `H_μ(𝒬 | 𝒜)`
  can be `+∞`; the article uses it for finite partitions only
  (`BoxLike/Support/ConditionalInformation.lean`).
- `thm:conditional_measures_of_a_conditional_measure`: the second statement, for `Ξ` a union of
  atoms (tex lines 1815 to 1819), holds `μ`-almost everywhere on `Ξ` without `μ(Ξ) > 0`. The
  first identity `(μ_Ξ)_𝐢^ξ = (μ_𝐢^ξ)_Ξ` needs no measurable partition: it holds for every
  sub-`σ`-algebra of a standard Borel space. `thm:double_conditional` needs only `ξ'` to be a
  measurable partition with `ξ'(x) ⊆ ξ(x)`; the conditional measure of `δ_j` at `j` is `δ_j` for
  every map `ξ` (`condMeas_cond`, `double_conditional`, `condMeas_dirac`).
- `\widehat{ξ}`, "the `σ`-algebra generated by `ξ`" (tex line 1792): for a measurable partition
  the `σ`-algebra of Borel unions of atoms and the pull-back `σ`-algebra of the inducing Borel map
  are equal, exactly and not only modulo null sets (`saturated_eq_comap`), so both readings give
  the same conditional measures.
- `thm:feng_entropy_as_limit` and `thm:feng_entropy_zero`: the scalar parts need neither
  rotations nor proximality, and no ergodicity (`System.infoSum_xiBar`). The constant-multiplicity
  check of tex lines 1956 to 1959 is correct and not needed: Feng's identity holds without his
  assumption (4.7) (`infoSum_of_pullShift`). For the planar part ergodicity cannot be dropped
  from the hypotheses: for `A_1 = diag(1/2, 1/4)`, `A_2 = diag(1/3, 1/9)` and the mean `μ` of the
  Dirac masses at the two constant sequences, `λ_2 < λ_1` but neither constant sequence has the
  backward rates `λ_1`, `λ_2`, so `μ(Σ') = 0`, every partition is trivial modulo `μ`, and the
  identity would give `μ([𝐢|_n]) = ∏_{k<n} μ([i_k])`, that is `1/2 = 2^{-n}`. The identity holds
  whenever `μ(Σ') = 1` (`System.infoSum_xi`, `PlanarSystem.infoSum_xi`).
- The planar part of `thm:feng_entropy_zero` needs `μ(Σ') = 1`: the cylinders `[𝐢|_n]` shrink to
  the points with the future of `𝐢`, and the past is fixed by the atom only on `Σ'`.
- `thm:feng_entropy_kolmogorov_sinai`: the limit holds for every invariant `μ` with `μ(Σ') = 1`,
  without ergodicity or `λ_2 < λ_1` (`System.tendsto_neg_log_cylinder_dimEntropyAt`); ergodicity
  enters only through `μ(Σ') = 1` and the constancy of the limit, and `λ_2 < λ_1` only through
  the definition and measurability of `Σ'`.
- tex lines 2000 to 2007: the supremum defining the Kolmogorov–Sinai entropy is attained at the
  time-zero partition `𝒫` (`isGreatest_partEntropyRate`, `ksEntropy_shift_eq_entropy`). In the
  Shannon–McMillan–Breiman display (tex lines 2008 to 2012) the qualifier "`𝐢 ∈ Σ'`" is
  superfluous: the limit holds for `μ`-almost every `𝐢 ∈ Σ` (`shannonMcMillanBreiman`).
- tex lines 2024 to 2026: `h_0(μ) = h(μ)` and `\overline{h}_0(ν) = h(ν)` hold for every invariant
  measure, with `ξ_0` the partition by the past of any Borel set of full measure; the planar form
  needs `μ(Σ') = 1` to define `ξ_0` (`System.dimEntropy_zero_eq_ksEntropy`,
  `System.dimEntropyBar_zero_eq_ksEntropy`, `integral_sum_negMulLog_condExp_past`).
- `thm:partitions_xi1` and `thm:partition_tau_conj` use only `λ_2 < λ_1` and past saturation,
  and `λ_2 < λ_1` only for the half on `Σ^ω`; proximality, rotations and ergodicity do not enter
  the set identities.

## `sec:affinity_dim`, `sec:normalisation`, `sec:gibbs_measures`

- tex lines 2188 to 2191: the pressure is convex on every interval `[k, k + 1]` and on all of
  `[2, ∞)`, and Lipschitz in `s` without contraction; strict monotonicity and `P(𝖠, s) → -∞`
  need `max_i ‖A_i‖ < 1` (`MatrixTuple.pressure_convexOn_Ici_two`,
  `BoxLike/Support/PressureConvexity.lean`).
- tex lines 2197 to 2200: the covering by `⌈α_1/α_2⌉` balls is correct with Euclidean balls: the
  ellipse `A(B(0, R))` lies in a rectangle with sides `2 α_1(A) R` and `2 α_2(A) R`
  (`Ellipse.exists_strip`). Falconer's bound `eq:hausdorff_affinity_upper_bound` needs only
  `A_i ∈ GL_2(ℝ)` and `‖A_i‖ < 1`; no separation, rotations, proximality or irreducibility
  (`PlanarSystem.upperBoxDim_attractor_le`, `PlanarSystem.dimH_attractor_le`). The theorem
  number "Falconer 1988, Theorem 5.4" (tex line 2206) and Falconer's *Techniques*, §2 (tex line
  2210), are not checked against the sources.
- From the existence of equilibrium states (tex lines 2252 to 2253, Käenmäki, Theorems 2.6 and
  4.1):
  - Existence of an ergodic equilibrium state holds for every tuple of invertible matrices and
    every `s ≥ 0`, as the article states it, with neither irreducibility nor rotations
    (`MatrixTuple.exists_ergodic_isEquilibriumState`). The extreme point is produced as the
    maximiser of a strictly convex weak-star continuous functional of the cylinder masses.
  - The sub-additive variational principle needs a limit measure: for the block measures `μ_n`
    of the construction the inequality `h_0(μ_n) + Λ(𝖠, μ_n, s) ≥ P(𝖠, s) - ε` is false in
    general, since `φ^s` is sub-multiplicative and Jensen's inequality goes the wrong way. What
    survives is the two-parameter estimate `System.log_svfSum_le_avgBlockMeasure` for
    `1 ≤ m ≤ n`, from which a weak-star limit point gives the conclusion.
- tex lines 2279 to 2285: correct; the invariance of `μ` is not used
  (`System.HasGibbsBounds.submultiplicative`).
- The Bernoulli definition (tex lines 2390 to 2397) imposes the cylinder condition at every
  position and states invariance and ergodicity. The one-symbol cylinder case identifies `(p_i)`
  as the marginal distribution. Both properties have Lean proofs
  (`measurePreserving_shift_bernoulli`, `ergodic_shift_bernoulli`).
- tex lines 556 to 563 and 2397 to 2404: the Gibbs bounds alone show that the equilibrium state
  is not quasi-Bernoulli, for every proximal tuple (`S.Proximal`, weaker than a proximal diagonal
  generator); neither `thm:box_like_proximal`, nor second iterates, nor Morris–Shmerkin,
  Lemma 3.5, is used, and of "with rotations" only the anti-diagonal generator
  (`System.IsEquilibriumState.not_quasiBernoulli`). The quantitative form is
  `φ^s(D^n) φ^s(R D^n) ≥ (γ/Γ)^{c_s} ((α/β)^{c_s})^n φ^s(D^n R D^n)`. "Grouping a Bernoulli
  measure in pairs gives a Bernoulli measure" (tex lines 2402 to 2403) is correct and proved
  (`IsBernoulli.map_group`), and the route of the prose through `𝖠²` is formalised
  (`System.IsEquilibriumState.not_isBernoulli_of_two_block`).
- `thm:bernoulli_equilibrium` (tex lines 2411 to 2430): `φ^s = |det|^{s/2}` holds for all real
  `2 × 2` matrices and `s ≥ 2`; at `s = 2` the definition uses the middle branch, and the values
  agree. `P(𝖠, s) = log ∑_i |det A_i|^{s/2}` needs no hypothesis beyond `s ≥ 2`, and
  `λ_1 + λ_2 = ∫ log |det A_{i_0}| dμ` holds for every invariant `μ`. The lemma holds for every
  box-like tuple and every `s ≥ 2`. Lean follows the entropy bound, its equality case and Gibbs'
  inequality, using `entropy_bernoulli` to verify that the Bernoulli measure attains the bound.
- `thm:sigma_tau_omega_positive_eq_measure` does not need a proximal diagonal generator, and has
  a shorter proof: integrating the counting inequality against the invariant measure gives
  `μ([i]) ≤ 2μ(Σ^τ)` for an anti-diagonal `A_i`, with no use of Birkhoff's theorem or of
  `λ_2 < λ_1` (`System.sigma_tau_omega_positive`). The prose proof is formalised as written
  (`System.sigma_tau_omega_positive_eq_measure`).
- `eq:orientation-restrictions` holds for every Borel set `E`, from `thm:eq_state_is_sum` alone;
  only the positivity uses `thm:sigma_tau_omega_positive_eq_measure`.
- Ergodicity of the equilibrium state follows from `thm:eq_state_is_sum` alone, also for
  `μ^(2)`: `μ = q_*μ_1` is a factor of the ergodic `μ_1` (`System.ergodic_of_hasProximalDiagonal`).
- tex lines 2519 to 2522: the limit defining `P_Z(f)` over periodic points exists exactly when
  some generator is diagonal; with anti-diagonal generators only, the sum vanishes for odd `n`
  (`periodicSum_eq_zero_of_odd`). Mixing is not needed. The form with all admissible words has a
  Fekete limit with no hypothesis.
- tex lines 2528 to 2536: the Gibbs cylinder comparison has the correct signs, and the doubling
  conclusion holds for the standard metric `d(𝐢, 𝐣) = 2^{-min{|n| : i_n ≠ j_n}}`, which the text
  does not specify; the doubling constant is the square of the constant of the one-step
  comparison (`IsGibbsPotential.doubling`, `IsGibbs.doubling_symBall`).
- tex lines 2536 to 2538: uniqueness of the ergodic Gibbs measure of a Hölder potential is
  elementary (`IsGibbsPotential.eq_of_ergodic_of_isHolder`), and the constant of a Gibbs measure
  is `P_Z(f)` (`IsGibbsPotential.pressure_eq_of_isHolder`). Existence on the two-sided shift is
  Bowen, LNM 470, Chapter 1; whether the cited Sarig notes treat the one-sided shift, so that the
  natural extension is needed, is not checked. The existence is the unauthorised proposal
  `BowenGibbsExistence` (`BoxLike/Proposals/IBowenGibbs.lean`), whose theorem number is quoted
  from memory.
- tex lines 2617 to 2630: `μ_1 ≠ μ_2` does not need `P_Z(f_{1,s}) = P_Z(f_{2,s})`: the two
  fixed points `(i_0)^∞` and `(i_0 + N)^∞` show that no measure is a Gibbs measure for both
  potentials (`System.not_isGibbs_potential₁_and_potential₂`).
- `eq:tau_cylinder` (tex lines 2631 to 2639) specifies positive `n` and restricts the cylinder
  to `Σ_Z`, matching the identity `[τ(𝐢)|_n] ∩ Σ_Z = τ([𝐢|_n])` (`cylinder_tau_inter_subshift`).
- `thm:eq_state_is_sum`, first line: `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` holds for every
  box-like system with a diagonal generator and `0 < s < 2`, with no proximality, no
  anti-diagonal generator and no equilibrium state. The Gibbs bounds determine `P` for every
  probability measure carried by `Σ_Z`, with no invariance, so the constants of
  `System.GibbsDecomposition` are `P(𝖠, s)`.
- `thm:eq_state_is_sum`: the four decompositions are redundant. Three of them and the finiteness
  of `μ_1` give the fourth, the identities of tex lines 2642 to 2643 and `μ_2 = flip_*μ_1`,
  without the Gibbs property or ergodicity (`System.decomposition₂_of_decompositions`). The
  `f_{2,1}` identities follow from `μ_2 = flip_*μ_1` alone.
- Fraser–Jordan–Jurga's decomposition uses no separation condition; strong separation enters
  their paper only from Section 2 on.
- `eq:simple_lyapunov` is Morris–Shmerkin, Theorem 3.1, directly; Lemmas 3.4 and 3.5 combine to
  it only through the uniqueness of their Proposition 3.3. Morris–Shmerkin order products as
  `A_{x_n} ⋯ A_{x_1}`; their theorem applies to the transposed tuple, which has the same norms of
  products and the same equilibrium states. The citation of Morris–Shmerkin, Theorem 4.2, at tex
  lines 1617 to 1619 is not used by any proof.

## `sec:ledrappier_young_formula` and `sec:dimension_of_projections`

- The text restricts both measures to nonzero finite Borel measures (tex line 2685), supplying
  the nonzero hypotheses in `eq:dimension_measure_def`, `eq:haus_dim_sum` and the
  exact-dimensionality criterion. With Lean's real-valued essential bounds, upper local
  dimensions also need essential boundedness, proved on `ℝ^d` by `ae_upperLocalDim_le`.
- There is no stated convention for `log μ(B(x,r))` when the ball is null. This concerns points
  outside the support and does not affect the almost-everywhere claims. With the library's
  real-valued conventions, `{lowerLocalDim < t}` contains the complement of the support; the
  positive-measure dimension argument uses the `G_δ` set `heavyBallSet` instead.
- `eq:dimension_measure_def`, first line (tex line 2705): it holds as stated for every finite
  Borel measure on `ℝ^d`, including the zero measure. The proof needs no packing measure: the
  modified upper box dimension suffices. The argument of tex lines 2710 to 2715 for
  `\overline{\dim}_p(μ + ν) ≥ \overline{\dim}_p(μ)` and for `eq:haus_dim_sum` formalises as
  written (`upperPackingDim_le_of_absolutelyContinuous`, `BoxLike/Aligned/MeasureDimSets.lean`).
  The characterisation of double-dimensional measures by `\overline{\dim}_p` and
  `\underline{\dim}_H` (tex lines 2737 to 2739) is proved
  (`isDoubleDim_iff_upperPackingDim_lowerHausdorffDim`).
- `thm:feng1`, first clause, covers every planar self-affine set, while the authorised
  `FengLedrappierYoung` quantifies over box-like systems only. The general transcription is the
  unauthorised proposal `PlanarFengLedrappierYoung` (`BoxLike/Proposals/CPlanarFeng.lean`).
- `thm:entropy_eq_gibbs`: block entropies differ by at most `log 2`, as the proof says; the final
  identification of the conditional entropies given the past with the entropy rates uses the
  chain rule, Lévy's upward theorem and Cesàro averaging (`BoxLike/PastEntropy.lean`).
- `thm:eq_state_proj_dim` for `0 < s < 2`: Jordan–Rapaport already gives exact-dimensionality
  under the separation condition, so the invocation of Feng–Hu at tex line 2880 is needed only
  for the remark that the marginals are double-dimensional without separation
  (`System.marginal_isDoubleDim`).

## `sec:average_gibbs` to `sec:dimension_result_proof`

- `thm:gibbs_tau_omega_positive` uses `Σ^τ`, `Σ^ω`, whose dependence on `μ` is fixed in the
  paragraph before the lemma and explicit in Lean, although `μ` is not repeated in the
  statement.
- `thm:conditional_two_ways`: the prose normalises on `E` and `F`, transports, then removes the
  restrictions using `thm:conditional_measures_of_a_conditional_measure`; this is formalised
  (`System.conditional_two_ways_normalised`). A shorter proof transports the unnormalised
  restrictions and uses the uniqueness of conditional measures once, with no positivity
  (`System.conditional_two_ways`).
- `thm:overline_h1_zero`: the separate Feng–Hu invocation in the proof is unused, since
  Jordan–Rapaport already supplies exact-dimensionality under the stated separation condition.
- `thm:overline_h1_zero_large` and `thm:orto_partition_dirac` assume only `h_0 ≤ -λ_2`, as do
  their Lean signatures. The latter proposition contains `thm:eq_state_h2_zero`, whose separate
  refinement proof is retained.
- `thm:overline_h1_large` needs only the preimage identity of cylinders from the proof of
  `thm:partition_tau_conj`, which holds on all of `Σ` without `λ_2 < λ_1`; positivity of one of
  the two sets `T(E)` already gives `\overline{h}_1(μ_1) = h_1(μ)`.
- `thm:SOSC_h2_zero` formalises as written; it uses that `φ_i(U)` is open and that
  `φ_j(\overline{U}) ⊆ \overline{φ_j(U)}`. The recurrence of tex lines 3554 to 3555 comes from
  Poincaré recurrence and ergodicity (`ae_frequently_iterate_mem`).
- `thm:main_extended`: Rossi's bound occurs only in the background (tex lines 2779 to 2785) and
  is not a dependency of the proof; `eq:main_extended1` and `eq:main_extended2` are equalities
  from `thm:feng1`.
- From the proof of `thm:main_extended` for `s ≥ 2` (tex lines 3598 to 3629):
  - Rotations, proximality and the projective exponential separation condition are not used;
    `N ≥ 2` is not needed for this branch.
  - The volume and stationarity arguments formalise as written; the sets `φ_i(V)` are Borel
    because `φ_i` is a continuous injection.
  - The invariance of `π_*μ` needs only the product formula for cylinders at time `0`. Lean
    derives it from the equality case of the entropy bound and Gibbs' inequality rather than
    applying `thm:bernoulli_equilibrium`.
  - The invariant measure is unique among all Borel probability measures; this form of
    Hutchinson's uniqueness theorem is proved, so no literature input is used. Boundedness of
    `V` is needed only for `0 < L²(V) < ∞`, and `∑_i p_i = 1` follows from invariance.
- From the proof of `thm:main2` (tex lines 3673 to 3786), which is formalised along the prose
  (`System.main2_prose`):
  - tex lines 3682 to 3684: the absence of exact overlaps passes to `Φ^(2)` as stated
    (`System.NoExactOverlaps.sq`).
  - tex lines 3702 to 3704 claim that `μ_1` is mixing; only ergodicity is needed. The returns to
    the horizontal orientation along infinitely many lengths come from ergodic Cesàro averages
    (`frequently_measure_inter_shift_ge`).
  - tex lines 3706 to 3708: "for all sufficiently large `n`" is needed only along a sequence of
    lengths, which is what tex line 3723 uses.
  - tex lines 3716 to 3717: "at least `c exp(n(h-ε))`" holds with `c` the lower bound of the
    total mass of the selected words.
  - tex lines 3719 to 3720: the pigeonhole over the `(n+1)^{2N}` count classes loses the factor
    `(n+1)^{2N}` in the cardinality, which is `exp(o(n))`; the limit `log #W_n / n → h` survives
    (`log_card_le_log_card_class_add`).
  - tex lines 3733 to 3735, the trimming: `log ⌊|b_n|⁻¹⌋ / n → -λ_2` uses only `⌊x⌋ ≥ x/2` for
    `x ≥ 1`; the case `h = -λ_2` needs no separate argument, since
    `log min{#W_n, ⌊|b_n|⁻¹⌋} / n → min{h, -λ_2} = h`.
  - tex line 3755, Kittle–Kogler: Theorem 1.1 of arXiv:2610.10511 is stated with the random walk
    entropy `h_μ`; the form `min{1, H_n / χ_{1,n}}` with the Shannon entropy of the weights uses
    `h_μ = H(p)` in the absence of exact overlaps, which the source notes. The literature
    statement `KittleKoglerDimension` takes this form.
  - tex lines 3764 to 3769: the scalar Ledrappier–Young formula is cited from Feng for the
    coordinate projections of a diagonal subsystem. The scalar part of `thm:feng1` (tex lines
    2769 to 2774) concerns proximal box-like systems with rotations, and a diagonal subsystem has
    no rotations; the citation is within Feng's theorem but outside `thm:feng1` as stated. Lean
    derives the scalar formula from the planar `FengLedrappierYoung` applied to an auxiliary
    box-like system carrying the line system (`BoxLike/MainTwoProse/ScalarFeng.lean`); the
    literal transcription is the unused proposal `FengLedrappierYoungBarScalar`.
  - tex lines 3762 to 3776: the independence of past and future of the Bernoulli measure,
    invoked at tex line 3774, is needed already at tex line 3765 to identify the conditional
    entropies `q_{x,n}`, `q_{y,n}` with Feng's entropies
    (`BoxLike/MainTwoProse/PastIndependence.lean`).
  - tex lines 3770 to 3772: `0 ≤ q_n ≤ q_{y,n} = 0` is the monotonicity of conditional entropy
    under refinement (`condEntropyPoint_eq_zero_of_le`).
  - tex line 3773: strong separation of the selected subsystem is proved
    (`System.subsystem_strongSeparation`) and gives unique coding.
  - tex lines 3782 to 3783: the limit uses `0 < -λ_1 < -λ_2` for the continuity of
    `(H, χ_1, χ_2) ↦ min{1, H/χ_1} + (H - χ_1 min{1, H/χ_1}) / χ_2`, and `h ≤ -λ_1 - λ_2`
    (`dim_L ≤ 2`) for its value `dim_L(𝖠, μ)` at `(h, -λ_1, -λ_2)`.
  - The planar Ledrappier–Young formula is the only use of `thm:feng1`; `FengInfoSumBar` and
    `FengLedrappierYoungBar` are not needed for `thm:main2`, and the typical words need no
    `P(𝖠, s) = 0` beyond the equilibrium identity.
  - A second proof (`System.main2_noExactOverlaps_all`) uses, in place of the
    Shannon–McMillan–Breiman theorem and the returns, the Gibbs bounds of `μ_1` with Birkhoff's
    theorem and a parity argument: the parity of the number of anti-diagonal generators is constant on a count class,
    and a class of odd parity becomes diagonal after one anti-diagonal generator is appended to
    every word. It carries the subsystem through an option alphabet with one anti-diagonal word
    of zero weight, which makes it box-like with rotations and proximal.

## `ex:projection_double_dimensional` and the separate example

- The prescribed-dimension example is formalised for every `0 < s_2 < s_1 ≤ 1`
  (`PrescribedExample.projection_double_dimensional`). The source calculations hold:
  `Q_ij = M(s)_ij v_j / v_i` gives the rows `(p, 1-p)`; `C = κ/8` and `c = b/128` give
  `L⁸(E_n) ≤ (b/4) 2^{-n}`; the dimension ratios are as displayed.
- The separate rational two-map system of `BoxLike.Example` has `ρ(M(1)) ≤ 2/15`, giving
  `P(𝖠, 1) ≤ log(2/15)`. Its common-prefix separation bound does not use the equal-derivative
  restriction. The library proves its double-dimensional marginals, pressure and affinity
  characteristic equation.
