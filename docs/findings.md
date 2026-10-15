# Findings about the manuscript

Findings made while formalising `diagonal-antidiagonal.tex`: hypotheses the proofs do not use,
conventions the text leaves implicit, citations that need a word, and arguments the library
shortens. Each item names the label or the tex lines it concerns. Tex line numbers refer to the
manuscript at the time of the finding. This file records state, not history: an item that the
manuscript has absorbed is deleted, and a new finding is added where it belongs.

- `lem:proj_gap_dominated` does not use that `φ_1, …, φ_m` are diagonal: a common first-row
  entry `a` suffices, since `g_i(x) = a_i x + v_i^{(1)}` for diagonal and anti-diagonal `i`
  alike. `System.gap_le_diagGap` is stated in that generality. The hypothesis `m ≤ ℓ` is
  harmless and natural for the application.
- `thm:main1` is stated for every invariant `s`-equilibrium state; ergodicity of `μ` is not a
  hypothesis, and only the Gibbs measures `μ_1`, `μ_2` need to be ergodic, for Jordan–Rapaport.
  Of `thm:irred_eq_state` only the Gibbs bounds are used: Fraser–Jordan–Jurga prove
  `thm:eq_state_is_sum` for the measure characterised by these bounds, and
  `FengKaenmakiGibbs` is the passage from the variational definition to them.
- `thm:box_like_proximal` holds for every box-like tuple; the hypothesis "with rotations" is
  not used.
- `eq:haus_dim_sum` is stated in the article for all finite Borel measures. With real-valued
  essential bounds the first line needs the upper pointwise dimensions essentially bounded,
  which holds on `ℝ^d` (`ae_upperLocalDim_le`, `upperPackingDim_add_of_finiteDimensional`),
  and the second needs both measures non-zero, since the essential infimum over the zero
  measure is not `+∞`. For the zero measure the article's second line reads
  `min{\underline{\dim}_H(μ), +∞}`, so the article is correct with the convention
  `inf ∅ = +∞`; the hypothesis is an artefact of real values.
- From `sec:ledrappier_young_formula`:
  - tex lines 2744 to 2749: there is no convention for `log μ(B(x,r))` when the ball is null.
    The article never states that the pointwise dimensions lie in `[0, d]`; the lower bound
    holds everywhere, the upper bound only almost everywhere, and the real-valued `esssup` and
    `essinf` of tex lines 2758 to 2759 rely on it.
  - `eq:dimension_measure_def`, second line: it needs `μ ≠ 0`; the restriction to Borel sets
    is not needed. With the library conventions the set `{lowerLocalDim < t}` is the wrong
    witness, since it contains the complement of the support; the witness is the `G_δ` set
    `heavyBallSet`.
  - `eq:dimension_measure_def`, first line: it holds as stated for every finite Borel measure
    on `ℝ^d`, including the zero measure, for which both sides vanish; the restriction to
    Borel sets and the boundedness of the pieces in the definition of `\dim_P` play no role.
    The proof needs no packing measure: the modified upper box dimension suffices (dyadic
    scales and the Borel–Cantelli lemma for the lower bound, a count of separated points for
    the upper bound). With real-valued essential bounds it needs `\overline{\dim}_{loc}(μ, ·)`
    essentially bounded, which holds on `ℝ^d`. The argument of tex lines 2769 to 2772 for
    `\overline{\dim}_p(μ + ν) ≥ \overline{\dim}_p(μ)` formalises as written.
  - tex lines 2796 to 2797: the equivalence "exact-dimensional if and only if
    `\overline{\dim}_p(μ) = \underline{\dim}_H(μ) = \dim(μ)`" needs `μ ≠ 0`.
- From the statement layer of layer E (`docs/layer-e.md`, section 5, has the details and says which
  points were checked and which only read):
  - `thm:lyapunov_exponents_via_g_system` is true by definition of the box-like `Σ'`; its
    hypotheses only serve `μ(Σ') = 1`, which needs Birkhoff and not Oseledets.
  - Ergodicity of the equilibrium state follows from `thm:eq_state_is_sum` alone, also for
    `μ^(2)`; `thm:main2` uses `thm:irred_eq_state` only through the Gibbs bounds.
  - The appeal to Rossi's bound in the proof of `thm:main_extended` is unused.
  - `thm:overline_h1_zero_large` and `thm:orto_partition_dirac` assume
    `-λ_1 ≤ h_0 ≤ -λ_2`, and their proofs use only `h_0 ≤ -λ_2`.
  - `h_0` and `\overline{h}_0` carry two meanings, `H(𝒫 | \widehat{ξ}_0)` and the
    Kolmogorov–Sinai entropy. The identification `\overline{h}_0(ν) = h(ν)` is asserted
    without lemma or citation and is used in three proofs.
  - `thm:gibbs_tau_omega_positive` uses `Σ^τ`, `Σ^ω`, which depend on the equilibrium state
    `μ`, which the statement does not mention.
  - `thm:sigma_tau_omega_positive_eq_measure` does not need a proximal diagonal generator;
    its Birkhoff display lacks the almost-everywhere qualifier.
  - `thm:partitions_xi1` and `thm:partition_tau_conj` use only `λ_2 < λ_1` and past
    saturation.
  - `eq:V_lyapunov` has `lim` where Feng has `lim sup`; harmless on `Σ'`.
- From the comparison of Feng's results with the source: the box-like `Σ'` of tex lines 1675
  to 1682 is not itself an admissible choice of Feng's `Σ'`, which must also satisfy the
  forward-time properties (4.2) and (4.3); a past-saturated set cannot guarantee these
  pointwise. The box-like `Σ'` contains an admissible one, the partitions agree there, and
  partitions agreeing on a set of full measure have `σ`-algebras equal modulo null sets. One
  sentence to this effect near tex line 1964 closes the point.
- From the proofs of `sec:average_gibbs` to `sec:dimension_result_proof`:
  - `thm:conditional_two_ways`: one application of uniqueness of conditional measures
    suffices; the normalisation, `thm:conditional_measures_of_a_conditional_measure` and
    `μ(E) > 0` are not needed. The kernel `K_𝐣` of the article is defined on `F` only and its
    measurability is asserted without proof; it uses that `F` is a union of `\overline{ξ}_1`
    atoms and that `T` maps atoms onto atoms, both from `thm:partitions_xi1`. The closing
    remark that the four sets `F` partition a set of full measure is not used.
  - `thm:overline_h1_zero`: the strict inequality `-h_0/λ_2 < -h_0/λ_1` of tex lines 3361 to
    3364 needs `h_0(μ) > 0`, which is not stated; the argument needs only `-h_0/λ_2 ≤ 1`. The
    last display of the proof uses the second line of `thm:gibbs_tau_omega_positive` without
    citing it.
  - `thm:overline_h1_zero_large` and `thm:orto_partition_dirac` do not use the lower bound
    `-λ_1 ≤ h_0`; the latter therefore contains `thm:eq_state_h2_zero`. Checked in Lean.
  - `thm:overline_h1_large` needs only the preimage identity of cylinders from the proof of
    `thm:partition_tau_conj`, which holds on all of `Σ` without `λ_2 < λ_1`; and positivity of
    one of the two sets `T(E)` already gives `\overline{h}_1(μ_1) = h_1(μ)`.
  - `thm:SOSC_h2_zero` formalises as written; it uses that `φ_i(U)` is open and that
    `φ_j(\overline{U}) ⊆ \overline{φ_j(U)}`, and Poincaré recurrence suffices in place of
    Birkhoff's theorem.
  - The appeal to Rossi's bound in the proof of `thm:main_extended` is unused, and `thm:main2`
    uses `thm:irred_eq_state` only through the Gibbs bounds: ergodicity of the equilibrium
    state follows from `thm:eq_state_is_sum`.
- From the proofs of layer E:
  - `thm:conditional_measures_of_a_conditional_measure`, first part, needs neither a
    measurable partition nor `μ(Ξ) > 0`; `thm:double_conditional` needs only `ξ'` to be a
    measurable partition with `ξ'(x) ⊆ ξ(x)`; the conditional measure of `δ_j` at `j` is `δ_j`
    for every map `ξ`.
  - `thm:partitions_xi1` uses only `λ_2 < λ_1`, and only for the half on `Σ^ω`.
  - `thm:sigma_tau_omega_positive_eq_measure` has a shorter proof: integrating the counting
    inequality against the invariant measure gives `μ([i]) ≤ 2μ(Σ^τ)` for an anti-diagonal
    `A_i`, with no use of Birkhoff's theorem or of `λ_2 < λ_1`.
  - `eq:orientation-restrictions` holds for every Borel set `E`, from `thm:eq_state_is_sum`
    alone; only the positivity uses `thm:sigma_tau_omega_positive_eq_measure`.
  - `μ(Σ') = 1` needs only Birkhoff's theorem, applied to a shift-invariant lift of `μ`.
  - `h_0(μ) = h(μ)` in the planar case needs `μ(Σ') = 1`; the scalar identity
    `\overline{h}_0(ν) = h(ν)` holds for every invariant `ν` on `Σ_Z`, as tex line 2091 says,
    and is proved (chain rule, Lévy's upward theorem, Cesàro).
  - The planar part of `thm:feng_entropy_zero` needs `μ(Σ') = 1`: the cylinders `[𝐢|_n]` shrink
    to the points with the future of `𝐢`, and the past is fixed by the atom only on `Σ'`.
- For the tex file, from the source checks of 2026-09-20 and 2026-09-21:
  - `thm:irred_eq_state` attributes the statement for `φ^s` and every `s > 0` to
    Feng–Käenmäki, Proposition 1.2. That proposition concerns the norm potential `‖·‖^q`,
    which is `φ^s` only for `s ≤ 1`. For `1 < s < 2` Fraser–Jordan–Jurga and Morris–Shmerkin
    cite the closing remark of Feng–Käenmäki and Käenmäki–Reeve. The proposition applies
    directly to the rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` with `q = 2 - s`,
    since `‖A'_𝐢‖^{2-s} = φ^s(A_𝐢)` and `A'` is irreducible when `𝖠` is; one sentence on the
    rescaling repairs the citation for `1 < s < 2`. For `s ≥ 2` existence, uniqueness and
    ergodicity hold for every box-like tuple, with no citation and no irreducibility: the
    equilibrium state is Bernoulli (`System.existsUnique_isEquilibriumState_of_two_le`,
    `System.IsEquilibriumState.ergodic_of_two_le`).
  - `eq:simple_lyapunov` is Morris–Shmerkin, Theorem 3.1, directly; Lemmas 3.4 and 3.5 combine
    to it only through the uniqueness of their Proposition 3.3.
  - Morris–Shmerkin order products as `A_{x_n} ⋯ A_{x_1}`; their theorem applies to the
    transposed tuple, which has the same norms of products and the same equilibrium states.
  - Fraser–Jordan–Jurga's decomposition uses no separation condition; strong separation
    enters their paper only from Section 2 on. This confirms the coauthors' reading.
- The Gibbs property enters `thm:main1` only through `μ_k(τ(Σ)) > 0` and `μ_k(ω(Σ)) > 0`.
- The equivalence `h_0(μ) < -λ_2 ↔ s < 2 - λ_1/λ_2` in the proofs of `thm:main1` and
  `thm:main2` needs only `s < 2`, `λ_2 < λ_1 < 0` and the equilibrium identity; `0 < s` is not
  used (`entropy_lt_iff`, `entropy_le_iff`).
- From `sec:two_sided_shift_space`:
  - tex lines 851 to 853: `e ∘ σ^+ ≠ σ ∘ e` needs `N ≥ 2`.
  - tex lines 883 to 894: the text shows only the surjectivity of `η_*`; injectivity is not
    argued, and it holds by invariance and generation. tex lines 884 to 886: the consistency of
    the premeasure on cylinders is never checked; it is the only place where the invariance of
    `μ^+` is needed. tex line 886: Hahn–Kolmogorov needs `σ`-additivity on the algebra of
    cylinders, which is not verified; it holds because the alphabet is finite, so that
    cylinders are compact and open, and this is the only use of finiteness. tex lines 887 to
    892: the display brings in invariance where it is not needed, and the invariance of `μ`
    from its values on cylinders needs a tacit `π`-system argument. tex line 893: bijectivity
    also needs `η_*μ = μ^+`, which is never stated. The statement holds for finite invariant
    measures.
  - tex line 894: "`η_*μ` is ergodic if and only if `μ` is" is stated without proof. The
    converse direction is not trivial; both directions are proved, and neither needs a finite
    alphabet.
- From `thm:A_classification`: "precisely one" of the three conditions holds for every tuple,
  without proximality or invertibility. The "i.e." of item (3) is an unconditional
  equivalence. The "i.e." of item (2) is an equivalence only under proximality, and both
  directions fail without it: the swap matrix `[[0,1],[1,0]]` is anti-diagonal and reducible;
  the matrix `[[0,-1],[1,-1]]` of order three is irreducible, not strongly irreducible and not
  box-like in any basis. For invertible matrices `A_i 𝒱 = 𝒱` is equivalent to `A_i 𝒱 ⊆ 𝒱`.
  The lemma needs no literature input. The irreducibility of a proximal box-like tuple needs
  only one anti-diagonal generator, no diagonal one, and not `thm:box_like_proximal`. The
  sentence on the union of the coordinate axes is at tex lines 1594 to 1595.
- From the existence of equilibrium states (tex lines 2322 to 2323, Käenmäki, Theorems 2.6 and
  4.1):
  - Existence needs neither irreducibility nor rotations, and holds for every `s ≥ 0`, as the
    article states it; `thm:irred_eq_state` uses irreducibility only for uniqueness and for the
    Gibbs bounds.
  - The sub-additive variational principle needs a limit measure: for the block measures
    `μ_n` of the construction the inequality `h_0(μ_n) + Λ(𝖠, μ_n, s) ≥ P(𝖠, s) - ε` is false
    in general, since `φ^s` is sub-multiplicative and Jensen's inequality goes the wrong way.
    What survives is the two-parameter estimate `System.log_svfSum_le_avgBlockMeasure` for
    `1 ≤ m ≤ n`, from which a weak-star limit point gives the conclusion.
- From `sec:affinity_dim` and `sec:normalisation`:
  - tex lines 2335 to 2338: correct; the invariance of `μ` is not used.
  - tex lines 2451 to 2456: the definition of a Bernoulli measure does not say that `(p_i)` is
    its one-symbol distribution. The sentence "It is well-known that `μ ∈ ℳ_σ(Σ)` is ergodic"
    of tex line 2456 lacks its subject; a suggested wording is "A Bernoulli measure is
    `σ`-invariant and ergodic". Both properties are proved; invariance follows from the
    definition, since the cylinder condition is imposed at every position.
  - tex lines 555 to 560 and 2457 to 2463: the Gibbs bounds alone show that the equilibrium
    state is not quasi-Bernoulli, for every proximal tuple (`S.Proximal`, weaker than a
    proximal diagonal generator). Neither `thm:box_like_proximal`, nor second iterates, nor
    Morris–Shmerkin, Lemma 3.5, is used, and of "with rotations" only the anti-diagonal
    generator. The quantitative form is
    `φ^s(D^n) φ^s(R D^n) ≥ (γ/Γ)^{c_s} ((α/β)^{c_s})^n φ^s(D^n R D^n)`. The claim "grouping a
    Bernoulli measure in pairs gives a Bernoulli measure" (tex line 2462) is not needed.
  - tex line 2471: `φ^s = |det|^{s/2}` holds for all real `2 × 2` matrices and `s ≥ 2`; at
    `s = 2` the definition uses the middle branch, and the values agree.
    `P(𝖠, s) = log ∑_i |det A_i|^{s/2}` needs no hypothesis beyond `s ≥ 2`, and
    `λ_1 + λ_2 = ∫ log |det A_{i_0}| dμ` holds for every invariant `μ`. tex lines 2471 to 2479
    hold for every box-like tuple and every `s ≥ 2`.
  - tex lines 2477 to 2479: both claims are correct and no proof is given; the route is
    Fekete's lemma, `H_n = nH_1` and the equality case of subadditivity. The "Indeed" sentence
    proves uniqueness only; existence needs that a Bernoulli measure has the entropy of its
    one-symbol distribution (`entropy_bernoulli`).
- From `sec:gibbs_measures` and `thm:eq_state_is_sum`:
  - tex lines 2575 to 2578: the limit defining `P_Z(f)` over periodic points exists exactly
    when some generator is diagonal; with anti-diagonal generators only, the sum vanishes for
    odd `n`. Mixing is not needed. The form with all admissible words has a Fekete limit with
    no hypothesis.
  - tex lines 2584 to 2588: the signs are correct, with the sharp constant
    `C² exp(P - f(σ^n 𝐢))`. The range `n ∈ ℕ` includes `n = 0`, where the Gibbs property is
    not stated; this case needs `ν(Σ_Z) = 1` and `C ≥ 1`. On the two-sided shift balls are
    two-sided cylinders, so doubling also needs the extension to the left, which follows from
    invariance (`IsGibbsWith.measureReal_preimage_shift_cylinder_le`). The article does not
    use the metric statement of doubling.
  - tex lines 2671 to 2683: `μ_1 ≠ μ_2` does not need `P_Z(f_{1,s}) = P_Z(f_{2,s})`: the two
    fixed points `(i_0)^∞` and `(i_0 + N)^∞` show that no measure is a Gibbs measure for both
    `f_{1,s}` and `f_{2,s}` (`System.not_isGibbs_potential₁_and_potential₂`).
  - `eq:tau_cylinder` needs `n ≥ 1`; in the library it reads `[τ(𝐢)|_n] ∩ Σ_Z = τ([𝐢|_n])`.
  - `thm:eq_state_is_sum`, first line: `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` holds for every
    box-like system with a diagonal generator and `0 < s < 2`, with no proximality, no
    anti-diagonal generator and no equilibrium state. `P_Z(f_{1,s}) = P_Z(f_{2,s})` is an exact
    symmetry of the sums. The Gibbs bounds determine `P` for every probability measure carried
    by `Σ_Z`, with no invariance, so the existential constants of `System.GibbsDecomposition`
    are `P(𝖠, s)`.
  - `thm:eq_state_is_sum`: the four decompositions are redundant. Three of them and the
    finiteness of `μ_1` give the fourth, the identities of tex lines 2695 to 2696 and
    `μ_2 = flip_*μ_1`, without the fourth decomposition, the Gibbs property or ergodicity. The
    `f_{2,1}` identities follow from `μ_2 = flip_*μ_1` alone.
- From `ex:projection_double_dimensional`, which lies in `sec:dimension_of_projections`: every
  number is correct. `ρ(M(1)) ≤ 2/15` is the largest row sum and equals `∑_i ‖A_i‖`, so
  `P(𝖠, 1) ≤ log(2/15)` follows from the first term of the sub-additive sequence without `M`.
  The common-prefix argument does not use the equal-derivative condition of `Δ_n^Ψ`. tex lines
  3147 to 3148: the distinctness of the two values needs only `s > 0` and `λ_2 < λ_1 < 0`;
  `s ≤ 1` gives `h_0 = -sλ_1`, and everything holds at `s = 1`. For `dimaff ≤ 1` the alternative
  hypothesis of `thm:main2` holds automatically (`System.main2_of_le_one`). The Markov-measure
  formulas and the numerical values of tex lines 3148 to 3154 are not formalised; a floating
  point computation outside Lean agrees with the article (`s = 0.22668…`, `λ_1 = -3.01516…`,
  `λ_2 = -3.08164…`).
- From the proof of `thm:main_extended` for `s ≥ 2`:
  - Rotations, proximality and the projective exponential separation condition are not used.
  - tex line 3692: `N ≥ 2` is not needed for the statements about `s ≥ 2`. tex lines 3699 to
    3723 formalise as written; the sets `φ_i(V)` are Borel because `φ_i` is a continuous
    injection.
  - tex line 3718: the invariance of `π_*μ` needs only the product formula for cylinders at
    time `0`.
  - tex line 3720: the invariant measure is unique among all Borel probability measures.
    Boundedness of `V` is needed only for `0 < L²(V) < ∞`, and `∑_i p_i = 1` follows from
    invariance.
- From the introduction and `sec:exponential_separation`, as stated in `FraserChain` and
  `NoOverlapExample`:
  - `thm:fraser` (tex lines 469 to 483, also tex lines 572, 578 and 2277) writes `\dim_M X`
    for every box-like set. Fraser's Theorem 2.3 (arXiv:1108.2639v1) gives
    `\dim_P X = \overline{\dim}_M X ≤ dimmaff(X)` without a separation condition and the
    existence of `\dim_M X` only under the rectangular open set condition; the first display
    of `thm:fraser` should read "upper Minkowski dimension". The equality
    `\dim_P X = \overline{\dim}_M X` holds for every box-like set
    (`System.packingDim_attractor`). Under the hypotheses of `thm:main2` the chain of tex lines
    575 to 577 gives the existence of `\dim_M X` (`System.dim_chain_main2`), so tex lines 575
    to 581 are correct.
  - tex lines 578 to 579 and 2277: Fraser states no result `dimmaff(X) ≤ dimaff(X)`; the
    closest is the discussion after his Corollary 2.5, which assumes `s_1, s_2 < min{1, d}`.
    The inequality is true for every box-like set and proved here through `s_1, s_2 ≤ dimaff(X)`,
    Falconer's covering argument for the projections (`System.dimmaff_le_dimaff`).
  - tex lines 582 to 584: the strict inequality `dimmaff(X) < dimaff(X)` is not Fraser's
    Corollary 2.5, which is the equality statement; it comes from the discussion after it,
    under `s_1, s_2 < min{1, d}` and a domination condition `α_2(A_𝐢) ≤ η^k α_1(A_𝐢)`.
  - tex lines 2273 to 2275: the article weights the longer side by the Minkowski dimension of
    the projection of `X` onto the coordinate axis parallel to it; Fraser uses the projection
    of `φ_𝐢(X)` onto the longer side, which for an anti-diagonal product is the other axis. The
    two agree because `s_1 = s_2` whenever an anti-diagonal map exists
    (`System.wordDim_eq_axis`); Fraser's wording is the precise one. For a square the choice of
    side does not matter (`System.modSvf_of_wordBase_eq`).
  - tex lines 478 to 482: the third part of `thm:fraser` needs no rectangular open set
    condition once `dimaff(X) ≤ 2`: full projections give `dimmaff(X) = dimaff(X)`
    (`System.dimmaff_eq_dimaff_of_full`).
  - Fraser assumes at least two maps, which `thm:fraser` omits; the omission is harmless, since
    all three statements hold for a single map (`System.fraserBound_of_subsingleton`,
    `System.fraserROSC_of_subsingleton`).
  - Fraser writes (arXiv:1108.2639v1, p. 6) that the zero of his pressure lies in
    `[0, s_1 + s_2]`; this needs the rectangular open set condition, since `∑_i |det A_i| > 1`
    gives `dimmaff(X) > s_1 + s_2`. The article does not use the remark.
  - Falconer's bound (tex lines 2255 to 2265) needs only `max_i ‖A_i‖ < 1`, stated at tex
    lines 2249 to 2250; no separation, rotations, proximality or irreducibility. For box-like
    maps in the sup metric it is elementary (stopping words on `α_1` for `s ≤ 1` and on `α_2`
    for `1 < s ≤ 2`) and proved (`System.upperBoxDim_attractor_le`). At tex lines 2258 to 2260
    the number `α_1/α_2` of balls should be rounded up; the exponent is unaffected. The bound
    of tex lines 573 to 574 has no citation and concerns the upper Minkowski dimension, which
    is all the argument uses. The theorem number "Falconer 1988, Theorem 5.4" (tex line 2264)
    and Falconer's *Techniques*, §2 (tex line 2268), are not checked against the sources.
  - `prop:ssc_no_overlap_not_pesc`: "Fix such a pair with `λ` transcendental" (tex lines 1488
    to 1490) is never used. The inequality `λ ≠ r_1` (tex lines 1520 to 1521) and the
    multiplicative independence (tex lines 1543 to 1545) need only the algebraic independence
    over `ℚ(λ, t)` and `λ ∈ (0, 1)`. The uncountability of the first-coordinate projection
    (tex lines 1484, 1488 to 1489) and the appeal to the construction of Bárány–Käenmäki,
    Lemma 3.8, are therefore unnecessary: Theorem 2.1 as stated, applied to
    `η_n = exp(-n²)`, suffices (`NoOverlap.ssc_no_overlap_not_pesc'`). The proof needs
    `0 < λ < 1/3`, `0 < t < λ/(1-λ)`, the freeness of the homogeneous system and a gap
    `Δ_n^{λ,t}` eventually below every exponential `c^n` (`NoOverlap.exists_system_of_homFree`).
  - tex lines 1481 to 1482: "applied to a sufficiently small constant multiple of `η_n`" is
    superfluous for Theorem 2.1 as stated, which gives `Δ_n^{λ,t} < η_n`; a constant occurs
    only inside its proof.
  - tex line 1487: "for all `n`" should read `n ≥ 1`, since `Δ_0 = ∞`.
  - tex lines 1491 to 1541: every numerical inequality is correct (the largest `x`-values of
    `φ_i(R)` are `8/3`, `19/6`, `11/3`, `9/5`, the largest `y`-value is `0.96`, the four
    `y`-bands are pairwise disjoint, `t < λ/(1-λ) < 4λ`, the `x`-images overlap). The
    freeness argument of tex lines 1543 to 1572 has no gap; its coefficient extraction is the
    evaluation at `r_1 = ⋯ = r_5 = q = 0`. The choice of parameters by a countable union of
    hypersurfaces (tex lines 1501 to 1502) is correct.
  - The free semigroup of `prop:ssc_no_overlap_not_pesc` is over all words of the alphabet
    of `Ψ`, not only admissible ones, as the proof (tex line 1547) and `Δ_n^Ψ` (tex line 1421)
    require. The reformulation "in the norm on affine coefficients" (tex lines 1591 to 1593)
    is not formalised.

