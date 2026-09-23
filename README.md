# BoxLike

A Lean 4 formalisation of `diagonal-antidiagonal.tex`, "Hausdorff dimension of planar
box-like self-affine sets with rotations" by Allen, Käenmäki, Prokaj, Simon and Troscheit.
The library is built on Mathlib alone. It proves the four main results of the article:
`thm:main1` (`System.main1_dimaff`), `thm:eq_state_proj_dim` (`System.eq_state_proj_dim`),
`thm:main_extended` for every `s > 0` (`System.main_extended`, `System.main_extended_min`) and
`thm:main2` (`System.main2`): for a proximal box-like self-affine set `X` with rotations
satisfying the projective exponential separation condition with `dimaff(X) < 2`, if
`dimaff(X) ≤ 2 - λ_1/λ_2` or `X` satisfies the strong open set condition, then
`\dim_H(X) = dimaff(X)`. Under the hypotheses of `thm:main_extended` it proves
`\dim_H(X) = min{2, dimaff(X)}` (`System.dimH_attractor_eq_min`). Off the main line it proves
`thm:A_classification`, `ex:projection_double_dimensional`, `prop:ssc_no_overlap_not_pesc`,
the uniqueness part of `thm:irred_eq_state`, the natural extension of the one-sided shift, and
the chain `\dim_H(X) = \dim_P(X) = \dim_M(X) = dimaff(X)` of the introduction. On the way it
develops the symbolic coding by a sub-shift of finite type, box-like systems and their
projective systems, the singular value pressure and the affinity dimension, the
Kolmogorov–Sinai entropy and Lyapunov exponents of shift-invariant measures, Birkhoff's
pointwise ergodic theorem, conditional measures along measurable partitions, the entropies
`h_i` of the Ledrappier–Young formula, Bernoulli and Gibbs measures, invariant measures of the
iterated function system, and the dimension theory of sets and measures. `PLAN.md` records
every labelled result and what remains; `LAYER_E.md` documents the design of the entropy
layer.

The library contains no `sorry`. The theorems the article cites from the literature without
proof are axioms, declared with their citations; `PLAN.md` lists them, their rules and their
comparison with the sources under "Fidelity boundary". Eight are on the main line, in
`BoxLike/Literature.lean` and `BoxLike/LiteratureFeng.lean`: `morrisShmerkin_lyapunov_lt`,
`fengKaenmaki_gibbs`, `fraserJordanJurga_decomposition`, `jordanRapaport_dimension`,
`System.feng_info_sum`, `System.feng_info_sum_bar`, `System.feng1_planar`, `System.feng1_bar`.
Five are off the main line and no main result depends on them: `fengHu_exactDim` and
`fengKaenmaki_unique` in `BoxLike/LiteratureRemarks.lean`, and `fraserBound`, `fraserROSC` and
`baranyKaenmakiTheorem` in `BoxLike/LiteratureOffMain.lean`. Falconer's bound
`eq:hausdorff_affinity_upper_bound`, which the article cites, is proved
(`System.dimH_attractor_le`). Rossi's bound is a `Prop` that no proof uses and is no axiom.
`BoxLike/AxCheck.lean` prints the axioms of every endpoint, so that each result shows exactly
which cited theorems it depends on; `System.main2`
depends on the eight of the main line. The case `s ≥ 2` of `thm:main_extended`
(`System.main_extended_ge_two`) and `System.dimH_attractor_of_two_le` depend on none.

## Layout

| Module | Contents |
|---|---|
| `Orientation` | The iterates `σ^n` of the two-sided shift, the orientation cocycle `ε_n` of `eq:def_of_eps_mod2`, its recursion, `eq:tau_omega_sigma_commutative1` |
| `Coding` | The transition rule `Z`, the sub-shift `Σ_Z`, the codings `τ`, `ω` of `eq:def_of_tau_omega` and their inverse, `eq:tau_omega_partition`, `thm:tau_omega_sigma_commutative` |
| `System` | Diagonal and anti-diagonal matrices and their product rule, the structure `System`, `A_i`, `φ_i`, the projective system `Ψ` of `eq:def_of_g_system`, `eq:phi_def_by_g`, the products `A_𝐢`, `thm:matrix_products_g_derivatives` |
| `Separation` | The compositions `g_𝐣`, the gap `Δ_n^Ψ`, the projective exponential separation condition, `Δ_{m+1}^Ψ ≤ Δ_m^Ψ`, `lem:proj_gap_dominated`, the last step of `prop:ssc_no_overlap_not_pesc` |
| `Projection` | The prefixes `𝐢|_n`, `\overline{π}` as a convergent series and as a limit, `φ_𝐢`, `π`, `eq:canonical_projection`, `eq:commutative_diagram`, `π(𝐢) = φ_{i_0}(π(σ𝐢))`, `eq:self_affine_set_def` for `X = π(Σ)` |
| `SingularValue` | The singular value function `φ^s` on real `2 × 2` matrices with the `ℓ²` operator norm, its sub-multiplicativity, `α_1 = max{|a|, |b|}` and the values of `φ^s` on diagonal and anti-diagonal matrices |
| `Pressure` | The sums `∑_{|𝐢| = n} φ^s(A_𝐢)`, their sub-multiplicativity, the lower bound `φ^s(A_𝐢) ≥ δ^{s|𝐢|}`, the pressure `P(𝖠, s)` and the existence of its limit by Fekete's lemma |
| `SecondIterate` | The system `Φ^(2)` over `ι × ι`, its matrices `A_i A_j`, maps `φ_i ∘ φ_j` and projective maps, `Δ_n^{Ψ^(2)} ≥ Δ_{2n}^Ψ`, the projective exponential separation condition for `Φ^(2)` |
| `LyapunovDim` | `eq:energy_def`, `eq:diml_min2`, the threshold `2 - λ_1/λ_2` of `thm:main1` and `thm:main2`, `eq:main_extended1`, `eq:main_extended2` |
| `MeasureDim` | `HasLocalDim`, `IsExactDim`, `IsDoubleDim`, `thm:exact-dimensional-mixture`, `eq:restricted-projection-dimensions`, from Besicovitch differentiation |
| `Measurable` | Measurability of `ε_n`, `τ`, `ω`, `\overline{π}`, `π` |
| `Entropy` | Cylinders, block entropies `H_μ(𝒫_0^{n-1})`, their sub-additivity, the entropy `h_0(μ)` and the existence of its limit |
| `EntropyFactor` | Lifts of a block to `Σ_Z`, `0 ≤ H_ν(\overline{𝒫}_0^{n-1}) - H_{q_*ν}(𝒫_0^{n-1}) ≤ log 2`, `h(q_*ν) = h(ν)` |
| `Thermodynamic` | `λ_1`, `λ_2`, `\overline{λ}`, `eq:eq_state_def`, `f_{1,s}`, `f_{2,s}`, Gibbs measures on `Σ_Z`, the conclusion of `thm:eq_state_is_sum`, the coordinate marginals, `\overline{λ} < 0` |
| `Literature`, `LiteratureFeng` | The eight literature axioms of the main line |
| `LiteratureOffMain` | Fraser's theorem and the theorem of Bárány and Käenmäki as axioms; `thm:fraser`, the squeeze `dimmaff(X) = dimaff(X)` and `prop:ssc_no_overlap_not_pesc` without hypotheses |
| `Main` | `thm:entropy_eq_gibbs`, `eq:proj_eq_is_sum`, `eq:gibbs_proj_dim`, for a tuple containing a proximal diagonal generator |
| `Proximal` | Proximal matrices and tuples through the characteristic polynomial, `thm:box_like_proximal`, irreducible tuples |
| `Lyapunov` | Existence of the limits defining `λ_1`, `λ_2`, `Λ` by Fekete's lemma, `-∞ < λ_2 ≤ λ_1 < 0`, `eq:energy_def`, `\overline{λ}` as a limit |
| `Grouping` | The grouping map `β`, `π^(2) ∘ β = π`, `P(𝖠², t) = 2P(𝖠, t)`, `h_0(β_*μ) = 2h_0(μ)`, `λ_i(𝖠², β_*μ) = 2λ_i(𝖠, μ)` |
| `MeasureDimBounds` | Upper and lower pointwise dimensions, `\overline{\dim}_p`, `\underline{\dim}_H`, their values for double-dimensional measures, `eq:haus_dim_sum` |
| `General` | `thm:two-block-normalisation` for equilibrium states, `eq:simple_lyapunov`, `thm:eq_state_proj_dim`, `thm:main1` |
| `AffinityDim`, `Variational`, `AffinityMain` | The affinity dimension as the unique zero of the pressure, `eq:variational`, `\dim_L ≤ dimaff`, `thm:main1` with `s = dimaff`, `dim(π_*μ) ≤ \dim_H(X)` |
| `Attractor`, `SeparationConditions`, `BoxLikeMatrix`, `MassDistribution` | Hutchinson's uniqueness of `X`, the separation conditions, `thm:box_like_sa`, the mass distribution principle |
| `Birkhoff` | Birkhoff's pointwise ergodic theorem through the maximal ergodic theorem |
| `Conditional`, `ConditionalMeasures`, `ConditionalLemmas`, `ConditionalTwoWays` | `sec:conditional`: conditional measures through `condExpKernel`, Rokhlin's properties, `thm:double_conditional`, `thm:finer_partition_dirac_mass`, transport of conditional measures, `thm:conditional_two_ways` |
| `SlowAxis`, `DimPartitions`, `MeasurablePartitions`, `PartitionIdentities`, `SigmaMeasure`, `GibbsOrientation` | `Σ'`, `Σ^τ`, `Σ^ω`, the partitions `ξ_i`, `\overline{ξ}_i`, `μ(Σ') = 1`, `thm:partitions_xi1`, `thm:gibbs_tau_omega_positive` |
| `PastEntropy`, `FengEntropy`, `AverageEntropy`, `EquilibriumEntropySmall`, `EquilibriumEntropyLarge`, `StrongOpenSetEntropy` | `h_0 = h`, `thm:feng_entropy_zero`, the entropies of `sec:average_gibbs_entropy` and `sec:higher_dimensional_entropies`, `thm:SOSC_h2_zero` |
| `MainTwo` | `thm:main_extended` for `0 < s < 2`, `thm:main2` |
| `SelfAffineMeasure` | Invariant measures `ν = ∑_i p_i (φ_i)_*ν` of the iterated function system |
| `PressureLarge` | The range `s ≥ 2` of `sec:normalisation`: `φ^s = |det|^{s/2}`, `P(𝖠, s) = log ∑_i |det A_i|^{s/2}`, `λ_1 + λ_2 = ∑_i μ([i]) log |det A_i|`, the equilibrium equation |
| `BernoulliEntropy` | `h(μ) ≤ H_μ(𝒫)` with equality only for a Bernoulli measure, Gibbs' inequality and its equality case |
| `LebesgueOpenSet` | `∑_i |det A_i| ≤ 1` under the strong open set condition, normalised Lebesgue measure on the open set as an invariant measure of exact dimension two |
| `InvariantMeasure` | Hutchinson's uniqueness of the invariant probability measure, the invariance of the projection of a Bernoulli measure |
| `MainExtended` | `thm:main_extended` for `s ≥ 2`, with no literature axiom, and in full |
| `BernoulliEquilibrium` | Bernoulli measures, their invariance, ergodicity and entropy; for `s ≥ 2` the equilibrium state exists, is unique, is Bernoulli and is ergodic |
| `DimensionFormula` | `\dim_H(X) = min{2, dimaff(X)}` under the hypotheses of `thm:main_extended`, Rossi's bound `eq:hausdorff_ergodic_lyapunov` as a `Prop`, equality in it for the equilibrium state |
| `LiteratureRemarks` | The two literature axioms that no main result depends on: Feng–Hu, Theorem 2.8, and the uniqueness part of `thm:irred_eq_state` |
| `NoSeparation` | The coordinate marginals are double-dimensional without separation (the remark before `thm:eq_state_proj_dim`), the uniqueness of `μ^(2)` in `thm:two-block-normalisation` |
| `UniqueEquilibrium` | Uniqueness of the `s`-equilibrium state for every `s > 0` (`thm:irred_eq_state`) |
| `CodingTopology` | `τ`, `ω` as closed embeddings, `β` as a homeomorphism conjugating `σ²` to the shift, the natural projection `η`; `η_*` is injective and preserves ergodicity in both directions |
| `NaturalExtension` | `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is a bijection, by the Carathéodory extension of a content on the clopen future sets |
| `LocalDimBounds` | Pointwise dimensions on `ℝ^d` lie in `[0, d]`, exact-dimensional iff `\overline{\dim}_p = \underline{\dim}_H`, the first line of `eq:haus_dim_sum` for all finite Borel measures, the second line of `eq:dimension_measure_def` |
| `InvariantMeasures` | The invariant measures are weak-star compact and `h_0 + Λ(𝖠, ·, s)` is upper semicontinuous on them, so it attains its maximum |
| `EquilibriumExistence` | An `s`-equilibrium state exists for every `s ≥ 0`, by the construction of Misiurewicz; irreducibility is not needed |
| `Example` | `ex:projection_double_dimensional`, `P(𝖠, t) = log ρ(M(t))`, the characteristic equation, `thm:main1` and `thm:main2` for `0 < s ≤ 1` |
| `Classification` | `thm:A_classification` for arbitrary planar tuples, counterexamples without proximality, a proximal box-like tuple with rotations is irreducible and not strongly irreducible |
| `PressureZ` | The pressure `P_Z(f)` of `sec:gibbs_measures` and its limit, `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})`, `μ_2 = flip_*μ_1`, the integral formulas of `thm:eq_state_is_sum`, the fourth decomposition from the other three |
| `GibbsProperties` | The equilibrium state is sub-multiplicative, not quasi-Bernoulli and not Bernoulli; doubling of Gibbs measures, `μ_1 ≠ μ_2`, `μ_1 ⟂ μ_2`, `eq:tau_cylinder`, absolute continuity |
| `SetDimensions` | Upper and lower Minkowski dimensions and the packing dimension of sets, `\dim_H E ≤ \dim_P E ≤ \overline{\dim}_M E`, `\dim_H E ≤ \underline{\dim}_M E`, bi-Lipschitz invariance, `\underline{\dim}_M E = \overline{\dim}_M E` for a super-multiplicative covering count |
| `PackingDimMeasure` | The first line of `eq:dimension_measure_def`, `\overline{\dim}_p(μ) = inf {\dim_P A : μ(ℝ^d \ A) = 0}`, for every finite Borel measure on `ℝ^d`; `\overline{\dim}_p` is monotone under absolute continuity |
| `ModifiedAffinity` | Fraser's modified singular value function, the modified pressure as a limit, the modified affinity dimension `dimmaff(X)`, `dimmaff(X) ≤ dimaff(X)` when `dimaff(X) ≥ 1` |
| `FalconerBound` | Falconer's bound `\overline{\dim}_M X ≤ min{2, dimaff(X)}` for every box-like self-affine set, and with it `eq:hausdorff_affinity_upper_bound`, `\dim_H X ≤ min{2, dimaff(X)}` |
| `FraserChain` | `thm:fraser` from Fraser's theorem as a hypothesis, `\dim_P X = \overline{\dim}_M X`, the chain `\dim_H X = \dim_P X = \dim_M X = dimaff(X)` whenever `\dim_H X = dimaff(X)`, and the squeeze `dimmaff(X) = dimaff(X)` from the first part of `thm:fraser` |
| `NoOverlapExampleFree` | The algebraic part of `prop:ssc_no_overlap_not_pesc`: algebraically independent parameters, freeness of the semigroup of the projective system |
| `NoOverlapExample` | `prop:ssc_no_overlap_not_pesc` and the paragraph after its proof, from the theorem of Bárány and Käenmäki as a hypothesis |
| `AxCheck` | The axiom audit, not imported by the root module |

## Build

The toolchain is pinned to Lean `v4.32.2`, with Mathlib pinned to the matching release in
`lakefile.toml`; on this machine `.lake/packages` is a symlink to a prebuilt Mathlib tree (see
`PLAN.md`, section 0); elsewhere run `lake exe cache get`.

```bash
lake build                       # the library and the axiom audit
```
