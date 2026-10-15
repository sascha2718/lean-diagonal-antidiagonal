module

/-
`BoxLike`: a formalisation of `diagonal-antidiagonal.tex`, "Hausdorff dimension of planar
box-like self-affine sets with rotations" (Allen, Käenmäki, Prokaj, Simon, Troscheit).

The library is built on Mathlib alone, contains no `sorry` and declares no axiom: every
constant depends on `propext`, `Classical.choice` and `Quot.sound` only. Literature theorems
cited by the article without proof are `Prop`-valued definitions of the modules
`BoxLike/Literature.lean`, `BoxLike/LiteratureFeng.lean` and `BoxLike/LiteratureRemarks.lean`,
and every result that uses one takes it as a hypothesis; the last module holds the ones that no
main result depends on. `docs/correspondence.md` records the state of every numbered result,
the remaining work and the fidelity boundary, and `docs/mathlib-gaps.md` the representation.

* `Orientation`: the two-sided shift `σ^n` and the orientation cocycle `ε_n` of
  `eq:def_of_eps_mod2`, with the cocycle identity `eq:tau_omega_sigma_commutative1`.
* `Coding`: the sub-shift `Σ_Z`, the codings `τ`, `ω` of `eq:def_of_tau_omega`, the partition
  `eq:tau_omega_partition` and `thm:tau_omega_sigma_commutative`.
* `System`: box-like systems, the matrices `A_i`, the maps `φ_i`, the projective system `Ψ` of
  `eq:def_of_g_system`, `eq:phi_def_by_g` and `thm:matrix_products_g_derivatives`.
* `Separation`: the projective gap `Δ_n^Ψ`, the projective exponential separation condition
  and `lem:proj_gap_dominated`.
* `Projection`: the canonical projections `\overline{π}` and `π`, `eq:canonical_projection`,
  `eq:commutative_diagram` and `eq:self_affine_set_def` for `X = π(Σ)`.
* `SingularValue`: the singular value function `φ^s` of `sec:Singular_value_function`, its
  sub-multiplicativity, and `α_1 = max{|a|, |b|}`, `α_1 α_2 = |a| |b|` on diagonal and
  anti-diagonal matrices.
* `Pressure`: the sums `∑_{|𝐢| = n} φ^s(A_𝐢)` and the pressure `P(𝖠, s)` of `sec:affinity_dim`,
  with the existence of its limit by Fekete's lemma.
* `SecondIterate`: the second iterate `Φ^(2)` and the separation part of
  `thm:two-block-normalisation`.
* `LyapunovDim`: the real-variable part of `thm:main1`, `thm:main_extended` and `thm:main2`:
  `eq:energy_def`, `eq:diml_min2`, the threshold `2 - λ_1/λ_2`, `eq:main_extended1` and
  `eq:main_extended2`.
* `MeasureDim`: pointwise dimension, exact- and double-dimensional measures,
  `thm:exact-dimensional-mixture` and `eq:restricted-projection-dimensions`.
* `Measurable`: measurability of `τ`, `ω`, `\overline{π}` and `π`.
* `Entropy`: block entropies and the Kolmogorov–Sinai entropy `h_0`, with the existence of its
  limit.
* `EntropyFactor`: the two-lift comparison of block entropies behind `thm:entropy_eq_gibbs`.
* `Thermodynamic`: Lyapunov exponents, `eq:eq_state_def`, the potentials `f_{1,s}`, `f_{2,s}`,
  Gibbs measures on `Σ_Z`, the conclusion of `thm:eq_state_is_sum`, the coordinate marginals.
* `Literature`: the literature theorems of the main line as `Prop`s: Morris–Shmerkin,
  Feng–Käenmäki (the Gibbs bounds), Fraser–Jordan–Jurga, Jordan–Rapaport.
* `Main`: `thm:entropy_eq_gibbs` and the decomposition `eq:proj_eq_is_sum`, `eq:gibbs_proj_dim`
  of the coordinate marginals, for a tuple containing a proximal diagonal generator.
* `Proximal`: proximal matrices and tuples, `thm:box_like_proximal`.
* `Lyapunov`: existence of the limits defining `λ_1`, `λ_2` and `Λ`, `λ_2 ≤ λ_1 < 0`,
  `eq:energy_def`, and `\overline{λ}` as a limit.
* `Grouping`: the grouping map `β` and the measure part of `thm:two-block-normalisation`.
* `MeasureDimBounds`: upper packing and lower Hausdorff dimension of a measure,
  `eq:haus_dim_sum`.
* `General`: `eq:simple_lyapunov`, `thm:eq_state_proj_dim` and `thm:main1` for every proximal
  box-like tuple with rotations.
* `AffinityDim`: the pressure is continuous and strictly decreasing, `P(𝖠, 0) = log N`, the
  affinity dimension `dimaff` as its unique zero.
* `Variational`: `eq:variational`, `0 ≤ P(𝖠, \dim_L)`, the identity
  `φ^s(A_{𝐢|_n}) = max{exp S_n f_{1,s}, exp S_n f_{2,s}}`.
* `Attractor`: continuity of `π`, compactness and uniqueness of `X`, `Φ^(2)` has attractor `X`.
* `SeparationConditions`: the strong separation, strong open set and rectangular open set
  conditions, and their passage to `Φ^(2)`.
* `MassDistribution`: `dim μ ≤ \dim_H A` for an exact-dimensional measure charging `A`.
* `BoxLikeMatrix`: `thm:box_like_sa`.
* `AffinityMain`: `\dim_L ≤ dimaff`, `thm:main1` with `s = dimaff(X)`, `dim(π_*μ) ≤ \dim_H(X)`.
* `Birkhoff`: Birkhoff's pointwise ergodic theorem, through the maximal ergodic theorem.
* `Conditional`: partitions as atom maps, the `σ`-algebra `\widehat{ξ}`, conditional measures,
  conditional information and entropy (`sec:conditional`, `sec:entropies`).
* `ConditionalMeasures`: Rokhlin's disintegration for `condMeas`, integrability of the
  conditional information, `eq:ergodic_entropy_constant`.
* `ConditionalLemmas`: `thm:conditional_measures_of_a_conditional_measure`,
  `thm:double_conditional`, `thm:finer_partition_dirac_mass`.
* `SlowAxis`: the box-like set `Σ'`, `Σ^τ`, `Σ^ω`, the slow axis,
  `thm:lyapunov_exponents_via_g_system`.
* `DimPartitions`: the partitions `ξ_i`, `ξ_1^⊥`, `\overline{ξ}_i`, the entropies `h_i`,
  `\overline{h}_i`, the average measure, ergodicity of the equilibrium state.
* `MeasurablePartitions`: `ξ_i`, `ξ_1^⊥`, `\overline{ξ}_i` are measurable partitions.
* `PartitionIdentities`: `eq:sigma_tau_omega_positive_eq_measure1`, `thm:partitions_xi1`,
  `thm:partition_tau_conj`.
* `SigmaMeasure`: `μ(Σ') = 1`, `eq:lyapunov_exponent_gsystem`,
  `thm:sigma_tau_omega_positive_eq_measure`.
* `GibbsOrientation`: `thm:gibbs_tau_omega_positive`, `eq:orientation-restrictions`.
* `PastEntropy`: `h_0(μ) = h(μ)` and `\overline{h}_0(ν) = h(ν)`, by the chain rule and
  martingale convergence.
* `LiteratureFeng`: the results of Feng as `Prop`s.
* `FengEntropy`: `thm:feng_entropy_as_limit`, `thm:feng_entropy_zero`.
* `ConditionalTwoWays`: transport of conditional measures, `thm:conditional_two_ways`.
* `StrongOpenSetEntropy`: `thm:SOSC_h2_zero`.
* `AverageEntropy`: `thm:overline_h1_zero`, `thm:overline_h1_zero_large`.
* `EquilibriumEntropySmall`: `thm:eq_state_h1_zero`, `thm:eq_state_h2_zero`,
  `thm:orto_partition_dirac`.
* `EquilibriumEntropyLarge`: `thm:overline_h1_large`, `thm:eq_state_h1_large`.
* `MainTwo`: `thm:main_extended` for `0 < s < 2` and `thm:main2`.
* `SelfAffineMeasure`: invariant measures `ν = ∑_i p_i (φ_i)_*ν` of the iterated function
  system, for the case `s ≥ 2` of `thm:main_extended`.
* `PressureLarge`: the range `s ≥ 2` of `sec:normalisation`: `φ^s = |det|^{s/2}`,
  `P(𝖠, s) = log ∑_i |det A_i|^{s/2}`, `λ_1 + λ_2 = ∑_i μ([i]) log |det A_i|` and the
  equilibrium equation.
* `BernoulliEntropy`: `h(μ) ≤ H_μ(𝒫)` with equality only for a Bernoulli measure, Gibbs'
  inequality and its equality case.
* `LebesgueOpenSet`: `∑_i |det A_i| ≤ 1` under the strong open set condition, and normalised
  Lebesgue measure on the open set as an invariant measure of exact dimension two.
* `InvariantMeasure`: Hutchinson's uniqueness of the invariant probability measure, and the
  invariance of the projection of a Bernoulli measure.
* `MainExtended`: `thm:main_extended` for `s ≥ 2` and in full.
* `BernoulliEquilibrium`: Bernoulli measures, their invariance, ergodicity and entropy; for
  `s ≥ 2` the equilibrium state exists, is unique and is Bernoulli (`sec:normalisation`).
* `DimensionFormula`: `\dim_H(X) = min{2, dimaff}` under the hypotheses of `thm:main_extended`,
  the statement of Rossi's bound `eq:hausdorff_ergodic_lyapunov`, and equality in it for the
  equilibrium state.
* `LiteratureRemarks`: the literature theorems that no main result depends on, as `Prop`s:
  Feng–Hu, Theorem 2.8, and the uniqueness part of `thm:irred_eq_state`.
* `NoSeparation`: the remark before `thm:eq_state_proj_dim` that the coordinate marginals are
  double-dimensional without separation, and the uniqueness of `μ^(2)` in
  `thm:two-block-normalisation`.
* `UniqueEquilibrium`: uniqueness of the `s`-equilibrium state of a proximal box-like tuple
  with rotations for every `s > 0` (`thm:irred_eq_state`).
* `CodingTopology`: `τ`, `ω` as closed embeddings, `β` as a homeomorphism conjugating `σ²` to
  the shift, the natural projection `η` of `sec:two_sided_shift_space`; `η_*` is injective and
  preserves ergodicity in both directions.
* `NaturalExtension`: `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is a bijection (`sec:two_sided_shift_space`),
  by the Carathéodory extension of a content on the clopen future sets.
* `LocalDimBounds`: pointwise dimensions on `ℝ^d` lie in `[0, d]` almost everywhere,
  exact-dimensional iff `\overline{\dim}_p = \underline{\dim}_H`, the first line of
  `eq:haus_dim_sum` for all finite Borel measures, the second line of
  `eq:dimension_measure_def`.
* `EquilibriumExistence`: an `s`-equilibrium state exists for every `s ≥ 0`, by the construction
  of Misiurewicz (tex lines 2322 to 2323, Käenmäki); irreducibility is not needed.
* `InvariantMeasures`: the invariant measures form a compact set in the weak-star topology and
  `h_0 + Λ(𝖠, ·, s)` is upper semicontinuous on it, so it attains its maximum (tex lines 2322
  to 2323, Käenmäki).
* `Example`: `ex:projection_double_dimensional`, with `thm:main1` and `thm:main2` for
  `0 < s ≤ 1`.
* `Classification`: `thm:A_classification`, proved for arbitrary planar tuples.
* `PressureZ`: the pressure `P_Z(f)` of `sec:gibbs_measures`,
  `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})`, `μ_2 = flip_*μ_1` and the integral formulas of
  `thm:eq_state_is_sum`.
* `GibbsProperties`: the equilibrium state is sub-multiplicative, not quasi-Bernoulli and not
  Bernoulli; the doubling inequality of Gibbs measures, `μ_1 ≠ μ_2`, `μ_1 ⟂ μ_2` and
  `eq:tau_cylinder`.
* `SetDimensions`: the upper and lower Minkowski dimensions and the packing dimension of sets,
  to which `sec:affinity_dim` refers, with `\dim_H E ≤ \underline{\dim}_M E`,
  `\dim_H E ≤ \dim_P E ≤ \overline{\dim}_M E`, bi-Lipschitz invariance, and the equality of the
  two Minkowski dimensions for a super-multiplicative covering count.
* `PackingDimMeasure`: the first line of `eq:dimension_measure_def`,
  `\overline{\dim}_p(μ) = inf {\dim_P A : μ(ℝ^d \ A) = 0}`, for every finite Borel measure on
  `ℝ^d`, through the packing dimension of `SetDimensions`.
* `ModifiedAffinity`: Fraser's modified singular value function, the modified pressure and the
  modified affinity dimension `dimmaff(X)` of `sec:affinity_dim`, with
  `dimmaff(X) ≤ dimaff(X)` when `dimaff(X) ≥ 1`.
* `FalconerBound`: Falconer's bound `\overline{\dim}_M X ≤ min{2, dimaff(X)}` for every box-like
  self-affine set, and with it `eq:hausdorff_affinity_upper_bound`.
* `FraserChain`: `thm:fraser`, with Fraser's theorem as a hypothesis and
  `\dim_P X = \overline{\dim}_M X` proved; the chain `\dim_H X = \dim_P X = \dim_M X = dimaff(X)`
  of the introduction, and the squeeze `dimmaff(X) = dimaff(X)` from the first part of
  `thm:fraser`.
* `NoOverlapExampleFree`: the algebraic part of `prop:ssc_no_overlap_not_pesc`: algebraically
  independent parameters and the freeness of the semigroup generated by the projective system.
* `NoOverlapExample`: `prop:ssc_no_overlap_not_pesc` and the paragraph after its proof, with the
  theorem of Bárány and Käenmäki as a hypothesis.
-/
public import BoxLike.Orientation
public import BoxLike.Coding
public import BoxLike.System
public import BoxLike.Separation
public import BoxLike.Projection
public import BoxLike.SingularValue
public import BoxLike.Pressure
public import BoxLike.SecondIterate
public import BoxLike.LyapunovDim
public import BoxLike.MeasureDim
public import BoxLike.Measurable
public import BoxLike.Entropy
public import BoxLike.EntropyFactor
public import BoxLike.Thermodynamic
public import BoxLike.Literature
public import BoxLike.Main
public import BoxLike.Proximal
public import BoxLike.Lyapunov
public import BoxLike.Grouping
public import BoxLike.MeasureDimBounds
public import BoxLike.General
public import BoxLike.AffinityDim
public import BoxLike.Variational
public import BoxLike.Attractor
public import BoxLike.SeparationConditions
public import BoxLike.MassDistribution
public import BoxLike.BoxLikeMatrix
public import BoxLike.AffinityMain
public import BoxLike.Birkhoff
public import BoxLike.Conditional
public import BoxLike.ConditionalMeasures
public import BoxLike.ConditionalLemmas
public import BoxLike.SlowAxis
public import BoxLike.DimPartitions
public import BoxLike.MeasurablePartitions
public import BoxLike.PartitionIdentities
public import BoxLike.SigmaMeasure
public import BoxLike.GibbsOrientation
public import BoxLike.PastEntropy
public import BoxLike.LiteratureFeng
public import BoxLike.FengEntropy
public import BoxLike.ConditionalTwoWays
public import BoxLike.StrongOpenSetEntropy
public import BoxLike.AverageEntropy
public import BoxLike.EquilibriumEntropySmall
public import BoxLike.EquilibriumEntropyLarge
public import BoxLike.MainTwo
public import BoxLike.SelfAffineMeasure
public import BoxLike.PressureLarge
public import BoxLike.BernoulliEntropy
public import BoxLike.LebesgueOpenSet
public import BoxLike.InvariantMeasure
public import BoxLike.MainExtended
public import BoxLike.BernoulliEquilibrium
public import BoxLike.DimensionFormula
public import BoxLike.LiteratureRemarks
public import BoxLike.NoSeparation
public import BoxLike.UniqueEquilibrium
public import BoxLike.CodingTopology
public import BoxLike.NaturalExtension
public import BoxLike.LocalDimBounds
public import BoxLike.InvariantMeasures
public import BoxLike.EquilibriumExistence
public import BoxLike.Example
public import BoxLike.Classification
public import BoxLike.PressureZ
public import BoxLike.GibbsProperties
public import BoxLike.SetDimensions
public import BoxLike.PackingDimMeasure
public import BoxLike.ModifiedAffinity
public import BoxLike.FalconerBound
public import BoxLike.FraserChain
public import BoxLike.NoOverlapExampleFree
public import BoxLike.NoOverlapExample
