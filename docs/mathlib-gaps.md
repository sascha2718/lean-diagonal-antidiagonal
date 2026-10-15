# Representation, layers, and what Mathlib does not have

This file records how the objects of `diagonal-antidiagonal.tex` are represented in the library
`BoxLike`, how the formalisation is layered along the paper, and which parts of the mathematics
the library builds because Mathlib lacks them. The module index is the root module
[`BoxLike.lean`](../BoxLike.lean), which lists every module with the part of the paper it
certifies. [`correspondence.md`](correspondence.md) has the state of every numbered result and
the fidelity boundary.

## 1. Representation

- The alphabet is a type `ι` with an orientation `o : ι → ZMod 2`; `o i = 0` for a diagonal
  generator and `o i = 1` for an anti-diagonal one. The paper's labelling `{1, …, ℓ}`
  diagonal, `{ℓ+1, …, N}` anti-diagonal is the special case `o i = 1 ↔ ℓ < i`.
- The alphabet `{1, …, 2N}` of `Σ_Z` and of the projective system `Ψ` is `ι × ZMod 2`:
  `(i, 0)` is the paper's `i` and `(i, 1)` is `i + N`. The second component is the
  coordinate axis followed. The transition matrix reads `Z((i,c),(j,c')) = 1 ↔ c' = c + o i`.
- `Σ = ℤ → ι`, `σ^n` is `shift n`, and `τ(𝐢)_n = (i_n, ε_n(𝐢))`, `ω(𝐢)_n = (i_n, ε_n(𝐢) + 1)`.
- The plane is `ℝ × ℝ`; `A_i` is `boxMat (o i) (a i) (b i)`, with `a i` always in the first
  row and `b i` in the second, so that `proj_c ∘ φ_i = g_(i,c) ∘ proj_(c + o i)`.


## 2. Layers

| Layer | Content | Character |
|---|---|---|
| A | `sec:box_like_self_affine`, `sec:irreducibility`, `sec:subshift`, `sec:projective_system`: matrices, `ε_n`, `Σ_Z`, `τ`, `ω`, `Ψ`, `π`, `\overline{π}`, the commutative diagram | elementary, proved in full |
| B | `sec:exponential_separation`, `sec:Singular_value_function`, `sec:affinity_dim`, `sec:normalisation` (algebraic part): `Δ_n^Ψ`, the projective exponential separation condition, `φ^s`, pressure by Fekete, affinity dimension, second iterates | elementary to moderate, proved in full |
| C | `sec:ledrappier_young_formula`: pointwise dimension, exact- and double-dimensional measures, `thm:exact-dimensional-mixture`, `eq:haus_dim_sum` | measure theory on Mathlib's differentiation theorem, proved in full |
| D | `sec:dimension_of_projections`, `sec:dimension_result_proof`: `thm:eq_state_proj_dim`, `thm:main1`, `thm:main_extended`, `thm:main2`, `\dim_H X = min{2, dimaff(X)}`; for `s ≥ 2` the Bernoulli equilibrium state, the Lebesgue measure of the open set and Hutchinson's uniqueness of the invariant measure | proved from the literature hypotheses and the results of layer E; the case `s ≥ 2` with no literature hypothesis |
| E | `sec:lyapunov_exponents`, `sec:conditional`, `sec:entropies`, `sec:gibbs_measures`, `sec:average_gibbs` to `sec:higher_dimensional_entropies`: the box-like `Σ'`, measurable partitions, conditional measures, the entropies `h_i`, Gibbs measures, `P_Z(f)` | Birkhoff's theorem, Rokhlin disintegration along measurable partitions and conditional entropy are built here, since Mathlib lacks them; Feng's results are hypotheses; proved in full |
| F | off the main line: the introduction (`thm:fraser`, the chain `\dim_H X = \dim_P X = \dim_M X = dimaff(X)`, `dimmaff`), `thm:A_classification`, `prop:ssc_no_overlap_not_pesc`, `ex:projection_double_dimensional`, the natural extension of `sec:two_sided_shift_space`, `thm:irred_eq_state` apart from the Gibbs bounds, and the unlabelled claims about the equilibrium state and the Gibbs measures | proved; cited theorems enter as `Prop` hypotheses |


## What Mathlib does not have

Each item is a piece of the paper that the library builds itself. Labels such as
`sec:conditional` and `thm:eq_state_is_sum` are the labels of the LaTeX source.

- **Iterated function systems and self-affine sets.** Mathlib has no affine iterated function
  systems, no attractor and no Hutchinson theorem. `System` is a finite family of planar maps
  `φ_i(x) = A_i x + v_i` with `A_i` diagonal or anti-diagonal (`BoxLike/System.lean`); the
  attractor is the range `X = π(Σ)` of the canonical projection (`Projection`, `Attractor`), which
  is compact, satisfies `eq:self_affine_set_def` and is the unique non-empty compact set doing
  so. Hutchinson's uniqueness of the invariant probability measure `ν = ∑_i p_i (φ_i)_*ν`, which
  the proof of `thm:main_extended` uses for `s ≥ 2`, is proved in `SelfAffineMeasure` and
  `InvariantMeasure`.
- **Symbolic dynamics.** Mathlib has no shift spaces beyond the function type. The two-sided shift
  `Σ = ℤ → ι`, the sub-shift of finite type `Σ_Z`, the codings `τ`, `ω`, the orientation cocycle
  `ε_n`, cylinders, and the topology of the coding spaces (`τ`, `ω` closed embeddings, `Σ_Z`
  closed) are built in `Orientation`, `Coding` and `CodingTopology`. The natural extension of
  `sec:two_sided_shift_space`, the bijection `η_*` between invariant measures of the one-sided
  and the two-sided shift, is built by the Carathéodory extension of a content on the clopen
  future sets (`NaturalExtension`), since Mathlib has no Kolmogorov extension theorem.
- **Thermodynamic formalism.** Mathlib has no pressure, no equilibrium states and no Gibbs
  measures. The singular value function and its sub-multiplicativity (`SingularValue`), the
  pressure `P(𝖠, s)` with the existence of its limit by Fekete's lemma (`Pressure`), its
  continuity and strict monotonicity and the affinity dimension as its unique zero
  (`AffinityDim`), the Lyapunov exponents as limits (`Lyapunov`), the variational inequality
  `eq:variational` (`Variational`), and the existence of an `s`-equilibrium state for every
  `s ≥ 0` by the construction of Misiurewicz (`EquilibriumExistence`) are proved. On the sub-shift
  `Σ_Z`, the pressure `P_Z(f)` over periodic points, Gibbs measures and their doubling, and the
  identity `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` are in `PressureZ`, `GibbsProperties` and
  `Thermodynamic`. The Bernoulli equilibrium state for `s ≥ 2`, with its uniqueness and
  ergodicity, is in `BernoulliEquilibrium`, `BernoulliEntropy` and `PressureLarge`.
- **Entropy.** Mathlib has no Kolmogorov–Sinai entropy and no conditional entropy. Block
  entropies and `h_0` with the existence of its limit (`Entropy`), the conditional information
  and conditional entropy of a countable partition given a `σ`-algebra, and the entropies `h_i`,
  `\overline{h}_i` of Feng's Ledrappier–Young theory (`Conditional`, `DimPartitions`,
  `PastEntropy`) are built here. The identities `h_0(μ) = h(μ)` and `\overline{h}_0(ν) = h(ν)`
  are proved directly by the chain rule, Lévy's upward theorem and Cesàro averaging, so the
  Shannon–McMillan–Breiman theorem is not needed.
- **Ergodic theory.** Mathlib has no pointwise ergodic theorem for measure-preserving maps in
  the form the paper uses. Birkhoff's theorem is proved through the maximal ergodic theorem
  (`Birkhoff`), and it gives `μ(Σ') = 1` for the box-like set `Σ'` (`SigmaMeasure`), without
  Oseledets' theorem.
- **Measurable partitions and conditional measures.** Mathlib has `condExpKernel` on a standard
  Borel space but no Rokhlin theory of measurable partitions. Partitions as atom maps, the
  `σ`-algebra `\widehat{ξ}`, conditional measures along a partition with their uniqueness and
  the lemmas `thm:conditional_measures_of_a_conditional_measure`, `thm:double_conditional`,
  `thm:finer_partition_dirac_mass` are in `Conditional`, `ConditionalMeasures`,
  `ConditionalLemmas` and `MeasurablePartitions`; the design is recorded in
  [`layer-e.md`](layer-e.md).
- **Dimension theory of sets.** Mathlib has the Hausdorff dimension `dimH` and nothing else. The
  upper and lower Minkowski dimensions, the packing dimension as the modified upper Minkowski
  dimension, and `\dim_P X = \overline{\dim}_M X` for every box-like set are in `SetDimensions`,
  `PackingDimMeasure` and `FraserChain`. Falconer's bound `eq:hausdorff_affinity_upper_bound`
  is proved for every box-like set by a covering argument in the supremum metric
  (`FalconerBound`), and the modified affinity dimension with `dimmaff(X) ≤ dimaff(X)` in
  `ModifiedAffinity`.
- **Dimension theory of measures.** Mathlib has no pointwise dimension. Upper and lower pointwise
  dimensions, exact- and double-dimensional measures, `thm:exact-dimensional-mixture` from
  Besicovitch's differentiation theorem, the upper packing and lower Hausdorff dimensions of a
  measure with both lines of `eq:dimension_measure_def` and `eq:haus_dim_sum`, and the mass
  distribution principle are in `MeasureDim`, `MeasureDimBounds`, `LocalDimBounds` and
  `MassDistribution`.
- **Linear algebra of planar tuples.** The projective line as a type of lines, irreducibility,
  strong irreducibility and proximality of a tuple, and the classification
  `thm:A_classification` with its counterexamples, are in `Classification` and `Proximal`; the
  operator norm of a box-like matrix is computed from the `C*`-identity, since `Aᵀ A` is
  diagonal (`BoxLikeMatrix`, `SingularValue`).

## 7. Reuse

- `TauCeti` is on Lean `v4.34.0-rc2` with the module system and has no symbolic dynamics,
  pressure, entropy or fractal geometry; nothing is taken from it.
- `LeanLibraries/GeometricMeasureTheory`: `lowerLocalDim`, `upperLocalDim`
  (`Assouad/MeasureDimensions.lean`), the quasi-Fekete lemmas (`Pressure/Subadditive.lean`) and
  the unique-zero template `pressure_zero` (`Pressure/Dimension.lean`) are copied when needed.
- `LeanLibraries/FractalGeometry/Hutchinson.lean`: the `code` pipeline is the template for the
  canonical projection and for the Bernoulli measure at `s ≥ 2`.
- The projects stay Mathlib-only, as `ML-ST/lean` and `JA-ST/lean` do: snippets are copied,
  never required by path.

