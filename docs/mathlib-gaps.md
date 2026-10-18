> Coverage is assessed in [correspondence.md](correspondence.md) and [review.json](review.json).

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
- The plane is `ℝ × ℝ` with the supremum norm; `A_i` is `boxMat (o i) (a i) (b i)`, with `a i`
  always in the first row and `b i` in the second, so that `proj_c ∘ φ_i = g_(i,c) ∘ proj_(c + o i)`.
- A general tuple of planar matrices is `A : ι → Matrix (Fin 2) (Fin 2) ℝ`
  (`BoxLike/MatrixTuple.lean`), invertible when `∀ i, (A i).det ≠ 0`, with its pressure, Lyapunov
  exponents, energy, equilibrium states and Gibbs bounds; a box-like system gives the tuple `S.mat`.
- A general planar self-affine system is `PlanarSystem ι` (`BoxLike/Planar/System.lean`): maps
  `φ_i(x) = A_i x + v_i` with `A_i ∈ GL_2(ℝ)` and `‖A_i‖ < 1`. Its linear parts act on coordinate
  vectors `Fin 2 → ℝ`; a box-like system is a planar system through `System.toPlanar`, with the
  same maps, projection, exponents, `Σ'`, partitions and entropies
  (`BoxLike/Planar/Specialisation.lean`). Falconer's covering and the one-sided projection use the
  Euclidean plane `EuclideanSpace ℝ (Fin 2)`, with `1`- and `2`-Lipschitz coordinate maps to
  `ℝ × ℝ`.

## 2. Layers

| Layer | Content | Character |
|---|---|---|
| A | `sec:box_like_self_affine`, `sec:irreducibility`, `sec:subshift`, `sec:projective_system`: matrices, `ε_n`, `Σ_Z`, `τ`, `ω`, `Ψ`, `π`, `\overline{π}`, the commutative diagram, topological mixing, changes of basis | elementary, proved in full |
| B | `sec:exponential_separation`, `sec:Singular_value_function`, `sec:affinity_dim`, `sec:normalisation` (algebraic part): `Δ_n^Ψ`, the projective exponential separation condition, `φ^s`, pressure by Fekete for box-like systems and for general tuples, affinity dimension, Falconer's bound for every planar self-affine set, second iterates | elementary to moderate, proved in full |
| C | `sec:ledrappier_young_formula`: pointwise dimension, exact- and double-dimensional measures, `thm:exact-dimensional-mixture`, `eq:dimension_measure_def`, `eq:haus_dim_sum`, Rossi's bound `eq:hausdorff_ergodic_lyapunov` | measure theory on Mathlib's differentiation theorem, proved in full; Rossi's bound by a covering argument with the entropy and Lyapunov limits of layer E |
| D | `sec:dimension_of_projections`, `sec:dimension_result_proof`: `thm:eq_state_proj_dim` and `thm:main1` for every `s > 0` (with the orientation lift for `s ≥ 2`), `ex:projection_double_dimensional`, `thm:main_extended`, `thm:main2` along the prose, `\dim_H X = min{2, dimaff(X)}` | proved from the literature hypotheses and layer E; the case `s ≥ 2` of `thm:main_extended` with no literature hypothesis |
| E | `sec:lyapunov_exponents`, `sec:conditional`, `sec:entropies`, `sec:gibbs_measures`, `sec:average_gibbs` to `sec:higher_dimensional_entropies`: `Σ'` and the Oseledets filtration, measurable partitions, conditional measures, the entropies `h_i`, Gibbs measures, `P_Z(f)` | Birkhoff, Maker, Shannon–McMillan–Breiman, Kolmogorov–Sinai, Kingman, Furstenberg–Kesten, Oseledets, Rokhlin's disintegration, Feng's identity, Bowen's existence of Gibbs measures, the Fraser–Jordan–Jurga decomposition `thm:eq_state_is_sum`, `thm:irred_eq_state` for tuples with rotations and `eq:simple_lyapunov` are built here; Feng's planar Ledrappier–Young formula is a hypothesis, and the scalar one follows from it through the planar system `z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` of the projective system (`fengLedrappierYoungBar_of_fengLedrappierYoung`); design in [`layer-e.md`](layer-e.md) |
| F | off the main line: `thm:fraser` and the dimension chain, `thm:A_classification`, `prop:ssc_no_overlap_not_pesc`, the rational example `Example.sys`, the natural extension, `thm:irred_eq_state` for irreducible box-like systems and for general tuples, the claims of the prose (`Support`) | proved; Fraser's Theorem 2.3 and Feng–Käenmäki's Proposition 1.2 in the form of the source, `FengKaenmakiNormEquilibrium`, are theorems of the library; Bárány–Käenmäki's theorem and the general form `PlanarFengLedrappierYoung` of Feng's formula enter as `Prop` hypotheses |

## 3. What Mathlib does not have

Each item is a piece of the paper that the library builds itself. Labels such as
`sec:conditional` and `thm:eq_state_is_sum` are the labels of the LaTeX source.

- **Iterated function systems and self-affine sets.** Mathlib has no affine iterated function
  systems, no attractor and no Hutchinson theorem. `System` is a finite family of planar maps with
  diagonal or anti-diagonal linear parts (`BoxLike/System.lean`) and `PlanarSystem` a finite family
  with arbitrary invertible contracting linear parts (`BoxLike/Planar/System.lean`). The attractor
  is the range `X = π(Σ)` of the canonical projection, which is compact, satisfies
  `eq:self_affine_set_def` and is the unique non-empty compact set doing so (`Attractor` for
  box-like systems, `PlanarSystem.eq_attractor` in general). The one-sided projection `π^+` and
  `(π^+)_*μ^+ = π_*μ` are in `Support/OneSidedProjection`. Hutchinson's uniqueness of the invariant
  probability measure `ν = ∑_i p_i (φ_i)_*ν` is proved in `SelfAffineMeasure` and
  `InvariantMeasure`.
- **Symbolic dynamics.** Mathlib has no shift spaces beyond the function type. The two-sided
  shift, the sub-shift of finite type `Σ_Z`, the codings `τ`, `ω`, the orientation cocycle `ε_n`,
  cylinders and the topology of the coding spaces are built in `Orientation`, `Coding` and
  `CodingTopology`; the topological mixing of `Σ_Z` and the standard metric of the two-sided
  shift are in `Support/SubshiftMixing` and `Support/GibbsDoubling`. The natural extension of
  `sec:two_sided_shift_space`, the bijection `η_*` between invariant measures of the one-sided and
  the two-sided shift, is built by the Carathéodory extension of a content on the clopen future
  sets (`NaturalExtension`), since Mathlib has no Kolmogorov extension theorem.
- **Thermodynamic formalism.** Mathlib has no pressure, no equilibrium states and no Gibbs
  measures. The singular value function and its sub-multiplicativity (`SingularValue`), the
  pressure with the existence of its limit by Fekete's lemma (`Pressure`, and for general tuples
  `MatrixTuple`, `TupleEquilibrium`), continuity, convexity between consecutive integers and
  strict monotonicity (`AffinityDim`, `Support/PressureConvexity`), the affinity dimension as its
  unique zero (`AffinityDim`, `Planar/AffinityDim`), the Lyapunov exponents as limits (`Lyapunov`,
  `Planar/Lyapunov`) and the variational inequality are proved. Equilibrium states exist for every
  `s ≥ 0` by the construction of Misiurewicz (`EquilibriumExistence`,
  `TupleEquilibriumExistence`). An ergodic one exists for every tuple (`TupleErgodicEquilibrium`):
  Mathlib's Krein–Milman theorem needs a real locally convex space, and finite measures form only
  an `ℝ≥0`-module, so the extreme point of the compact set of equilibrium states is produced as the
  maximiser of the strictly convex weak-star continuous functional
  `Q(μ) = ∑_𝐢 2^{-e(𝐢)} μ([𝐢])²` of the cylinder masses, and an extreme point is ergodic. On `Σ_Z`,
  the pressure `P_Z(f)`, Gibbs measures, their doubling, the uniqueness of the ergodic Gibbs
  measure of a Hölder potential and `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` are in `PressureZ`,
  `GibbsProperties`, `Support/HolderPressure`, `Support/GibbsUniqueness` and `Thermodynamic`.
  Bowen's theorem, the existence of an ergodic Gibbs measure for every Hölder potential on the
  mixing `Σ_Z`, is built in `Bowen/`: the bounds `e^{nP} ≤ A_n ≤ K e^{nP}` on the partition sums,
  from Fekete's lemma and a super-additive form of it for sums glued through periodic points
  (`Bowen/PartitionBounds`); the weighted periodic-orbit measures, which satisfy the Gibbs bounds
  up to every length with one constant (`Bowen/PeriodicMeasures`); a weak-star limit point in the
  compact space of probability measures, where the Gibbs bounds up to a length are a closed
  condition since cylinders are clopen (`Bowen/Limit`); and the ergodicity of every invariant
  Gibbs measure from a quasi-Bernoulli lower bound (`Bowen/Ergodic`, `Bowen/Main`). The
  decomposition of `thm:eq_state_is_sum` (Fraser–Jordan–Jurga) is built on Bowen's theorem in
  `FraserJordanJurga/`: the ergodic Gibbs measure `μ_1` of `f_{1,s}`, its image `μ_2` under the
  exchange of the axes, and the Gibbs bounds of `φ^s` for the image of `μ_1` under forgetting the
  axis (`FraserJordanJurga/Gibbs`); the equality of every invariant measure with these bounds and
  this image, and the four decompositions from `Σ_Z = τ(Σ) ⊔ ω(Σ)`
  (`FraserJordanJurga/Decomposition`); the Lyapunov identities from Birkhoff's theorem along the
  two lifts and a relative-entropy comparison (`FraserJordanJurga/Lyapunov`); and the assembly
  `fraserJordanJurgaDecomposition_holds` (`FraserJordanJurga/Main`). For a tuple with rotations
  and `0 < s < 2` every invariant equilibrium state is the image of `μ_1` under forgetting the
  axis (`EquilibriumGibbs`), since the relative entropy of the cylinder partitions is bounded and
  bounded relative entropy implies absolute continuity (`Support/RelativeEntropy`). This gives
  `thm:irred_eq_state` for tuples with rotations. Morris–Shmerkin's Lemma 3.4 and
  `eq:simple_lyapunov` are in `MorrisShmerkin`. Feng–Käenmäki's Proposition 1.2 for irreducible
  planar tuples, the quasi-multiplicative Gibbs theory of the norm potential `‖·‖^q`, is built in
  `QuasiMultiplicative/`: the quasi-multiplicativity of the norm of an irreducible tuple, with
  connecting words of length at most one, by compactness of the unit sphere of the matrices
  (`QuasiMultiplicative/Irreducible`); the bounds `e^{nP} ≤ Z_n ≤ K e^{nP}` on the partition sums,
  from Fekete's lemma and a super-multiplicative form of it for words joined through connecting
  words (`QuasiMultiplicative/GibbsMeasurePressure`); the weighted periodic-orbit measures, which
  satisfy the Gibbs bounds for every fixed word once their period is large
  (`QuasiMultiplicative/GibbsMeasurePeriodic`); a weak-star limit point
  (`QuasiMultiplicative/GibbsMeasure`); the ergodicity of every invariant Gibbs measure from a
  quasi-Bernoulli lower bound whose gap varies with the words
  (`QuasiMultiplicative/GibbsMeasureErgodic`); the equality of every invariant equilibrium state
  with the Gibbs measure, by the bound on the relative entropy of the cylinder partitions
  (`QuasiMultiplicative/Uniqueness`); and the passage to the one-sided shift through the natural
  extension (`QuasiMultiplicative/Main`). The Bernoulli equilibrium state for `s ≥ 2` is in
  `BernoulliEquilibrium`, `BernoulliEntropy` and `PressureLarge`, and the orientation lift of a
  Bernoulli measure as a mixing stationary Markov measure in `OrientationLift`.
- **Entropy.** Mathlib has no Kolmogorov–Sinai entropy and no conditional entropy. Block
  entropies and the entropy rate (`Entropy`), the entropy of finite partitions, the conditional
  entropy calculus, the Kolmogorov–Sinai entropy as a supremum over finite Borel partitions and
  the generator theorem for the two-sided shift (`KolmogorovSinai`), the conditional information
  and entropy of countable partitions (`Conditional`, `Support/ConditionalInformation`), the
  entropies `h_i`, `\overline{h}_i` of Feng's Ledrappier–Young theory (`DimPartitions`,
  `Planar/Partitions`), and the identities `h_0(μ) = h(μ)`, `\overline{h}_0(ν) = h(ν)`
  (`PastEntropy`, `CylinderEntropy`) are built here. The Shannon–McMillan–Breiman theorem is proved
  by Breiman's argument: Maker's generalised ergodic theorem (`SMB/Maker`), the informations of the
  finite pasts with Chung's maximal inequality (`SMB/PastInformation`) and the theorem for every
  invariant measure (`ShannonMcMillanBreiman`). Feng's information-sum identity is proved along
  his Lemmas 4.4 and 4.5 (`FengIdentity`, `FengIdentityBar`, `Planar/FengIdentity`).
- **Ergodic theory.** Mathlib has no pointwise ergodic theorem in the form the paper uses, no
  subadditive ergodic theorem and no multiplicative ergodic theorem. Birkhoff's theorem is proved
  through the maximal ergodic theorem (`Birkhoff`); Kingman's subadditive ergodic theorem from it
  by the stopping-time method (`Kingman`); the Furstenberg–Kesten limits along backward products
  (`FurstenbergKesten`) and along forward products (`Rossi`) from Kingman's theorem; and
  Oseledets' theorem for invertible planar cocycles from these and a deterministic planar argument
  for the slow directions (`Planar/OseledetsTheoremDirection`, `Planar/OseledetsTheorem`). Mixing
  on cylinders implies ergodicity (`OrientationLift`).
- **Measurable partitions and conditional measures.** Mathlib has `condExpKernel` on a standard
  Borel space but no Rokhlin theory of measurable partitions. Partitions as atom maps, the
  `σ`-algebra `\widehat{ξ}`, conditional measures along a partition with their uniqueness, the
  lemmas `thm:conditional_measures_of_a_conditional_measure`, `thm:double_conditional`,
  `thm:finer_partition_dirac_mass`, and the comparison of partitions that agree after cutting
  down to a set of full measure (`OseledetsBridge`) are in `Conditional`, `ConditionalMeasures`,
  `ConditionalLemmas`, `MeasurablePartitions` and `OseledetsBridge`; the design is recorded in
  [`layer-e.md`](layer-e.md).
- **Dimension theory of sets.** Mathlib has the Hausdorff dimension `dimH` and nothing else. The
  upper and lower Minkowski dimensions, the packing dimension as the modified upper Minkowski
  dimension, and `\dim_P X = \overline{\dim}_M X` for every box-like set are in `SetDimensions`,
  `PackingDimMeasure` and `FraserChain`. Falconer's bound `eq:hausdorff_affinity_upper_bound` is
  proved for every planar self-affine set by the Euclidean ellipse cover (`Planar/FalconerBound`):
  the operator norm is attained on the unit circle, `det(A x | A y) = det A · det(x | y)` bounds the
  component orthogonal to the long axis by `α_2(A)`, so the ellipse `A(B(0, R))` lies in a
  rectangle with sides `2 α_1(A) R` and `2 α_2(A) R` and is covered by `⌈α_1/α_2⌉` balls. For
  box-like sets a covering in the supremum metric gives the same bound (`FalconerBound`). The
  modified affinity dimension with `dimmaff(X) ≤ dimaff(X)` is in `ModifiedAffinity`. Fraser's box
  dimension theory, his Theorem 2.3, is built along his Section 5 in `Fraser/`: covering numbers of
  finite unions and of planar sets with one coordinate in an interval, the bound
  `N_r(E) ≤ C r^{-t}` from `\overline{\dim}_M E < t`, his Lemma 5.1 (1) and the cover of `X` by the
  copies `φ_𝐢(X)` of the stopping words, which give `\overline{\dim}_M X ≤ dimmaff(X)`
  (`Fraser/Upper`, `Fraser/UpperBound`); the `δ`-stoppings as sums over a tree of words, with two
  tree inequalities in place of the combinatorics of prefix codes, and his Lemma 5.1 (2)
  (`Fraser/LowerStop`); the lower bound `dimmaff(X) ≤ \underline{\dim}_M X` under the rectangular
  open set condition, by an area count for the disjoint rectangles `φ_𝐢(R)` near a square
  (`Fraser/LowerCover`); and the assembly (`Fraser/Lower`, `Fraser/Main`). The
  invariance of the dimensions under linear changes of coordinates is in `Planar/ChangeOfBasis`.
- **Dimension theory of measures.** Mathlib has no pointwise dimension. Upper and lower pointwise
  dimensions, exact- and double-dimensional measures, `thm:exact-dimensional-mixture` from
  Besicovitch's differentiation theorem, the upper packing and lower Hausdorff dimensions of a
  measure with both lines of `eq:dimension_measure_def` and `eq:haus_dim_sum`, and the mass
  distribution principle are in `MeasureDim`, `MeasureDimBounds`, `LocalDimBounds`,
  `PackingDimMeasure`, `MassDistribution` and `Aligned/MeasureDimSets`. Rossi's covering bound
  `eq:hausdorff_ergodic_lyapunov` is in `Rossi` and `RossiBound`: for `t ≤ 2` with
  `h_0(μ) + Λ(𝖠, μ, t) < 0`, the Shannon–McMillan–Breiman theorem and the forward
  Furstenberg–Kesten limits bound the number of typical words of length `n` and the sides of the
  rectangles that contain their copies of `X`; the squares covering these rectangles give a Borel
  set of full `π_*μ`-measure and Hausdorff dimension at most `t`, and a set of full measure with
  Hausdorff dimension at most `t` bounds the lower pointwise dimension by `t` almost everywhere.
- **Linear algebra of planar tuples.** The projective line as a type of lines, irreducibility,
  strong irreducibility and proximality of a tuple, and the classification
  `thm:A_classification` with its counterexamples, are in `Classification` and `Proximal`; the
  operator norm of a box-like matrix is computed from the `C*`-identity, since `Aᵀ A` is diagonal
  (`BoxLikeMatrix`, `SingularValue`); the comparison of singular values under conjugation and the
  basis-independence of the classification are in `Planar/ChangeOfBasis`.

## 4. Reuse

- `TauCeti` is on Lean `v4.34.0-rc2` with the module system and has no symbolic dynamics,
  pressure, entropy or fractal geometry; nothing is taken from it.
- `LeanLibraries/GeometricMeasureTheory`: `lowerLocalDim`, `upperLocalDim`
  (`Assouad/MeasureDimensions.lean`), the quasi-Fekete lemmas (`Pressure/Subadditive.lean`) and
  the unique-zero template `pressure_zero` (`Pressure/Dimension.lean`) are copied when needed.
- `LeanLibraries/FractalGeometry/Hutchinson.lean`: the `code` pipeline is the template for the
  canonical projection and for the Bernoulli measure at `s ≥ 2`.
- The projects stay Mathlib-only, as `ML-ST/lean` and `JA-ST/lean` do: snippets are copied,
  never required by path.
