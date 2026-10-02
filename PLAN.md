# `BoxLike`: formalisation of `diagonal-antidiagonal.tex`

The article determines the Hausdorff dimension of proximal planar box-like self-affine sets
with rotations under the projective exponential separation condition, and shows that the
coordinate projections of the equilibrium state are double-dimensional. This library
formalises the article on Mathlib alone. The library is sorry-free. It proves `thm:main1`
(`System.main1_dimaff`), `thm:eq_state_proj_dim` (`System.eq_state_proj_dim`), `thm:main2`
(`System.main2`) and `thm:main_extended` in full (`System.main_extended`,
`System.main_extended_min`; the case `s ≥ 2`, `System.main_extended_ge_two`, takes no
literature hypothesis), and with them `\dim_H X = min{2, dimaff(X)}` under the hypotheses of
`thm:main_extended` (`System.dimH_attractor_eq_min`, and `System.dimH_attractor_of_two_le` for `dimaff(X) ≥ 2`
under the strong open set condition, with no measure assumed). Off the main line it proves
`thm:A_classification`, `ex:projection_double_dimensional`, the existence of an `s`-equilibrium
state for every `s ≥ 0`, both lines of `eq:dimension_measure_def`, `prop:ssc_no_overlap_not_pesc` and the chain
`\dim_H X = \dim_P X = \dim_M X = dimaff(X)` of the introduction, the last two from cited
theorems taken as hypotheses.

The library declares no axiom: every constant depends on `propext`, `Classical.choice` and
`Quot.sound` only. The literature theorems the article cites without proof are `Prop`-valued
definitions, and every result that uses one takes it as an explicit hypothesis; "Fidelity
boundary" lists them, the rules they obey and their comparison with the sources. Ten are
quantified over every alphabet and every system. Eight are on the main line, in
`BoxLike/Literature.lean` and `BoxLike/LiteratureFeng.lean`. Two are off it and no main result
takes them: `FengHuExactDim` and `FengKaenmakiUnique` in `BoxLike/LiteratureRemarks.lean`.
Fraser's theorem and the theorem of Bárány and Käenmäki are the `Prop`s `System.FraserBound`,
`System.FraserROSC`, `NoOverlap.BaranyKaenmakiTheorem` and `NoOverlap.BaranyKaenmakiPair`,
defined beside the results that take them. Falconer's bound
`eq:hausdorff_affinity_upper_bound`, which the article cites, is proved
(`System.dimH_attractor_le`, through the upper Minkowski dimension). Rossi's bound is a `Prop`
that no theorem takes.

`Challenge.lean` states seven headline results over Mathlib alone, `Solution.lean` proves them
from the library, and the comparator checks the pair (section 0). The module index is the root
module `BoxLike.lean`. This file carries the build setup, the layers of the formalisation, the
state of every labelled result, the remaining work, the findings about the document, the
fidelity boundary, and technique notes.

Convention: state, not history. Edit in place, append nothing; `git log` has the rest.

## 0. Build setup

The checked-in `lakefile.toml` and `lake-manifest.json` are the standard portable ones:
Mathlib is required at `rev = "v4.35.0-rc2"` and `packagesDir` is the default `.lake/packages`.
On this machine `.lake/packages` is a symlink to the already-built tree
`~/Documents/lean/mathematics_in_lean/.lake/packages`, shared with `ML-ST/lean`, `JA-ST/lean`
and the `LeanLibraries` projects. On another machine run `lake exe cache get`.

- `lean-toolchain` is pinned to `v4.35.0-rc2`; Mathlib is pinned to rev `06535612`.
- Do not run `lake update` and do not edit `lean-toolchain` or `lakefile.toml` during routine
  work: re-resolution drags the shared checkouts and breaks the sibling projects.
- Never put an absolute `packagesDir` into `lakefile.toml` or the manifest.
- `native_decide` is banned: at this toolchain every use declares an axiom
  (`<name>._native.native_decide.ax_…`), which the comparator rejects.

```
cd lean
lake build                                # the library `BoxLike`, the default target
lake build Solution                       # the proofs of the headline results
python3 scripts/check_module_headers.py   # the module header of every tracked Lean file
lake comparator --config comparator.json --inadvisably-no-sandbox   # local preflight, macOS
./comparator-audit.sh                     # the sandboxed comparator audit, Linux only
```

Module system. Every Lean file of the project begins with `module` and imports with
`public import`; every file with declarations opens `@[expose] public section`.
`scripts/check_module_headers.py` checks the first line of every Lean file tracked by git.

Palomar layout, after the registered project `JA-ST/lean`. `lakefile.toml` declares the
libraries `BoxLike` (the default target), `Challenge` and `Solution`. `Challenge.lean` states
the headline results over Mathlib alone, with the eight literature `Prop`s of the main line
restated in it, and with an intentional `sorry` for each proof. Its definition block is
identical to `Solution/Definitions.lean`. `Solution.lean` and `Solution/` prove the statements
from the library. The development is licensed under Apache-2.0 (`LICENSE`).

| `Challenge` | Article | Library |
|---|---|---|
| `audit_main1` | `thm:main1` | `System.main1_dimaff` |
| `audit_eq_state_proj_dim` | `thm:eq_state_proj_dim` | `System.eq_state_proj_dim` |
| `audit_main2` | `thm:main2` | `System.main2` |
| `audit_main_extended` | `thm:main_extended` | `System.main_extended_min` |
| `audit_main_extended_ge_two` | `thm:main_extended`, `s ≥ 2` | `System.main_extended_ge_two` |
| `audit_dimH_eq_min` | `\dim_H X = min{2, dimaff(X)}` | `System.dimH_attractor_eq_min` |
| `audit_dimH_of_two_le` | the same for `dimaff(X) ≥ 2` under the strong open set condition | `System.dimH_attractor_of_two_le` |

The comparator is the axiom audit. `comparator.json` lists the seven theorems and permits only
`propext`, `Quot.sound` and `Classical.choice`. `comparator-audit.sh` runs the toolchain's
`lake comparator` inside a `bwrap` sandbox, which exists on Linux only; on macOS the unsandboxed
call above serves as a local preflight.

CI. `.github/workflows/build.yml` runs on every push: it checks the module headers, builds the
library, and in a second job runs `comparator-audit.sh` on `ubuntu-24.04` without compiling
project code beforehand. `.github/workflows/palomar-preflight.yml`, started by hand, runs
Palomar's own submission pipeline on the current commit as a predictive preflight.

`Archive/` is ignored by git. It holds `Archive/tools/LayerE.lean`, the statement layer of
layer E, which the library supersedes (`LAYER_E.md`); it is not built.

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

## 3. State

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

## 4. Remaining work, in order

The four main results are complete, `thm:main_extended` for every `s > 0`, and so is layer E,
whose design `LAYER_E.md` documents. The comparator pair `Challenge.lean` / `Solution.lean`
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

## 5. Findings about the document

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
- From the statement layer of layer E (`LAYER_E.md`, section 5, has the details and says which
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

## 6. Fidelity boundary

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

## 8. Technique notes

- Nested absolute-value bars misparse: write `abs (Real.log |x|)`. The letter `Σ` is a reserved
  token and cannot occur in an identifier.
- While agents have unfinished files under `BoxLike/`, the glob target fails on them: build
  the named target, `lake build BoxLike`.
- A module under development is checked with `lake env lean BoxLike/X.lean`, which writes
  nothing and is safe beside a running `lake build`.
- The `ℓ²` operator norm on matrices is scoped: `open scoped Matrix.Norms.L2Operator`. The norm
  of a box matrix comes from the C*-identity `l2_opNorm_conjTranspose_mul_self` and
  `l2_opNorm_diagonal`, since `Aᵀ A` is diagonal.
- `Subadditive.lim` is irreducible; `System.pressure` is its unfolded `sInf`, and
  `rwa [Subadditive.lim]` bridges the two.
- A higher-order rewrite with `sum_ofFn_add` needs the summand given explicitly.
- Identities in `ZMod 2` close by `generalize` on every atom followed by `revert; decide`.
- The recursion `ε_{m+1} = ε_m + o(i_m)` with `ε_0 = 0` determines `ε` (`eq_eps_of_succ`);
  cocycle identities over `ℤ` are proved through it, avoiding interval sums.
- A literature hypothesis names its universe: `(hfk : FengKaenmakiGibbs.{u})` beside
  `{ι : Type u}`. Without `.{u}` Lean generalises the universe of the hypothesis to a fresh
  one, and the proof cannot apply it at `ι`.
- Lean `v4.35.0-rc2` accepts two modules that declare the same theorem name when both are imported.
  The build does not detect name clashes between the files of different agents; check them by
  grep.
