Status: every statement of this layer is proved in the library, under the same name, except
three literature statements of section 2.1 that no proof needs (`shannonMcMillanBreiman`,
`feng_entropy_kolmogorov_sinai`, `…_bar`) and the four results of Feng that are `Prop`-valued
definitions of `BoxLike/LiteratureFeng.lean`, taken as hypotheses by the results that use them:
`FengInfoSum`, `FengInfoSumBar`, `FengLedrappierYoung` and `FengLedrappierYoungBar`. Birkhoff's
theorem, the Rokhlin properties, Feng's Lemma 4.2 and `thm:feng_entropy_as_limit` are proved.
`System.main_extended_ge_two` and `System.main_extended` are in `BoxLike/MainExtended.lean`. The
file of the statement layer is `Archive/tools/LayerE.lean`, outside git and never built; the
library supersedes it, and it holds no declaration the library lacks. This document is the
design record of the definitions of sections 3.2 to 3.4 of the article
(`sec:lyapunov_exponents`, `sec:conditional`, `sec:entropies`); sections 2 to 4 below describe
the statement layer. `PLAN.md`, section 3, has the state of each result and section 5 the
findings.

# Layer E: statement layer for the entropy part of `diagonal-antidiagonal.tex`

The statement layer states, in Lean 4 over the `BoxLike` library and Mathlib, the definitions
and results of `sec:lyapunov_exponents`, `sec:conditional`, `sec:entropies`, the second half of
`sec:normalisation`, `thm:feng1`, `sec:average_gibbs`, `sec:average_gibbs_entropy`,
`sec:higher_dimensional_entropies` and `sec:dimension_result_proof`. Each statement is marked
LITERATURE, for a theorem the article cites without proof, or PAPER, for a result of the
article.
Tex line numbers refer to `diagonal-antidiagonal.tex` as of 2026-09-20.

## 1. Definitions

### 1.1 Partitions as atom maps, and the domain of a partition

A partition of a set `Ω` is a map `ξ : Ω → Set Ω` sending a point to its atom. The article's
`ξ_i` and `ξ_1^⊥` are partitions of the full-measure set `Σ'` (tex 1949 to 1958) and
`\overline{ξ}_i` are partitions of `Σ_Z` (tex 2008 to 2013), while the conditional measures
are those of measures on `Σ` and on `{1, …, 2N}^ℤ` (tex 2005 to 2006: "extending it by zero").
`atomsOn D ξ` turns a partition of `D ⊆ Ω` into a partition of `Ω` by adding the single atom
`Ω ∖ D`:

```
atomsOn D ξ x = if x ∈ D then ξ x ∩ D else Dᶜ
```

Reason. `ProbabilityTheory.condExpKernel` takes a sub-`σ`-algebra of the ambient standard
Borel space. The extra atom is a null set for every measure the article conditions, so no
almost-everywhere statement changes. The atoms inside `D` are literally the article's.
Checked: `System.mem_xi_self` and `System.xi_eq_of_mem` prove that `ξ_i` is a partition of `Σ`
in this form, for every measure `μ` and every `i`.

Consequence for `thm:double_conditional` and `thm:finer_partition_dirac_mass`. The article
takes "measurable partitions of a Borel set `Σ'` with `μ(Σ') = 1`" and assumes
`ξ'(𝐢) ⊆ ξ(𝐢)` for `𝐢 ∈ Σ'`. The Lean statements take partitions of `Ω` with
`∀ x, ξ' x ⊆ ξ x`. For the extended partitions both atoms equal `Σ ∖ Σ'` outside `Σ'`, so the
hypothesis holds everywhere; `System.xi_succ_subset`, `System.xi_two_subset_xiPerp`,
`System.xiPerp_subset_xi_zero` and `System.xiBar_succ_subset` prove the inclusions of tex 1966
to 1968 and 2020 in this form.

### 1.2 The `σ`-algebra `\widehat{ξ}`

`saturated ξ` is the `σ`-algebra of Borel sets `A` with `x ∈ A ↔ y ∈ A` whenever `y ∈ ξ x`. For
a partition these are the Borel unions of atoms, which is Feng's definition (Section 2.1: "the
sub-`σ`-algebra of `B` whose sets are `ξ`-saturated") and the article's "associated
`σ`-algebra" (tex 1817). The symmetric form of the condition makes `saturated ξ` a
`σ`-algebra for every map `ξ`, and `saturated ξ ≤ mΩ` holds by construction
(`saturated_le`), so the kernel of 1.4 is formed without any measurability proof.

The article adds (tex 1818 to 1819) that partitions are realised as fibres of Borel maps into
standard Borel spaces, "so these `σ`-algebras are countably generated before completion". This
leaves two readings of `\widehat{ξ}`: the saturated Borel sets, and the pull-back of the Borel
`σ`-algebra under the inducing map. `saturated_eq_comap` proves that they are equal, exactly
and not only modulo null sets, when the atoms are the fibres of a Borel map between standard
Borel spaces. The proof is Blackwell's theorem through Lusin separation
(`MeasurableSet.analyticSet_image`, `AnalyticSet.measurablySeparable`). The ambiguity is
therefore void, and a prover may work with either form.

`IsMeasurablePartition ξ` says that the atoms are the fibres of a Borel map `f : Ω → ℝ`:
`∀ x y, y ∈ ξ x ↔ f y = f x`. Every standard Borel space embeds measurably into `ℝ`
(`MeasureTheory.embeddingReal`), so the target `ℝ` loses nothing and avoids a universe
variable.

### 1.3 Instances

`condExpKernel` needs `[StandardBorelSpace Ω]` and `[IsFiniteMeasure μ]`. For the alphabet the
library's standing instances are `[Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]`.
They give `DiscreteMeasurableSpace ι` (`MeasurableSingletonClass.toDiscreteMeasurableSpace`),
hence `StandardBorelSpace ι` (`standardBorelSpace_of_discreteMeasurableSpace`), hence
`StandardBorelSpace (ℤ → ι)` and `StandardBorelSpace (ℤ → ι × ZMod 2)`
(`StandardBorelSpace.pi_countable`, `StandardBorelSpace.prod`). Two `example`s in
`BoxLike/Conditional.lean` check both by `inferInstance`. Finite measures: `condMeas μ ξ x` is a
probability measure (an instance in `BoxLike/Conditional.lean`), `μ[|Ξ]` is finite by Mathlib,
and `avgMeasure μ₁ μ₂` is finite (an instance in `BoxLike/DimPartitions.lean`) and a
probability measure (`isProbabilityMeasure_avgMeasure`, proved).

### 1.4 Conditional measures

`condMeas μ ξ x = condExpKernel μ (saturated ξ) x` mirrors tex 1820 to 1834. The kernel is
defined at every point, is `\widehat{ξ}`-measurable (`measurable_condMeas`, proved), satisfies
`∫_B μ_x^ξ(A) dμ = μ(A ∩ B)` (`setLIntegral_condMeas`) and is determined up to a `μ`-null set
of points (`condMeas_unique`).

"The conditional measure supported on `ξ(𝐢)`" (tex 1822, 2041) has no pointwise meaning for a
kernel defined almost everywhere. Its meaning here is the statement `condMeas_atom`: for a
measurable partition, `μ_x^ξ(ξ(x)) = 1` for `μ`-almost every `x`.

Identities between conditional measures are almost-everywhere equalities of measures. The
article's "simultaneously for all Borel sets `A`" (tex 1859) is the equality of the two
measures. Where the article writes `μ({𝐢 : μ_𝐢^ξ = δ_𝐢}) = 1`, the Lean statement is
`∀ᵐ x ∂μ, condMeas μ ξ x = Measure.dirac x`; this needs no measurability of the set.

The normalised restriction `μ_Ξ` (tex 1845 to 1848) is Mathlib's `ProbabilityTheory.cond`,
written `μ[|Ξ]`.

### 1.5 Conditional information and the entropies

- `condInfo μ ξ x = -log μ_x^ξ([x_0])` is `I_μ(𝒫 | \widehat{ξ})(x)` of tex 1798 to 1803, with
  the conditional expectation `E_μ(1_{[x_0]} | \widehat{ξ})` realised by the kernel. It is
  non-negative (`condInfo_nonneg`, proved). Where `μ_x^ξ([x_0]) = 0`, Lean's `Real.log 0 = 0`
  gives `0` and the article `+∞`; this set is `μ`-null (Feng, Lemma 2.2).
- `condEntropy μ ξ = ∫ condInfo μ ξ dμ` is `H_μ(𝒫 | \widehat{ξ})` (tex 1804 to 1808). The
  integral is a genuine value once `integrable_condInfo` is known.
- `localEntropy μ ξ = μ[condInfo μ ξ | MeasurableSpace.invariants (shift 1)]` is
  `E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)` (tex 1980). Mathlib's `invariants` is the `σ`-algebra of
  Borel sets with `σ⁻¹A = A`, which is the article's `ℐ`. The function is a conditional
  expectation and is determined up to a null set, so every statement about `h_i(μ, 𝐢)` is an
  almost-everywhere statement, as in the article.

How `h_i(μ)` is obtained from `h_i(μ, 𝐢)`. The article defines
`h_i(μ) = ∫ h_i(μ, 𝐢) dμ = H_μ(𝒫 | \widehat{ξ}_i)` (tex 1985 to 1989). Lean defines `h_i(μ)` as
`H_μ(𝒫 | \widehat{ξ}_i)`; `integral_localEntropy` proves the first equality, and
`localEntropy_ae_eq` states `eq:ergodic_entropy_constant`.

`h_0` and the Kolmogorov–Sinai entropy. The library's `entropy μ` is
`lim_n n⁻¹ H_μ(𝒫_0^{n-1})`. `thm:feng1` carries `h_0(μ) = H_μ(𝒫 | \widehat{ξ}_0)`. The bridge
is `System.dimEntropy_zero_eq_entropy` and `System.dimEntropyBar_zero_eq_entropy` (tex 2087 to
2091). Hypotheses such as `h_0(μ) ≤ -λ_1(𝖠, μ)` are written with `entropy μ`, which is the
quantity in `eq:eq_state_def` and in the real-variable lemmas of `LyapunovDim`.

Two-sided shifts are used throughout, as in the article and in Feng: the partitions fix the
past `𝐢^-` and `π` depends on the future `𝐢^+`. `SamePast x y` is `∀ n < 0, x n = y n`
(tex 855 to 856). `𝒫_0^{n-1}(𝐢)` is `cylinder (block n x)`.

### 1.6 `Σ^τ`, `Σ^ω`, `Σ'`

The article first describes `Σ'` through Oseledets' theorem (tex 1642 to 1664) and then fixes
it in the box-like case (tex 1675 to 1677): "all sequences for which the two backward
coordinate growth rates exist and equal `λ_1(𝖠, μ)` and `λ_2(𝖠, μ)` in either order". Lean
follows the second description:

```
S.HasBackRate y l  :=  Tendsto (fun n => log |S.gDeriv (pastWord y n)| / n) atTop (𝓝 l)
S.SigmaTau μ   = {x | HasBackRate (τ x) λ₁ ∧ HasBackRate (ω x) λ₂}     -- V¹ is the y-axis
S.SigmaOmega μ = {x | HasBackRate (τ x) λ₂ ∧ HasBackRate (ω x) λ₁}     -- V¹ is the x-axis
S.SigmaPrime μ = S.SigmaTau μ ∪ S.SigmaOmega μ
```

By `thm:matrix_products_g_derivatives` the rate along `τ(𝐢)` is the growth rate of
`|A_{i_{-n}} ⋯ A_{i_{-1}} e_1|` and the rate along `ω(𝐢)` that of `e_2`
(`System.hasBackRate_tau_iff`, `System.hasBackRate_omega_iff`, proved). No Oseledets theorem
is needed. The measure enters through the two numbers `λ_1`, `λ_2` only. When `λ_1 = λ_2` the
sets `Σ^τ` and `Σ^ω` coincide.

Proved in `BoxLike/SlowAxis.lean`: `Σ^τ`, `Σ^ω`, `Σ'` are Borel (`measurableSet_SigmaTau`,
`measurableSet_SigmaOmega`, `measurableSet_SigmaPrime`); they are saturated with respect to the
past (`mem_SigmaTau_of_samePast`, `mem_SigmaOmega_of_samePast`, tex 1680 to 1681); they are
disjoint when `λ_2 < λ_1` (`disjoint_SigmaTau_SigmaOmega`, `eq:tau_omega_partition2`). Proved in
`BoxLike/SigmaMeasure.lean` and `BoxLike/PartitionIdentities.lean`: `μ(Σ') = 1` for ergodic `μ`
(`measure_SigmaPrime_compl`) and the behaviour under the shift (`shift_mem_SigmaTau_iff`, which
is `eq:sigma_tau_omega_positive_eq_measure1` and gives `σ(Σ') = Σ'`).

### 1.7 The slow axis and `V_𝐢^i`

`S.slowAxis μ x : ZMod 2` is `1` on `Σ^τ` (the `y`-axis) and `0` elsewhere, which on `Σ^ω` is
the `x`-axis when `λ_2 < λ_1`. `S.oseledets μ x i` is `ℝ²` for `i = 0`, the axis
`{v | coord (slowAxis + 1) v = 0}` for `i = 1` and `{0}` for `i ≥ 2`
(`mem_oseledets_iff`, proved, unfolds membership of a difference). The slow axis depends only on
the past (`slowAxis_eq_of_samePast`, proved), which is Feng's Lemma 4.1 in the box-like case.

### 1.8 The partitions

```
S.xi μ i    = atomsOn Σ'  fun x => {y | SamePast y x ∧ π y - π x ∈ V_x^i}
S.xiPerp μ  = atomsOn Σ'  fun x => {y | SamePast y x ∧ coord (slowAxis x) (π y - π x) = 0}
S.xiBar 0   = atomsOn Σ_Z fun y => {z | SamePast z y}
S.xiBar _   = atomsOn Σ_Z fun y => {z | SamePast z y ∧ \overline{π} z = \overline{π} y}
```

These are tex 1949 to 1958 and 2008 to 2013 verbatim. Orthogonality to a coordinate axis is the
vanishing of that coordinate. Indices above the article's range repeat the last partition.

### 1.9 Entropies of the system

`S.dimEntropy μ i`, `S.dimEntropyAt μ i`, `S.dimEntropyBar ν i`, `S.dimEntropyBarAt ν i` are
`h_i(μ)`, `h_i(μ, ·)`, `\overline{h}_i(ν)`, `\overline{h}_i(ν, ·)`.

### 1.10 The average measure, the Gibbs measures, the separation condition

`avgMeasure μ₁ μ₂ = (2⁻¹ : ℝ≥0) • (μ₁ + μ₂)` is `eq:average_gibbs`. The scalar lies in `ℝ≥0`
because Mathlib's finiteness instance for scalar multiples is for `ℝ≥0`.

"`μ_1`, `μ_2` are the `s`-Gibbs measures" is the hypothesis
`hdec : S.GibbsDecomposition s μ μ₁ μ₂`, the conclusion of `thm:eq_state_is_sum`, together with
`[IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]` where conditional measures of `μ_k`
occur. `S.fastPart μ = τ(Σ^τ) ∪ ω(Σ^ω)` and `S.slowPart μ = ω(Σ^τ) ∪ τ(Σ^ω)` name the two
unions of `thm:gibbs_tau_omega_positive`. The inverses `\overline{τ}`, `\overline{ω}` are
`unCode`, and `\overline{τ}(B)` for `B ⊆ τ(Σ)` is `unCode '' B`.

The strong open set condition is `System.StrongOpenSet` of
`BoxLike/SeparationConditions.lean`, which is built and imported; that module also proves
`System.StrongOpenSet.sq`.

### 1.11 Hypotheses

The statements take the article's hypotheses: `S.WithRotations`, `S.Proximal` or, where the
article assumes the normalised tuple, `S.HasProximalDiagonal`; `S.ProjExpSeparation`;
`0 < s`, `s < 2`; `[IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)`;
`S.IsEquilibriumState s μ`; `hP : S.pressure s = 0` for `s = dimaff(𝖠)`. Ergodicity of the
equilibrium state is the hypothesis `herg : Ergodic (shift 1) μ`, which the article takes from
`thm:irred_eq_state`. The statements hold for every invariant equilibrium state; uniqueness is
not used. `S.lyapunov₂ μ < S.lyapunov₁ μ` is a hypothesis `hlt` where the article assumes it
and is derived from the hypothesis `MorrisShmerkinLyapunov` through `System.simple_lyapunov` in
the assembly. The cited theorems enter as the hypotheses `hms`, `hfk`, `hfjj`, `hjr`, `hfi`,
`hfib`, `hly`, `hlyb` of `PLAN.md`, section 6.

For the three proved statements of `sec:lyapunov_exponents` the hypotheses are the minimal ones,
which are weaker than the article's. `thm:lyapunov_exponents_via_g_system` holds by definition
of the box-like `Σ'`, for every measure and every `𝐢 ∈ Σ'`.

## 2. Statements

Difficulty: S under 100 lines, M 100 to 400, L more, X needs theory missing from Mathlib.
"proved" marks a statement that the layer proved from the others; the difficulty of every
other statement is the estimate on which the order of proof of section 3 rests.

### 2.1 LITERATURE

| Name | Source, tex label | Depends on | Difficulty |
|---|---|---|---|
| `birkhoff_ae` | Birkhoff's pointwise ergodic theorem, general form; used by Feng, Lemma 4.6, and for `μ(Σ') = 1` | none | X: no pointwise ergodic theorem in Mathlib; a self-contained proof through the maximal ergodic theorem is L |
| `birkhoff_ergodic` | the form of tex 1706 to 1711, 2541 to 2547, 3634 | `birkhoff_ae` | S |
| `shannonMcMillanBreiman` | tex 2071 to 2075 | `birkhoff_ae`, Mathlib's `Integrable.tendsto_ae_condExp`, conditional information calculus | X: L once Birkhoff and the chain rule for conditional information exist |
| `integrable_condInfo` | Feng, Lemma 2.1(v), (4.15); tex 1991 to 1992 | none | M |
| `setLIntegral_condMeas` | Rokhlin; tex 1824 to 1827 | Mathlib `condExpKernel_ae_eq_condExp`, `setIntegral_condExp` | S |
| `condMeas_unique` | Rokhlin; tex 1828 | Mathlib `Probability/Kernel/Disintegration/Unique.lean` or a `π`-system argument | M |
| `condMeas_atom` | Rokhlin; tex 1822 to 1823 | `saturated_eq_comap`, `setLIntegral_condMeas` | M |
| `System.isMeasurablePartition_xi` | Feng, Lemma 4.2; tex 1959 to 1960 | `measurableSet_SigmaTau`, `System.Bounds.measurable_proj`, `embeddingReal` | M |
| `System.isMeasurablePartition_xiPerp` | tex 1960 | same | M |
| `System.isMeasurablePartition_xiBar` | Feng, Lemma 4.2 for `Ψ` | `measurableSet_subshift`, `System.Bounds.measurable_projBar` | M |
| `FengInfoSum`, `FengInfoSumBar` | Feng, Lemma 4.6, first identity of (4.16); used in the proof of `thm:feng_entropy_zero` | Feng, Lemma 4.4(1), Lemma 2.1(ii),(iii) | X: conditional information calculus (chain rule, behaviour under `σ`) is missing; L. A hypothesis |
| `System.feng_entropy_as_limit`, `System.feng_entropy_as_limit_bar` | `thm:feng_entropy_as_limit`; Feng, Lemma 4.6 | `FengInfoSum`, `birkhoff_ae`, `integrable_condInfo` | M given its inputs |
| `System.feng_entropy_kolmogorov_sinai`, `System.feng_entropy_kolmogorov_sinai_bar` | `thm:feng_entropy_kolmogorov_sinai`; Feng (4.17) | Shannon–McMillan–Breiman for `σ` and `σ⁻¹` in its non-ergodic form | X, L |
| `FengLedrappierYoung` | `thm:feng1`, `eq:feng1_1`; Feng, Theorems 1.2 and 1.3 | Feng's article | X: a hypothesis |
| `FengLedrappierYoungBar` | `thm:feng1`, second display; Feng, Theorems 1.2 and 1.3 for `Ψ` | Feng's article | X: a hypothesis |

### 2.2 PAPER and INFRASTRUCTURE

| Name | tex label | Depends on | State, difficulty |
|---|---|---|---|
| `saturated_eq_comap` | tex 1818 to 1819 | Mathlib (Lusin separation) | proved |
| `System.hasBackRate_tau_iff`, `System.hasBackRate_omega_iff` | `thm:matrix_products_g_derivatives` | library | proved |
| `System.lyapunov_exponents_via_g_system` | `thm:lyapunov_exponents_via_g_system` | definitions | proved |
| `System.disjoint_SigmaTau_SigmaOmega` | `eq:tau_omega_partition2` | none | proved |
| `System.mem_SigmaTau_of_samePast`, `System.mem_SigmaOmega_of_samePast` | tex 1680 to 1681 | `codeWord_pastWord_tau`, `oWord_pastWord` | proved |
| `System.measurableSet_SigmaTau`, `…SigmaOmega`, `…SigmaPrime` | tex 1677 | `measurableSet_tendsto` | proved |
| `System.mem_xi_self`, `System.xi_eq_of_mem`, `System.xi_succ_subset`, `System.xi_two_subset_xiPerp`, `System.xiPerp_subset_xi_zero`, `System.xiBar_succ_subset` | tex 1954, 1966 to 1968, 2020 | past saturation | proved |
| `integral_localEntropy`, `condInfo_nonneg`, `measurable_condMeas`, `isProbabilityMeasure_avgMeasure` | tex 1985 to 1989 | Mathlib | proved |
| `System.measure_SigmaPrime_compl` | tex 1677 | `birkhoff_ae`, `thm:tau_omega_sigma_commutative`, `thm:matrix_products_g_derivatives` | M to L |
| `System.shift_mem_SigmaTau_iff` | `eq:sigma_tau_omega_positive_eq_measure1`, tex 1678 to 1679 | `eq:tau_omega_sigma_commutative1` | S to M |
| `System.lyapunov_exponent_gsystem` | `eq:lyapunov_exponent_gsystem` | `birkhoff_ergodic` for `σ⁻¹` (`Ergodic.symm`), `System.lyapBarLim_eq` | M |
| `condMeas_cond`, `condMeas_cond_of_saturated` | `thm:conditional_measures_of_a_conditional_measure` | `setLIntegral_condMeas`, `condMeas_unique` | M, S |
| `double_conditional` | `thm:double_conditional` | `setLIntegral_condMeas`, `condMeas_unique`, `saturated_eq_comap` | M to L |
| `finer_partition_dirac_mass` | `thm:finer_partition_dirac_mass` | `double_conditional` | M |
| `localEntropy_ae_eq` | `eq:ergodic_entropy_constant` | Mathlib `Ergodic.ae_eq_const_of_ae_eq_comp₀`, `integral_condExp` | S |
| `System.dimEntropy_zero_eq_entropy` | tex 2087 to 2090 | `feng_entropy_kolmogorov_sinai`, `shannonMcMillanBreiman`, `localEntropy_ae_eq` | S |
| `System.dimEntropyBar_zero_eq_entropy` | tex 2091 | `feng_entropy_kolmogorov_sinai_bar`, `shannonMcMillanBreiman`, `localEntropy_ae_eq` | S |
| `System.feng_entropy_zero`, `System.feng_entropy_zero_bar` | `thm:feng_entropy_zero` | `FengInfoSum`, `feng_entropy_as_limit`, `condMeas_atom`, `isMeasurablePartition_*` | M each |
| `System.partitions_xi1` | `thm:partitions_xi1` | `eq:commutative_diagram`, `range_tau`, `range_omega`, past saturation, disjointness | M |
| `System.partition_tau_conj` | `thm:partition_tau_conj` | `partitions_xi1`, `eps_congr` | S to M |
| `System.sigma_tau_omega_positive` | `thm:sigma_tau_omega_positive_eq_measure` | `System.simple_lyapunov`, `shift_mem_SigmaTau_iff`, `measure_SigmaPrime_compl`, `FengKaenmakiGibbs`, `birkhoff_ergodic` | M |
| `System.ergodic_of_gibbsDecomposition`, `System.ergodic_of_hasProximalDiagonal` | INFRASTRUCTURE | `MeasurePreserving.ergodic_of_ergodic_semiconj`; the second also `FengKaenmakiGibbs`, `FraserJordanJurgaDecomposition` | proved |
| `System.gibbs_tau_omega_positive` | `thm:gibbs_tau_omega_positive` | `lyapunov_exponent_gsystem`, `lyapunov_exponents_via_g_system`, `measure_SigmaPrime_compl`, `sigma_tau_omega_positive`, `System.simple_lyapunov` | M |
| `System.orientation_restrictions` | `eq:orientation-restrictions` | `GibbsDecomposition.eq_tau`, `eq_omega`, `gibbs_tau_omega_positive`, `sigma_tau_omega_positive` | M |
| `System.conditional_two_ways` | `thm:conditional_two_ways` | `orientation_restrictions`, `gibbs_tau_omega_positive`, `partitions_xi1`, `condMeas_cond_of_saturated`, `condMeas_unique`, Lusin–Souslin (`MeasurableSet.image_of_measurable_injOn`) | L |
| `System.overline_h1_zero` | `thm:overline_h1_zero` | `JordanRapaportDimension`, `GibbsDecomposition.entropy_eq₁`, `entropy_eq₂`, `FengLedrappierYoungBar`, `dimEntropyBar_zero_eq_entropy`, `feng_entropy_as_limit_bar`, `localEntropy_ae_eq`, `conditional_two_ways`, `gibbs_tau_omega_positive` | M |
| `System.overline_h1_zero_large` | `thm:overline_h1_zero_large` | as above with `feng_entropy_zero_bar` | M |
| `System.overline_h1_large` | `thm:overline_h1_large` | `gibbs_tau_omega_positive`, `orientation_restrictions`, `conditional_two_ways`, `partition_tau_conj`, `feng_entropy_as_limit`, `feng_entropy_as_limit_bar`, `localEntropy_ae_eq` | M to L |
| `System.eq_state_h1_zero` | `thm:eq_state_h1_zero` | `overline_h1_zero`, `feng_entropy_zero`, `feng_entropy_zero_bar`, `conditional_two_ways`, `orientation_restrictions`, `measure_SigmaPrime_compl`, `localEntropy_ae_eq`, the hypotheses `FengKaenmakiGibbs` and `FraserJordanJurgaDecomposition` | M |
| `System.eq_state_h1_large` | `thm:eq_state_h1_large` | `JordanRapaportDimension`, `FengLedrappierYoungBar`, `dimEntropyBar_zero_eq_entropy`, `overline_h1_large`, `IsExactDim.unique` | S to M |
| `System.eq_state_h2_zero` | `thm:eq_state_h2_zero` | `eq_state_h1_zero`, `finer_partition_dirac_mass`, `feng_entropy_zero`, `isMeasurablePartition_xi`, `xi_succ_subset` | S |
| `System.orto_partition_dirac` | `thm:orto_partition_dirac` | `overline_h1_zero_large`, `conditional_two_ways`, `orientation_restrictions`, `finer_partition_dirac_mass`, `feng_entropy_zero`, `xi_two_subset_xiPerp` | M |
| `System.SOSC_h2_zero` | `thm:SOSC_h2_zero` | `FengKaenmakiGibbs` (full support), `System.simple_lyapunov`, `measure_SigmaPrime_compl`, recurrence (`birkhoff_ergodic`, or Poincaré recurrence of `Mathlib/Dynamics/Ergodic/Conservative.lean` with ergodicity), `System.Bounds.proj_eq`, `condMeas_atom`, `feng_entropy_zero` | L |
| `System.main_extended_ge_two` | `thm:main_extended`, case `s ≥ 2` | Bernoulli equilibrium state for `s ≥ 2` (tex 2471 to 2480), strict monotonicity of the pressure, Hutchinson's uniqueness of the invariant measure, `addHaar_image_linearMap` | L, X for Hutchinson's measure (template `LeanLibraries/FractalGeometry/Hutchinson.lean`) |
| `neg_lt_entropy_of_two_le` | first step of the proof of `thm:main_extended` | none | proved |
| `System.main_extended_normalised` | `thm:main_extended`, `0 < s < 2`, normalised | `MorrisShmerkinLyapunov`, `FengLedrappierYoung`, `dimEntropy_zero_eq_entropy`, `eq_state_h1_zero`, `eq_state_h2_zero`, `eq_state_h1_large`, `orto_partition_dirac`, `SOSC_h2_zero`, `ledrappierYoung_small`, `ledrappierYoung_large`, `entropy_lt_of_lt_two`, `lyapDim_eq`, `IsEquilibriumState.pressure_eq` | proved |
| `System.main_extended_lt_two_aux`, `System.main_extended_lt_two`, `System.main_extended_lt_two'` | `thm:main_extended`, `0 < s < 2` | `main_extended_normalised`, `Proximal.hasProximalDiagonal_or_sq`, `IsEquilibriumState.map_group`, `pressure_sq`, `entropy_map_group`, `lyapunov₂_sq_map_group`, `ProjExpSeparation.sq`, `StrongOpenSet.sq`, `proj_sq_group`; the primed version also `ergodic_of_hasProximalDiagonal` | proved |
| `System.main_extended` | `thm:main_extended` | `main_extended_lt_two`, `main_extended_ge_two`, `neg_lt_entropy_of_two_le` | proved |
| `System.main2_of_bounds`, `System.main2` | `thm:main2` | `System.simple_lyapunov`, `entropy_le_iff`, `main_extended_lt_two'` and the hypotheses `hupper`, `hlower`; `main2` discharges them by `System.dimH_attractor_le` and `System.le_dimH_attractor` | proved |

The assembly theorems are fully proved from the statements above. `main2_of_bounds` has
exactly the hypotheses of `thm:main2` together with `hupper` (Falconer) and `hlower`; it needs
no ergodicity hypothesis. `hupper` is `System.dimH_attractor_le` of `BoxLike/FalconerBound.lean`
and `hlower` is `System.le_dimH_attractor` of `BoxLike/AffinityMain.lean`.

## 3. Order of proof

Each line lists the literature inputs it needs beyond the lines before it.

1. `setLIntegral_condMeas`, `condMeas_unique`, `condMeas_atom`, `integrable_condInfo`:
   Mathlib only.
2. `condMeas_cond`, `condMeas_cond_of_saturated`, `double_conditional`,
   `finer_partition_dirac_mass`: from 1.
3. `localEntropy_ae_eq`: Mathlib only.
4. `shift_mem_SigmaTau_iff`: library only.
5. `isMeasurablePartition_xi`, `isMeasurablePartition_xiPerp`, `isMeasurablePartition_xiBar`:
   library and Mathlib only.
6. `partitions_xi1`, then `partition_tau_conj`: library only.
7. `measure_SigmaPrime_compl`: `birkhoff_ae`.
8. `lyapunov_exponent_gsystem`: `birkhoff_ergodic`.
9. `sigma_tau_omega_positive`: `birkhoff_ergodic`, `FengKaenmakiGibbs`,
   `MorrisShmerkinLyapunov`; uses 4 and 7.
10. `gibbs_tau_omega_positive`: `FraserJordanJurgaDecomposition` through `hdec`; uses 7, 8, 9.
11. `orientation_restrictions`: uses 9, 10.
12. `conditional_two_ways`: uses 1, 2, 5, 6, 10, 11.
13. `feng_entropy_zero`, `feng_entropy_zero_bar`: `FengInfoSum`, `FengInfoSumBar`,
    `feng_entropy_as_limit`, `feng_entropy_as_limit_bar`; uses 1, 5.
14. `dimEntropy_zero_eq_entropy`, `dimEntropyBar_zero_eq_entropy`:
    `feng_entropy_kolmogorov_sinai`, `feng_entropy_kolmogorov_sinai_bar`,
    `shannonMcMillanBreiman`; uses 3.
15. `overline_h1_zero`, `overline_h1_zero_large`: `JordanRapaportDimension`,
    `FengLedrappierYoungBar`, `feng_entropy_as_limit_bar`; uses 3, 10, 12, 13, 14.
16. `overline_h1_large`: `feng_entropy_as_limit`, `feng_entropy_as_limit_bar`; uses 3, 6, 10,
    11, 12.
17. `eq_state_h1_zero`: `FengKaenmakiGibbs`, `FraserJordanJurgaDecomposition`; uses 7, 11,
    12, 13, 15.
18. `eq_state_h1_large`: `JordanRapaportDimension`, `FengLedrappierYoungBar`; uses 14, 16.
19. `eq_state_h2_zero`: uses 2, 5, 13, 17.
20. `orto_partition_dirac`: uses 2, 5, 11, 12, 13, 15.
21. `SOSC_h2_zero`: `FengKaenmakiGibbs`, `birkhoff_ergodic` or Poincaré recurrence; uses 1, 5,
    7, 13.
22. `main_extended_normalised` (proved): `FengLedrappierYoung`, `MorrisShmerkinLyapunov`; uses
    14, 17 to 21.
23. `main_extended_lt_two`, `main_extended_lt_two'` (proved): uses 22.
24. `main_extended_ge_two`: independent of 1 to 23.
25. `main_extended`, `main2_of_bounds`, `main2` (proved): uses 23, 24.

`SOSC_h2_zero` and `sigma_tau_omega_positive` are stated for every proximal tuple, as in the
article. The assembly uses them for a tuple containing a proximal diagonal generator only. In
the general case their proofs need `S.Irreducible` for a proximal tuple with rotations, which
follows from `Proximal.hasProximalDiagonal_or_sq` and `irreducible_of_hasProximalDiagonal`
applied to `S.sq`, since a common invariant line of `𝖠` is one of `𝖠²`.

## 4. Literature inputs that become hypotheses

Under the rules of `PLAN.md`, section 6, a cited theorem is a `Prop`-valued definition that the
results using it take as a hypothesis, and new ones need explicit authorisation. The inputs of
layer E fall into three groups.

Literature statements with no realistic alternative, the `Prop`s of
`BoxLike/LiteratureFeng.lean`.

- `FengLedrappierYoung`, `FengLedrappierYoungBar`. D.-J. Feng, *Dimension of invariant measures for
  affine iterated function systems*, Duke Math. J. 172 (2023), Theorems 1.2 and 1.3
  (arXiv:1901.01691; the local PDF is the arXiv version of June 2020). The planar statement is
  the case `d = 2`, `s = 2`, `k_1 = k_2 = 1`; the scalar statement is the case `d = 1` for `Ψ`.
  The article cites Feng–Hu, Comm. Pure Appl. Math. 62 (2009), Theorem 2.8, for the
  exact-dimensionality in the scalar case (tex 2977, 3351); whether its entropy term equals
  `\overline{h}_0 - \overline{h}_1` was not compared.
- `FengInfoSum`, `FengInfoSumBar`. Feng, Lemma 4.6, first identity of (4.16). They can be
  proved from Birkhoff and Feng's Lemmas 2.1 and 4.4, which is a development of conditional
  information that Mathlib lacks. `System.feng_entropy_as_limit` and
  `System.feng_entropy_as_limit_bar` are proved from them with Birkhoff. Feng's (4.17),
  `feng_entropy_kolmogorov_sinai` and `…_bar`, is not needed: `PastEntropy` proves
  `h_0(μ) = h(μ)` and `\overline{h}_0(ν) = h(ν)` directly.

The Lean statements specialise Feng's results in two ways that a comparison with the source
must accept. First, Feng's `Σ'` is any invariant Borel set of full measure on which the
Oseledets properties hold and `ξ_i` partitions `Σ'`; here `Σ'` is the article's box-like set
and the partition is extended by one null atom. Two such choices give `σ`-algebras that agree
modulo null sets. Second, for `Ψ` the article restricts `\overline{ξ}_i` to `Σ_Z`, which has
full measure (tex 2014 to 2017). Degenerate instance checked by hand for both parts of
`thm:feng1`: a Dirac mass on a constant sequence over a diagonal generator with
`|a| ≠ |b|` gives `h_i = 0`, the formula gives `0`, and the projected measure is a Dirac mass
of pointwise dimension `0`. For `λ_1 = λ_2` the planar statement is silent through `hlt`.

Standard theorems, proved in the library except Shannon–McMillan–Breiman, which no proof needs.

- Birkhoff's pointwise ergodic theorem (`birkhoff_ae`, `birkhoff_ergodic`). Mathlib at this pin
  has `birkhoffSum`, `birkhoffAverage` and the von Neumann mean ergodic theorem
  (`Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean`), and no pointwise theorem. A proof
  through the maximal ergodic theorem is self-contained. `birkhoff_ergodic` follows from
  `birkhoff_ae` and `Ergodic.ae_eq_const_of_ae_eq_comp₀`.
- Shannon–McMillan–Breiman (`shannonMcMillanBreiman`). Mathlib has neither the theorem nor
  conditional information. It has the martingale convergence theorems
  (`MeasureTheory.Integrable.tendsto_ae_condExp`,
  `MeasureTheory.Submartingale.ae_tendsto_limitProcess`) that the standard proof uses.
- Rokhlin's disintegration (`setLIntegral_condMeas`, `condMeas_unique`, `condMeas_atom`).
  Mathlib has the existence (`condExpKernel`, `condDistrib`) and a uniqueness theorem for
  disintegrations (`Mathlib/Probability/Kernel/Disintegration/Unique.lean`). The three
  statements are repackagings of moderate length. Lusin–Souslin
  (`MeasurableSet.image_of_measurable_injOn`) and Lusin separation are in Mathlib.
- Feng, Lemma 4.2 (`isMeasurablePartition_*`) and Feng, Lemma 2.1(v)
  (`integrable_condInfo`): elementary here.

Inputs of the same sections that need no new statement.

- Oseledets' theorem and Froyland–Lloyd–Quas, Theorem 4.1 (tex 1642 to 1664): not needed,
  because `Σ'` has its box-like form. Mathlib has neither Oseledets' nor Kingman's theorem.
- Morris–Shmerkin, Fraser–Jordan–Jurga, Feng–Käenmäki, Jordan–Rapaport: the four `Prop`s of
  `BoxLike/Literature.lean`, `MorrisShmerkinLyapunov`, `FraserJordanJurgaDecomposition`,
  `FengKaenmakiGibbs` and `JordanRapaportDimension`.
- The Kolmogorov–Sinai generator theorem (Bowen, tex 2063 to 2070): not needed, since
  `entropy` is defined through the generator `𝒫`.
- Feng–Hu, Theorem 2.8 (tex 3351): contained in `JordanRapaportDimension`, whose conclusion
  is exact-dimensionality with the value.
- Rossi, Theorem 2.2 (`eq:hausdorff_ergodic_lyapunov`): not used, see section 5.
- Falconer, Theorem 5.4 (`eq:hausdorff_affinity_upper_bound`): the hypothesis `hupper` of
  `System.main2_of_bounds`, proved as `System.dimH_attractor_le`.
- `eq:dimension_measure_def` (Falconer, *Techniques*, §10): the hypothesis `hlower`, proved as
  `System.le_dimH_attractor`.
- For `s ≥ 2`: Hutchinson's uniqueness of the invariant measure (not in Mathlib),
  Käenmäki–Vilppolainen, Lemma 2.1 (strict monotonicity of the pressure), the change of
  variables for Lebesgue measure (Mathlib: `MeasureTheory.Measure.addHaar_image_linearMap`).
- `thm:irred_eq_state`, uniqueness and ergodicity: not needed as a hypothesis, see section 5.

## 5. Findings about the article

Checked means: verified by a proved Lean declaration. Read means: observed while transcribing
the proof, with no Lean proof behind it.

1. `thm:lyapunov_exponents_via_g_system` (tex 1721 to 1782). Checked. With the box-like choice
   of `Σ'` made at tex 1675 to 1677 the four limits hold by definition of `Σ^τ` and `Σ^ω`, for
   every `𝐢 ∈ Σ'`, and none of the hypotheses (proximal, with rotations, ergodic,
   `λ_2 < λ_1`) is used. The hypotheses carry the two facts the text states without proof:
   `μ(Σ') = 1` and `Σ^τ ∩ Σ^ω = ∅`. The second is checked
   (`disjoint_SigmaTau_SigmaOmega`). The first does not need Oseledets' theorem: the two
   backward rates are Birkhoff averages under `σ⁻¹` for the invariant lift
   `(τ_*μ + ω_*μ)/2` on `Σ_Z`; their maximum and their sum are `σ`-invariant, hence constant,
   and equal `λ_1` and `λ_1 + λ_2` by bounded convergence and invariance. This argument is
   read, not checked. Borel measurability and saturation with respect to the past are checked.

2. Ergodicity of the equilibrium state. Checked relative to the literature hypotheses. In the
   normalised case `μ = q_*μ_1` is a factor of the ergodic Gibbs measure `μ_1`, so
   `thm:eq_state_is_sum` alone gives ergodicity (`ergodic_of_gibbsDecomposition`,
   `ergodic_of_hasProximalDiagonal`). The same applies to `μ^(2)` for `𝖠²`. The assembled
   `main2_of_bounds` therefore uses `thm:irred_eq_state` through its Gibbs bounds only; its uniqueness
   and ergodicity assertions are not inputs of `thm:main2`.

3. Proof of `thm:main_extended`, tex 3730 to 3732. Checked. The sentence "Since
   `dim(π_*μ) ≤ dim_L(𝖠, μ)` by `eq:hausdorff_ergodic_lyapunov`, it suffices to show the lower
   bound" is not used: `eq:main_extended1` and `eq:main_extended2` are equalities obtained from
   `thm:feng1`. `main_extended_normalised` is proved without Rossi's theorem.

4. `thm:overline_h1_zero_large` (tex 3403 to 3443) and `thm:orto_partition_dirac` (tex 3586 to
   3609). Read. Both assume `-λ_1(𝖠, μ) ≤ h_0(μ) ≤ -λ_2(𝖠, μ)`, and both proofs use the upper
   bound `h_0(μ) ≤ -λ_2(𝖠, μ)` only. Without the lower bound, `thm:orto_partition_dirac`
   contains `thm:eq_state_h2_zero`, and the case distinction for `h_2` in the proof of
   `thm:main_extended` reduces to `h_0(μ) ≤ -λ_2(𝖠, μ)`. The Lean statements keep the
   article's hypotheses.

5. `h_0` and `\overline{h}_0` have two meanings. `sec:entropies` defines
   `h_0(μ) = H_μ(𝒫 | \widehat{ξ}_0)`; `eq:eq_state_def`, `thm:entropy_eq_gibbs` and
   Jordan–Rapaport use the Kolmogorov–Sinai entropy. The planar identification is
   `thm:feng_entropy_kolmogorov_sinai` with Shannon–McMillan–Breiman. The scalar identification
   `\overline{h}_0(ν) = h(ν)` is asserted in running text (tex 2091) with no lemma and no
   citation, and it is used in `thm:overline_h1_zero`, `thm:overline_h1_zero_large` and
   `thm:eq_state_h1_large`, where the `\overline{h}_0(μ_k)` of `thm:feng1` is equated with the
   entropy of `thm:entropy_eq_gibbs`. Feng's (4.17) applied to `Ψ`, or the identity
   `h(ν) = H_ν(\overline{𝒫} | \overline{𝒫}^-)`, closes it; the Lean layer states the first
   as `feng_entropy_kolmogorov_sinai_bar`. The sentence "we use `h_0(μ) = h(μ)` for every
   `μ ∈ ℳ_σ(Σ)`, without a spectrum or ergodicity assumption" (tex 2088 to 2089) concerns
   measures for which `Σ'` and hence `ξ_0` are not defined; it reads as a convention.

6. `thm:gibbs_tau_omega_positive` (tex 3189 to 3204). The sets `Σ^τ`, `Σ^ω` in the statement
   belong to the equilibrium state `μ`, which the statement does not mention; `μ` is fixed in
   the paragraph before the lemma. The Lean statement takes `μ` and `hdec`.

7. `thm:sigma_tau_omega_positive_eq_measure`. The paragraph before it (tex 2484 to 2486) assumes
   a proximal diagonal generator; the statement assumes a proximal tuple. Read: the proof uses
   ergodicity, full support, `λ_2 < λ_1` and `eq:sigma_tau_omega_positive_eq_measure1`, and no
   normalisation. The display at tex 2543 to 2547 is an almost-everywhere identity whose
   qualifier "for `μ`-almost all `𝐢`" appears only after the next display; it also needs `Σ^τ`
   Borel, which is checked.

8. `thm:partitions_xi1`, `thm:partition_tau_conj`. Read. The proofs use past saturation, the
   transition rule of `Z` and `λ_2 < λ_1` (for `Σ^τ ∩ Σ^ω = ∅`); proximality, rotations and
   ergodicity do not enter the set identities.

9. `thm:conditional_measures_of_a_conditional_measure`, first part. Read. The identity
   `(μ_Ξ)_𝐢^ξ = (μ_𝐢^ξ)_Ξ` holds for every sub-`σ`-algebra of a standard Borel space; the
   hypothesis that `ξ` is a measurable partition and the remark that the kernel is "supported
   on `ξ(𝐢)`" (tex 1875) are needed for the second part only, where `Ξ ∈ \widehat{ξ}` uses the
   symmetry of the partition.

10. `\widehat{ξ}` (tex 1817 to 1819). Checked. The `σ`-algebra of Borel unions of atoms and the
    pull-back `σ`-algebra of the inducing Borel map are equal (`saturated_eq_comap`), so
    "countably generated before completion" is correct as stated.

11. `eq:V_lyapunov` (tex 1659 to 1662) has `lim` where Feng's (4.6) has `lim sup`. On `Σ'` the
    limit exists for every `v`, so the two sets agree there.

Not checked: the citation "Petersen [§3, Theorem 2.3]" for Shannon–McMillan–Breiman; the
numbering of Feng's results in the journal version (the local PDF is the arXiv version); the
proof of `thm:main_extended` for `s ≥ 2` beyond its first step (`neg_lt_entropy_of_two_le`);
the proofs of `thm:conditional_two_ways`, `thm:overline_h1_large` and `thm:SOSC_h2_zero` were
read for their dependencies and show no gap at that level.
