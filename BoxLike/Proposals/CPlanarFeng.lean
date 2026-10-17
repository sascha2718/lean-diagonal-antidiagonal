module

/-
PROPOSAL FOR THE PROJECT OWNER'S REVIEW. This file is not part of the authorised literature
boundary, nothing outside `BoxLike/Proposals/` imports it, and every result in it that takes
`PlanarFengInfoSum` or `PlanarFengLedrappierYoung` is conditional on an unauthorised premise.

`thm:feng_entropy_as_limit` (tex lines 1985 to 1998) and `thm:feng1` (tex lines 2762 to 2775)
are cited from Feng, *Dimension of invariant measures for affine iterated function systems*,
Duke Math. J. 172 (2023), arXiv:1901.01691v2, for every planar self-affine set; the predicates
`FengInfoSum` and `FengLedrappierYoung` of `BoxLike/LiteratureFeng.lean` quantify over box-like
systems only. The two premises below are their transcriptions at the full planar scope, about the
planar systems, partitions and entropies of `BoxLike/Planar/`. Each implies the box-like
predicate (`PlanarFengInfoSum.fengInfoSum`, `PlanarFengLedrappierYoung.fengLedrappierYoung`), so
the box-like predicates are their specialisations.

The library does not need `PlanarFengInfoSum`. Its conclusion is Feng's identity for planar
systems, which the library proves for every invariant `μ` with `λ_2 < λ_1` and `μ(Σ') = 1`
(`PlanarSystem.infoSum_xi` in `BoxLike/Planar/FengIdentity.lean`), and `μ(Σ') = 1` for ergodic `μ`
is the proved planar Oseledets theorem (`PlanarSystem.measure_SigmaPrime_compl_of_ergodic` in
`BoxLike/Planar/OseledetsTheorem.lean`). The planar parts of `thm:feng_entropy_as_limit` and
`thm:feng_entropy_zero` at the article's scope are therefore theorems with no premise
(`feng_entropy_as_limit_general`, `feng_entropy_zero_general` in
`BoxLike/Planar/FengGeneral.lean`), and so is `FengInfoSum` (`fengInfoSum_holds`). The premise
`PlanarFengLedrappierYoung` is needed for the planar clause of `thm:feng1` at the general scope
and awaits authorisation; the headline results use the authorised box-like
`FengLedrappierYoung`. The scalar parts of the three statements concern box-like systems in the
article and use the proved `FengInfoSumBar` and the authorised `FengLedrappierYoungBar`.

* `PlanarFengInfoSum`: Feng, Lemma 4.6, first identity of (4.16), for planar systems.
* `PlanarFengLedrappierYoung`: Feng, Theorems 1.2 and 1.3, for planar systems.
* `PlanarFengInfoSum.fengInfoSum`, `PlanarFengLedrappierYoung.fengLedrappierYoung`: the
  reductions to the authorised box-like predicates.
* `PlanarSystem.feng_entropy_as_limit`, `PlanarSystem.feng_entropy_zero`, `PlanarSystem.feng1`:
  the planar parts of `thm:feng_entropy_as_limit`, `thm:feng_entropy_zero` and `thm:feng1` for a
  planar self-affine system, conditional.
* `planar_feng_entropy_as_limit`, `planar_feng_entropy_zero`, `planar_feng1`: both parts of the
  three statements, with the planar part at the general scope, conditional.
* `planarFengInfoSum_of_fengXi`, `planarFengLedrappierYoung_of_fengXi`: the two premises follow
  from the source statements for Feng's own partitions on any Borel set of full measure inside
  `Σ'` (`BoxLike/Planar/FengPartitions.lean`), with no premise.
-/
public import BoxLike.Planar.FengEntropy
public import BoxLike.Planar.FengPartitions

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

universe u

/-- **Proposed literature premise, not authorised.** Feng, Lemma 4.6, first identity of (4.16),
for planar self-affine systems: for an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and every `i`,
`-log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ}_i)(σ^k 𝐢)` for all `n`, on one set of
full measure. It broadens the authorised `FengInfoSum` from box-like to planar systems
(`PlanarFengInfoSum.fengInfoSum`).

Source. D.-J. Feng, *Dimension of invariant measures for affine iterated function systems*,
Duke Math. J. 172 (2023); compared with arXiv:1901.01691v2 (2 June 2020), Lemma 4.6, first
identity of (4.16), with the construction of Section 4: (4.1) to (4.7), Lemmas 4.1, 4.2, 4.4 and
4.5. The manuscript cites it at tex lines 1980 and 2049 to 2054.

Source hypotheses. An affine IFS `S_j(x) = M_j x + a_j` on `ℝ^d`, not necessarily invertible or
contracting; `m ∈ M_σ(Σ)` on the two-sided full shift, with `S` average contracting with respect
to `m` (Definition 1.1); the set `Σ'` of Section 4, obtained from Feng's Theorem 2.12 for the
cocycle `M(x) = M_{x_{-1}}` over `σ⁻¹` and Proposition 3.1, with `σ(Σ') = Σ'`, `m(Σ') = 1` and
(4.1) to (4.4); assumption (4.7), that `s(x)`, `k_1(x), …, k_{s(x)}(x)` are constant `m`-almost
everywhere on `Σ'`; the partitions `ξ_i(x) = {y ∈ ξ_0(x) : π y - π x ∈ V_x^i}` of `Σ'` with
`V_x^i` given by (4.6); `𝒫 = {[j] ∩ Σ'}`; `i ∈ {0, …, s}`. Ergodicity is not required.

Specialisation. `d = 2`; `M_j = A_j` invertible with `‖A_j‖ < 1`, so `S` is contracting, hence
average contracting for every `m`, and `π` is defined everywhere (`PlanarSystem.proj`); `m = μ`
ergodic, which gives (4.7); `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, so `s = 2`, `k_1 = k_2 = 1`, and Feng's
`λ_i(x)` are the constants `λ_i(𝖠, μ)` almost everywhere (Furstenberg–Kesten, as in
`PlanarOseledets`). Indices `i > 2` repeat `ξ_2`, for which the identity is the case `i = 2`.
Feng's `Σ'` can be taken inside the library's `Σ' = PlanarSystem.SigmaPrime`, the set of all
points with (V1) to (V3): on Feng's set every non-zero vector of `V_x^1 = E_x^2` has backward
rate `λ_2` by (4.1), every other vector has backward rate `λ_1` by (4.1) and
`MatrixTuple.HasPastRate.add_smul`. On such a set Feng's `V_x^i` of (4.6) is the library's
filtration (`MatrixTuple.fengV_eq_filtration`), Feng's atoms are the library's atoms cut down to
it, and the conditional measures agree almost everywhere; the identity for Feng's partitions on
his set implies the one stated here (`planarFengInfoSum_of_fengXi`, proved). Conditional
measures are those of `BoxLike/Conditional.lean`, `condInfo` is `I_μ(𝒫 | \widehat{ξ}_i)` with
`log 0 = 0` on a null set, as for `FengInfoSum`.

Degenerate instances, by hand. One letter with `A = diag(1/2, 1/4)`: the Dirac mass at the
constant sequence is the only invariant probability; `Σ'` is that point, every conditional
measure is the Dirac mass, and both sides vanish. Two letters, all translations zero, a Bernoulli
measure with weights `p_j`: `π = 0`, every `ξ_i` is the partition by the past on `Σ'`, the
conditional measure of `[𝐢|_n]` is `p_{i_0} ⋯ p_{i_{n-1}}` and the right-hand side is
`-∑_k log p_{i_k}`. Scaled rotations: `λ_1 = λ_2`, the statement is silent. The identity would
fail for a non-Bernoulli `μ` if `μ(Σ') = 0`, since the partitions are then trivial modulo `μ`;
`μ(Σ') = 1` is Oseledets' theorem, inside the source's construction, and is proved for box-like
tuples (`System.measure_toPlanar_SigmaPrime_compl`).

Used by: `PlanarFengInfoSum.fengInfoSum`, `PlanarSystem.feng_entropy_as_limit`,
`PlanarSystem.feng_entropy_zero`, `planar_feng_entropy_as_limit`, `planar_feng_entropy_zero`. -/
def PlanarFengInfoSum : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
    MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
    ∀ i : ℕ, ∀ᵐ x ∂μ, ∀ n : ℕ,
      -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) =
        ∑ k ∈ Finset.range n, condInfo μ (P.xi μ i) (shift k x)

/-- **Proposed literature premise, not authorised.** `thm:feng1`, first part,
`eq:feng1_1`, for planar self-affine systems; Feng, Theorems 1.2 and 1.3, for `d = 2` and simple
Lyapunov spectrum: if `μ` is ergodic with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `π_*μ` is
exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`. It broadens the
authorised `FengLedrappierYoung` from box-like to planar systems
(`PlanarFengLedrappierYoung.fengLedrappierYoung`).

Source. D.-J. Feng, Duke Math. J. 172 (2023); compared with arXiv:1901.01691v2 (2 June 2020),
Theorem 1.2 (ii) (exact-dimensionality) and Theorem 1.3, formula (1.6), with the entropies
`h_i = H_m(𝒫 | \widehat{ξ}_i)` of (1.5). The manuscript cites them at tex lines 2755 to 2775.

Source hypotheses. An affine IFS on `ℝ^d`, not necessarily invertible or contracting; an ergodic
`m ∈ M_σ(Σ)` on the two-sided full shift with respect to which `S` is average contracting; the
distinct Lyapunov exponents `λ_1 > ⋯ > λ_s` with multiplicities `k_i` of the cocycle of
Section 1.2; local dimensions with closed Euclidean balls.

Specialisation. As for `PlanarFengInfoSum`: `d = 2`, invertible contractions, `m = μ` ergodic,
`λ_2 < λ_1` so that `s = 2` and `k_1 = k_2 = 1`; (1.6) is then
`(h_1 - h_0) / λ_1 + (h_2 - h_1) / λ_2`. Feng's entropies for his partitions on his `Σ'`, taken
inside the library's `Σ'`, are the library's (`PlanarSystem.condEntropy_fengXi_eq`), so the
source statement implies the one stated here (`planarFengLedrappierYoung_of_fengXi`, proved).
`IsExactDim` on `ℝ × ℝ` uses closed balls of the supremum norm; they lie between the Euclidean
balls of radii `r` and `√2 r`, which gives the same pointwise dimension. The order of the
matrix products (`A_{𝐢|_n} = A_{i_0} ⋯ A_{i_{n-1}}` for `λ_i`, `A_{i_{-n}} ⋯ A_{i_{-1}}` for the
filtration) and the signs of the formula agree with Feng's (1.3), Section 1.2 and (1.6).

Degenerate instances, by hand. One letter with `A = diag(1/2, 1/4)`: `π_*μ` is a Dirac mass, of
pointwise dimension `0`, and all `h_i` vanish since `𝒫` has one atom. Two letters, all
translations zero, Bernoulli `μ`: `π_*μ = δ_0` and `h_0 = h_1 = h_2`, so both sides vanish.
Scaled rotations: `λ_1 = λ_2`, the statement is silent.

Used by: `PlanarFengLedrappierYoung.fengLedrappierYoung`, `PlanarSystem.feng1`, `planar_feng1`. -/
def PlanarFengLedrappierYoung : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
    MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
    IsExactDim (μ.map P.proj)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
        (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)

/-- The planar premise `PlanarFengInfoSum` implies the authorised box-like predicate
`FengInfoSum`: apply it to the planar system `S.toPlanar` of a box-like system, whose partitions
are the box-like partitions (`System.toPlanar_xi`) and whose exponents are those of `S`. -/
theorem PlanarFengInfoSum.fengInfoSum (h : PlanarFengInfoSum.{u}) : FengInfoSum.{u} := by
  intro ι _ _ _ S μ _ hinv herg hlt i
  have := h S.toPlanar μ hinv herg hlt i
  rwa [S.toPlanar_xi μ hlt] at this

/-- The planar premise `PlanarFengLedrappierYoung` implies the authorised box-like predicate
`FengLedrappierYoung`: apply it to the planar system `S.toPlanar`, whose projection, entropies
and exponents are those of `S` (`System.toPlanar_proj`, `System.toPlanar_dimEntropy`). -/
theorem PlanarFengLedrappierYoung.fengLedrappierYoung (h : PlanarFengLedrappierYoung.{u}) :
    FengLedrappierYoung.{u} := by
  intro ι _ _ _ S μ _ hinv herg hlt
  have := h S.toPlanar μ hinv herg hlt
  rwa [S.toPlanar_proj, S.toPlanar_dimEntropy μ hlt, S.toPlanar_dimEntropy μ hlt,
    S.toPlanar_dimEntropy μ hlt, S.toPlanar_lyapunov₁, S.toPlanar_lyapunov₂] at this

/-- The source form of Feng, Lemma 4.6, (4.16) implies `PlanarFengInfoSum`, with no premise: if
for every planar system and every ergodic `μ` with `λ_2 < λ_1` the identity holds for Feng's
partitions `PlanarSystem.fengXi` on some Borel set `D ⊆ Σ'` of full measure (his `Σ'`), then it
holds for the library's partitions. -/
theorem planarFengInfoSum_of_fengXi
    (h : ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      ∃ D : Set (ℤ → ι), MeasurableSet D ∧ D ⊆ P.SigmaPrime μ ∧ μ Dᶜ = 0 ∧
        ∀ i : ℕ, ∀ᵐ x ∂μ, ∀ n : ℕ,
          -Real.log ((condMeas μ (P.fengXi μ D i) x).real (cylinder (block n x))) =
            ∑ k ∈ Finset.range n, condInfo μ (P.fengXi μ D i) (shift k x)) :
    PlanarFengInfoSum.{u} := by
  intro ι _ _ _ P μ _ hinv herg hlt i
  obtain ⟨D, hD, hDsub, hfull, hsum⟩ := h P μ hinv herg hlt
  exact (P.infoSum_fengXi_iff μ hinv hlt hD hDsub hfull i).1 (hsum i)

/-- The source form of Feng, Theorems 1.2 and 1.3, implies `PlanarFengLedrappierYoung`, with no
premise: if for every planar system and every ergodic `μ` with `λ_2 < λ_1` the formula holds with
Feng's entropies `H_μ(𝒫 | \widehat{ξ}_i)` for his partitions on some Borel set `D ⊆ Σ'` of full
measure, then it holds with the library's entropies. -/
theorem planarFengLedrappierYoung_of_fengXi
    (h : ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      ∃ D : Set (ℤ → ι), MeasurableSet D ∧ D ⊆ P.SigmaPrime μ ∧ μ Dᶜ = 0 ∧
        IsExactDim (μ.map P.proj)
          ((condEntropy μ (P.fengXi μ D 1) - condEntropy μ (P.fengXi μ D 0)) / P.lyapunov₁ μ +
            (condEntropy μ (P.fengXi μ D 2) - condEntropy μ (P.fengXi μ D 1)) /
              P.lyapunov₂ μ)) :
    PlanarFengLedrappierYoung.{u} := by
  intro ι _ _ _ P μ _ hinv herg hlt
  obtain ⟨D, hD, hDsub, hfull, hdim⟩ := h P μ hinv herg hlt
  simpa only [P.condEntropy_fengXi_eq μ hlt hD hDsub hfull] using hdim

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- Conditional on the unauthorised premise `PlanarFengInfoSum`. `thm:feng_entropy_as_limit`,
planar part, for a planar self-affine set: for ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and each
`i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = -lim_n n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢`. -/
theorem feng_entropy_as_limit (hfi : PlanarFengInfoSum.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (i : ℕ) (_hi : i ≤ 2) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (P.dimEntropyAt μ i x)) :=
  P.feng_entropy_as_limit_of_infoSum μ hinv (hfi P μ hinv herg hlt i)

/-- Conditional on the unauthorised premise `PlanarFengInfoSum`. `thm:feng_entropy_zero`,
planar part, for a planar self-affine set: for ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and each
`i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = 0 ↔ μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost every `𝐢`, by the article's
proof in `PlanarSystem.feng_entropy_zero_of_infoSum`. -/
theorem feng_entropy_zero (hfi : PlanarFengInfoSum.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (i : ℕ) (_hi : i ≤ 2) :
    ∀ᵐ x ∂μ, P.dimEntropyAt μ i x = 0 ↔ condMeas μ (P.xi μ i) x = Measure.dirac x :=
  P.feng_entropy_zero_of_infoSum μ hinv herg hlt (hfi P μ hinv herg hlt i)

/-- Conditional on the unauthorised premise `PlanarFengLedrappierYoung`. `thm:feng1`, first
part, `eq:feng1_1`, for a planar self-affine set: for ergodic `μ` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, `π_*μ` is exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`. -/
theorem feng1 (hly : PlanarFengLedrappierYoung.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    IsExactDim (μ.map P.proj)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
        (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ) :=
  hly P μ hinv herg hlt

end PlanarSystem

/-- Conditional on the unauthorised premise `PlanarFengInfoSum`. `thm:feng_entropy_as_limit`,
both parts, at the article's scope. Planar part: for every planar self-affine set, every ergodic
`μ` with `λ_2 < λ_1` and each `i ∈ {0, 1, 2}`,
`h_i(μ, 𝐢) = -lim_n n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢`. Scalar part: for
every proximal box-like self-affine set with rotations, every invariant `ν` on `Σ_Z`, ergodic or
not, and each `i ∈ {0, 1}`,
`\overline{h}_i(ν, 𝐢) = -lim_n n⁻¹ log ν_𝐢^{\overline{ξ}_i}(\overline{𝒫}_0^{n-1}(𝐢))` for
`ν`-almost every `𝐢`; hypothesis `FengInfoSumBar`. -/
theorem planar_feng_entropy_as_limit (hfi : PlanarFengInfoSum.{u})
    (hfib : FengInfoSumBar.{u}) :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      ∀ i : ℕ, i ≤ 2 → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
        atTop (𝓝 (P.dimEntropyAt μ i x))) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 →
      ∀ i : ℕ, i ≤ 1 → ∀ᵐ y ∂ν, Tendsto
        (fun n : ℕ => -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) / n)
        atTop (𝓝 (S.dimEntropyBarAt ν i y))) :=
  ⟨fun P μ _ hinv herg hlt i hi => P.feng_entropy_as_limit hfi μ hinv herg hlt i hi,
    fun S hrot hprox ν _ hinv hsupp i _ =>
      S.feng_entropy_as_limit_bar hfib hrot hprox ν hinv hsupp i⟩

/-- Conditional on the unauthorised premise `PlanarFengInfoSum`. `thm:feng_entropy_zero`, both
parts, at the article's scope. Planar part: for every planar self-affine set, every ergodic `μ`
with `λ_2 < λ_1` and each `i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = 0 ↔ μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost every
`𝐢`. Scalar part: for every proximal box-like self-affine set with rotations, every invariant
`ν` on `Σ_Z`, ergodic or not, and each `i ∈ {0, 1}`,
`\overline{h}_i(ν, 𝐢) = 0 ↔ ν_𝐢^{\overline{ξ}_i} = δ_𝐢` for `ν`-almost every `𝐢`; hypothesis
`FengInfoSumBar`. -/
theorem planar_feng_entropy_zero (hfi : PlanarFengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      ∀ i : ℕ, i ≤ 2 → ∀ᵐ x ∂μ,
        P.dimEntropyAt μ i x = 0 ↔ condMeas μ (P.xi μ i) x = Measure.dirac x) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 →
      ∀ i : ℕ, i ≤ 1 → ∀ᵐ y ∂ν,
        S.dimEntropyBarAt ν i y = 0 ↔ condMeas ν (S.xiBar i) y = Measure.dirac y) :=
  ⟨fun P μ _ hinv herg hlt i hi => P.feng_entropy_zero hfi μ hinv herg hlt i hi,
    fun S hrot hprox ν _ hinv hsupp i _ =>
      S.feng_entropy_zero_bar hfib hrot hprox ν hinv hsupp i⟩

/-- Conditional on the unauthorised premise `PlanarFengLedrappierYoung`. `thm:feng1`, both
parts, at the article's scope. First part: for every planar self-affine set and every ergodic
`μ` with `λ_2 < λ_1`, `π_*μ` is exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`. Second part: for
every proximal box-like self-affine set with rotations and every ergodic `ν` on `Σ_Z`,
`\overline{π}_*ν` is exact-dimensional with
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`; this is the
authorised `FengLedrappierYoungBar`. -/
theorem planar_feng1 (hly : PlanarFengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      IsExactDim (μ.map P.proj)
        ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
          (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → Ergodic (shift 1) ν → ν (subshift S.o)ᶜ = 0 →
      IsExactDim (ν.map S.projBar)
        ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν)) :=
  ⟨fun P μ _ hinv herg hlt => P.feng1 hly μ hinv herg hlt, hlyb⟩

end BoxLike
