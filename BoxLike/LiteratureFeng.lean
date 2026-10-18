module

/-
The results of D.-J. Feng, *Dimension of invariant measures for affine iterated function
systems*, Duke Math. J. 172 (2023), arXiv:1901.01691, which the article cites without proof in
`sec:entropies` and `sec:ledrappier_young_formula`, as `Prop`-valued definitions. A result that
uses one of them takes it as a hypothesis. `BoxLike/Literature.lean` holds the citations that
need only the symbolic and thermodynamic vocabulary; the ones here need the partitions `ξ_i`,
`\overline{ξ}_i`, the conditional measures and the entropies `h_i`, `\overline{h}_i` of
`BoxLike/DimPartitions.lean`. `docs/correspondence.md`, "Fidelity boundary", states the rules.

Feng's set `Σ'` is an invariant Borel set of full measure on which his properties (4.1) to
(4.4) hold, some of which concern forward time; it can be taken inside the article's box-like
set `Σ'`, which is the one used here, with each partition extended to the whole shift by one
null atom. Feng's atom at a point of his set is the box-like atom cut down to his set, so the
atoms differ pointwise in general. The conditional measures agree almost everywhere
(`System.condMeas_fengXi_ae_eq` of `BoxLike/OseledetsBridge.lean`), hence so do the
conditional informations and the entropies, and the information-sum identity holds for one
family of partitions exactly when it holds for the other (`System.infoSum_fengXi_iff`). The
statements were compared with the arXiv version (v2) of the source on 2026-09-20.

* `FengInfoSum`, `FengInfoSumBar`: Feng, Lemma 4.6, first identity of (4.16), behind
  `thm:feng_entropy_as_limit` and `thm:feng_entropy_zero`. Both are theorems of the library
  (`fengInfoSum_holds` in `BoxLike/FengIdentity.lean`, `fengInfoSumBar_holds` in
  `BoxLike/FengIdentityBar.lean`); the results that state them as hypotheses receive these
  proofs, and no headline statement takes them.
* `FengLedrappierYoung`, `FengLedrappierYoungBar`: `thm:feng1`, from Feng, Theorems 1.2
  and 1.3.
-/
public import BoxLike.DimPartitions

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- Feng, Lemma 4.6, first identity of (4.16), for the planar partitions:
`-log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ}_i)(σ^k 𝐢)` for all `n`, on one set of
full measure. The proof of `thm:feng_entropy_zero` uses it. Hypotheses as in
`thm:feng_entropy_as_limit`. The library proves it along Feng's Lemmas 4.4 and 4.5
(`fengInfoSum_holds`, `BoxLike/FengIdentity.lean`). -/
def FengInfoSum : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    Ergodic (shift 1) μ → S.lyapunov₂ μ < S.lyapunov₁ μ → ∀ i : ℕ,
    ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (S.xi μ i) x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ (S.xi μ i) (shift k x)

/-- Feng, Lemma 4.6, first identity of (4.16), for the projective system and an
invariant measure `ν` on `Σ_Z`, ergodic or not; the article checks Feng's constant-multiplicity
hypothesis (4.7) in `sec:entropies`, tex lines 1921 to 1924. The library proves it, with neither
that hypothesis nor rotations nor proximality (`fengInfoSumBar_holds`,
`BoxLike/FengIdentityBar.lean`). -/
def FengInfoSumBar : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.Proximal → ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 → ∀ i : ℕ,
    ∀ᵐ y ∂ν, ∀ n : ℕ, -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) =
      ∑ k ∈ Finset.range n, condInfo ν (S.xiBar i) (shift k y)

/-- `thm:feng1`, first part, `eq:feng1_1`; Feng, Theorems 1.2 and 1.3, for `d = 2`
and simple Lyapunov spectrum: if `μ` is ergodic with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `π_*μ` is
exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`.
Feng works with closed Euclidean balls; `IsExactDim` on `ℝ × ℝ` uses closed balls of the
supremum norm, which gives the same pointwise dimension. -/
def FengLedrappierYoung : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    Ergodic (shift 1) μ → S.lyapunov₂ μ < S.lyapunov₁ μ →
    IsExactDim (μ.map S.proj)
      ((S.dimEntropy μ 1 - S.dimEntropy μ 0) / S.lyapunov₁ μ +
        (S.dimEntropy μ 2 - S.dimEntropy μ 1) / S.lyapunov₂ μ)

/-- `thm:feng1`, second part; Feng, Theorems 1.2 and 1.3, for the self-similar system
`Ψ` on `ℝ`: if `ν` is an ergodic invariant measure on `Σ_Z`, then `\overline{π}_*ν` is
exact-dimensional with
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`. -/
def FengLedrappierYoungBar : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.Proximal → ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    MeasurePreserving (shift 1) ν ν → Ergodic (shift 1) ν → ν (subshift S.o)ᶜ = 0 →
    IsExactDim (ν.map S.projBar)
      ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν)

end BoxLike
