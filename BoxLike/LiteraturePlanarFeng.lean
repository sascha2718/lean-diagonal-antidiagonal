module

/-
The result of D.-J. Feng, *Dimension of invariant measures for affine iterated function systems*,
Duke Math. J. 172 (2023), arXiv:1901.01691, that the article cites in `thm:feng1` for every
planar self-affine set, as a `Prop`-valued definition about the planar systems, partitions and
entropies of `BoxLike/Planar/`. A result that uses it takes it as a hypothesis. The library
proves it (`planarFengLedrappierYoung_holds` in `BoxLike/FengLedrappierYoung.lean`), along Feng's
Sections 4 to 6 for `d = 2`. `docs/correspondence.md`, "Fidelity boundary", states the rules; the
project owner authorised this statement. The box-like predicate `FengLedrappierYoung` of `BoxLike/LiteratureFeng.lean`
is its specialisation.

* `PlanarFengLedrappierYoung`: Feng, Theorems 1.2 and 1.3, for planar systems.
* `PlanarFengLedrappierYoung.fengLedrappierYoung`: the reduction to `FengLedrappierYoung`.
* `planarFengLedrappierYoung_of_fengXi`: the statement follows from the source statement for
  Feng's own partitions on any Borel set of full measure inside `Σ'`, with no premise.
-/
public import BoxLike.Planar.FengEntropy
public import BoxLike.Planar.FengPartitions

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- `thm:feng1`, first part,
`eq:feng1_1`, for planar self-affine systems; Feng, Theorems 1.2 and 1.3, for `d = 2` and simple
Lyapunov spectrum: if `μ` is ergodic with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `π_*μ` is
exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`. This is the
planar case of the source; the box-like `FengLedrappierYoung` is its specialisation
(`PlanarFengLedrappierYoung.fengLedrappierYoung`).

Source. D.-J. Feng, Duke Math. J. 172 (2023); compared with arXiv:1901.01691v2 (2 June 2020),
Theorem 1.2 (ii) (exact-dimensionality) and Theorem 1.3, formula (1.6), with the entropies
`h_i = H_m(𝒫 | \widehat{ξ}_i)` of (1.5). The manuscript cites them at tex lines 2704 to 2724.

Source hypotheses. An affine IFS on `ℝ^d`, not necessarily invertible or contracting; an ergodic
`m ∈ M_σ(Σ)` on the two-sided full shift with respect to which `S` is average contracting; the
distinct Lyapunov exponents `λ_1 > ⋯ > λ_s` with multiplicities `k_i` of the cocycle of
Section 1.2; local dimensions with closed Euclidean balls.

Specialisation. `d = 2`, invertible contractions, `m = μ` ergodic,
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

Used by: `PlanarFengLedrappierYoung.fengLedrappierYoung`, `PlanarSystem.feng1`, `planar_feng1`.
Proved: `planarFengLedrappierYoung_holds` (`BoxLike/FengLedrappierYoung.lean`). -/
def PlanarFengLedrappierYoung : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
    MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
    IsExactDim (μ.map P.proj)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
        (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)

/-- The planar premise `PlanarFengLedrappierYoung` implies the authorised box-like predicate
`FengLedrappierYoung`: apply it to the planar system `S.toPlanar`, whose projection, entropies
and exponents are those of `S` (`System.toPlanar_proj`, `System.toPlanar_dimEntropy`). -/
theorem PlanarFengLedrappierYoung.fengLedrappierYoung (h : PlanarFengLedrappierYoung.{u}) :
    FengLedrappierYoung.{u} := by
  intro ι _ _ _ S μ _ hinv herg hlt
  have := h S.toPlanar μ hinv herg hlt
  rwa [S.toPlanar_proj, S.toPlanar_dimEntropy μ hlt, S.toPlanar_dimEntropy μ hlt,
    S.toPlanar_dimEntropy μ hlt, S.toPlanar_lyapunov₁, S.toPlanar_lyapunov₂] at this

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

end BoxLike
