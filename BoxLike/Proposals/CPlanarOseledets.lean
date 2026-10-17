module

/-
PROPOSAL FOR THE PROJECT OWNER'S REVIEW, NOT NEEDED BY THE LIBRARY. This file is not part of the
authorised literature boundary, nothing outside `BoxLike/Proposals/` imports it, and every result
in it is conditional on the unauthorised premise `PlanarOseledets`. The library does not need the
premise: its conclusion is a theorem, Oseledets' theorem for invertible planar cocycles
(`MatrixTuple.measure_regularSet_compl_of_ergodic` in `BoxLike/Planar/OseledetsTheorem.lean`,
from Kingman's subadditive ergodic theorem of `BoxLike/Kingman.lean` and the Furstenberg–Kesten
limits of `BoxLike/FurstenbergKesten.lean`), and the conditional results below have unconditional
counterparts there (`PlanarSystem.measure_SigmaPrime_compl_of_ergodic`,
`PlanarSystem.oseledetsSetOfErgodic`, `PlanarSystem.feng_entropy_kolmogorov_sinai_general`,
`PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_ergodic`). The file records the proposal and its
consistency checks.

`sec:lyapunov_exponents` (tex lines 1620 to 1642) asserts, citing Oseledets' multiplicative
ergodic theorem (Oseledec 1968) and Froyland–Lloyd–Quas, Theorem 4.1, that for an ergodic
`μ ∈ M_σ(Σ)` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` there is an invariant Borel set `Σ'` of full measure
on which the Oseledets properties (V1) to (V3) hold. `BoxLike/Planar/Oseledets.lean` defines
`Σ'` as the set of all points at which (V1) to (V3) hold, proves that it is Borel, invariant and
saturated with respect to the past, and `BoxLike/Planar/Specialisation.lean` proves that it has
full measure for box-like tuples (`System.measure_toPlanar_SigmaPrime_compl`, from Birkhoff's
theorem). For an arbitrary tuple of invertible matrices the full measure is the content of
Oseledets' theorem, which Mathlib does not contain; the library proves it in
`BoxLike/Planar/OseledetsTheorem.lean`.

* `PlanarOseledets`: the proposed premise.
* `PlanarSystem.measure_SigmaPrime_compl`: `μ(Σ') = 1`, conditional on `PlanarOseledets`.
* `PlanarSystem.dimEntropy_zero_eq_entropy`: `h_0(μ) = h(μ)` (tex lines 2024 to 2026) at the
  general planar scope, conditional on `PlanarOseledets`.
* `planarOseledets_boxLike`: the conclusion of `PlanarOseledets` holds for every box-like
  tuple, without any premise; this is the consistency check of the proposal on the scope of the
  headline results.
* `planarOseledets_iff_nonempty_oseledetsSet`: `PlanarOseledets` is the existence of a choice
  of `Σ'` and of the Oseledets filtration (`MatrixTuple.OseledetsSet` of
  `BoxLike/OseledetsFiltration.lean`) for every invertible tuple and ergodic `μ` with
  `λ_2 < λ_1`.
* `PlanarSystem.oseledetsSet`: such a choice for a planar system, conditional.
* `PlanarSystem.feng_entropy_kolmogorov_sinai`, `PlanarSystem.feng_entropy_kolmogorov_sinai'`,
  `PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_planarOseledets`:
  `thm:feng_entropy_kolmogorov_sinai` and `h_0(μ) = h(μ)` at the general planar scope,
  conditional on `PlanarOseledets`.
-/
public import BoxLike.Planar.CylinderEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

universe u

/-- **Proposed literature premise, not authorised.** Oseledets' multiplicative ergodic theorem
for planar matrix cocycles, in the form `sec:lyapunov_exponents` uses it.

Source. V. I. Oseledec, *A multiplicative ergodic theorem. Lyapunov characteristic numbers for
dynamical systems*, Trudy Moskov. Mat. Obšč. 19 (1968), 179–210, cited at tex line 1620; the
form with a splitting and the growth characterisation `eq:V_lyapunov` is G. Froyland,
S. Lloyd and A. Quas, *Coherent structures and isolated spectrum for Perron–Frobenius cocycles*,
Ergodic Theory Dynam. Systems 30 (2010), Theorem 4.1, cited at tex line 1642, which is also the
form Feng uses (D.-J. Feng, Duke Math. J. 172 (2023), arXiv:1901.01691v2, Theorem 2.12 and
Remark 2.13).

Source hypotheses. An invertible measure-preserving transformation `T` of a Lebesgue space
`(X, m)` and a measurable `M : X → Mat_d(ℝ)` with `∫ log⁺ ‖M‖ dm < ∞`; `m` ergodic in
Froyland–Lloyd–Quas, any `m` in Feng's Remark 2.13. Source conclusion: an invariant set `X'` of
full measure on which there are exponents `λ_1(x) > ⋯ > λ_{s(x)}(x)` and a splitting
`ℝ^d = E_x^1 ⊕ ⋯ ⊕ E_x^{s(x)}` with `M(x) E_x^i = E_{T x}^i` for invertible `M` and
`n⁻¹ log |M(T^{n-1} x) ⋯ M(x) v| → λ_i(x)` for `v ∈ E_x^i ∖ {0}`.

Specialisation. `X = Σ = ι^ℤ` with the product of the discrete `σ`-algebras, a standard Borel
space; `T = σ⁻¹`; `M(𝐢) = A_{i_{-1}}`, so that `M(T^{n-1} 𝐢) ⋯ M(𝐢) = A_{i_{-n}} ⋯ A_{i_{-1}}`;
`d = 2`; `log⁺ ‖M‖` is bounded since the alphabet is finite; `m = μ` ergodic. The exponents of the
cocycle over `σ⁻¹` are `λ_1(𝖠, μ)` and `λ_2(𝖠, μ)`: by invariance
`∫ log ‖A_{i_{-n}} ⋯ A_{i_{-1}}‖ dμ = ∫ log ‖A_{i_0} ⋯ A_{i_{n-1}}‖ dμ`, and the same for the
determinant, so the top exponent and the sum of the exponents of Furstenberg–Kesten agree.
Since `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, the spectrum is simple, `s = 2`; with `V_𝐢^1 = E_𝐢^2`, every
`v ∈ V_𝐢^1 ∖ {0}` has backward rate `λ_2` and every `v ∉ V_𝐢^1` has backward rate `λ_1`
(`MatrixTuple.HasPastRate.add_smul`), which is `MatrixTuple.IsRegular`. The set of regular points
contains the source's `X'`, hence has full measure. Norms: the source's norm is arbitrary; the
library's supremum norm on vectors gives the same rates.

Degenerate instances, by hand. One letter with `A = diag(1/2, 1/4)`: the only invariant
probability is the Dirac mass at the constant sequence, `λ_1 = log (1/2) > λ_2 = log (1/4)`, and
the constant sequence is regular with slow line the `y`-axis. One letter with a scaled rotation,
or a Jordan block `[[1/2, 1/2], [0, 1/2]]`: `λ_1 = λ_2` and the statement is silent. A singular
matrix is excluded by `det A_i ≠ 0`. The empty alphabet carries no probability measure. The
statement asks nothing of measures with `λ_1 = λ_2`, for which `Σ'` in this form may be empty.

Scope. Matrices only: no contraction, no translation. Used by, in this file:
`PlanarSystem.measure_SigmaPrime_compl`, `PlanarSystem.dimEntropy_zero_eq_entropy`,
`PlanarSystem.oseledetsSet`, `PlanarSystem.feng_entropy_kolmogorov_sinai`,
`PlanarSystem.feng_entropy_kolmogorov_sinai'` and
`PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_planarOseledets`. It is equivalent to the existence
of a `MatrixTuple.OseledetsSet` (`planarOseledets_iff_nonempty_oseledetsSet`). For box-like
tuples the conclusion is a theorem (`planarOseledets_boxLike`). -/
def PlanarOseledets : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ), (∀ i, (A i).det ≠ 0) →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    Ergodic (shift 1) μ → MatrixTuple.lyapunov₂ A μ < MatrixTuple.lyapunov₁ A μ →
    μ (MatrixTuple.regularSet A (MatrixTuple.lyapunov₁ A μ) (MatrixTuple.lyapunov₂ A μ))ᶜ = 0

/-- The consistency check of `PlanarOseledets` on the scope of the headline results: its
conclusion holds, with no premise, for the linear parts of every box-like system
(`System.measure_toPlanar_SigmaPrime_compl`). -/
theorem planarOseledets_boxLike {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : MatrixTuple.lyapunov₂ S.mat μ < MatrixTuple.lyapunov₁ S.mat μ) :
    μ (MatrixTuple.regularSet S.mat (MatrixTuple.lyapunov₁ S.mat μ)
      (MatrixTuple.lyapunov₂ S.mat μ))ᶜ = 0 :=
  S.measure_toPlanar_SigmaPrime_compl μ hinv herg hlt

/-- `PlanarOseledets` is the statement that a choice of `Σ'` and of the Oseledets filtration in
the sense of `MatrixTuple.OseledetsSet` (`BoxLike/OseledetsFiltration.lean`), the form in which
`sec:lyapunov_exponents` (tex lines 1620 to 1642) takes Oseledets' theorem, exists for every
invertible planar tuple and every ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem planarOseledets_iff_nonempty_oseledetsSet :
    PlanarOseledets.{u} ↔
      ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
        (A : ι → Matrix (Fin 2) (Fin 2) ℝ), (∀ i, (A i).det ≠ 0) →
        ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
        Ergodic (shift 1) μ → MatrixTuple.lyapunov₂ A μ < MatrixTuple.lyapunov₁ A μ →
        Nonempty (MatrixTuple.OseledetsSet A μ) := by
  constructor
  · intro h ι _ _ _ A hA μ _ hinv herg hlt
    exact (MatrixTuple.nonempty_oseledetsSet_iff hA hlt).2 (h A hA μ hinv herg hlt)
  · intro h ι _ _ _ A hA μ _ hinv herg hlt
    exact (MatrixTuple.nonempty_oseledetsSet_iff hA hlt).1 (h A hA μ hinv herg hlt)

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- Conditional on the unauthorised premise `PlanarOseledets`: a choice of `Σ'` and of the
Oseledets filtration in the sense of `MatrixTuple.OseledetsSet` for a planar self-affine system and
an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, namely the set of regular points with the filtration
`MatrixTuple.regularV`. -/
noncomputable def oseledetsSet (hos : PlanarOseledets.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    MatrixTuple.OseledetsSet P.mat μ :=
  MatrixTuple.regularOseledetsSet P.mat μ P.det_ne_zero hlt
    (hos P.mat P.det_ne_zero μ hinv herg hlt)

/-- Conditional on the unauthorised premise `PlanarOseledets`. `thm:feng_entropy_kolmogorov_sinai`
for a planar self-affine set, in the form of the article: if `μ` is ergodic with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `h_0(μ, 𝐢) = -lim_n n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` for `μ`-almost every
`𝐢 ∈ Σ'`, with the unconditional masses of the cylinders. -/
theorem feng_entropy_kolmogorov_sinai (hos : PlanarOseledets.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, x ∈ P.SigmaPrime μ →
      Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
        (𝓝 (P.dimEntropyAt μ 0 x)) :=
  P.feng_entropy_kolmogorov_sinai_of_oseledetsSet μ
    (P.oseledetsSet hos μ herg.toMeasurePreserving herg hlt) herg hlt

/-- Conditional on the unauthorised premise `PlanarOseledets`. `thm:feng_entropy_kolmogorov_sinai`
for a planar self-affine set on all of `Σ`: the limit holds for `μ`-almost every `𝐢`. -/
theorem feng_entropy_kolmogorov_sinai' (hos : PlanarOseledets.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (P.dimEntropyAt μ 0 x)) :=
  P.tendsto_neg_log_cylinder_dimEntropyAt μ herg.toMeasurePreserving hlt
    (hos P.mat P.det_ne_zero μ herg.toMeasurePreserving herg hlt)

/-- Conditional on the unauthorised premise `PlanarOseledets`: `h_0(μ) = h(μ)` with the
Kolmogorov–Sinai entropy of tex lines 2000 to 2007, for an ergodic `μ` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:entropies`, tex lines 2024 to 2026), for a planar self-affine
system. -/
theorem dimEntropy_zero_eq_ksEntropy_of_planarOseledets (hos : PlanarOseledets.{u})
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    P.dimEntropy μ 0 = ksEntropy μ (shift 1) :=
  P.dimEntropy_zero_eq_ksEntropy μ hinv hlt (hos P.mat P.det_ne_zero μ hinv herg hlt)

/-- Conditional on the unauthorised premise `PlanarOseledets`: `μ(Σ') = 1` for an ergodic `μ`
with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:lyapunov_exponents`, tex lines 1633 to 1635). -/
theorem measure_SigmaPrime_compl (hos : PlanarOseledets.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    μ (P.SigmaPrime μ)ᶜ = 0 :=
  hos P.mat P.det_ne_zero μ hinv herg hlt

/-- Conditional on the unauthorised premise `PlanarOseledets`: `h_0(μ) = h(μ)`, the
Kolmogorov–Sinai entropy, for an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:entropies`, tex
lines 2087 to 2090), for a planar self-affine system. -/
theorem dimEntropy_zero_eq_entropy (hos : PlanarOseledets.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    P.dimEntropy μ 0 = entropy μ :=
  P.dimEntropy_zero_eq_entropy' μ hinv hlt (P.measure_SigmaPrime_compl hos μ hinv herg hlt)

end PlanarSystem

end BoxLike
