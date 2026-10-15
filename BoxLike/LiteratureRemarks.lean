module

/-
Literature theorems behind results off the main line of the article, as `Prop`-valued
definitions; a result that uses one of them takes it as a hypothesis. The four main results
`thm:main1`, `thm:main2`, `thm:eq_state_proj_dim` and `thm:main_extended` do not depend on this
module. The rules of `docs/correspondence.md`, "Fidelity boundary", apply.

Standing conventions: measures on `Σ = ℤ → ι` and on `Σ_Z ⊆ (ι × ZMod 2)^ℤ` are Borel
probability measures, invariant under the left shift `shift 1`; the alphabet `ι` is finite with
the discrete `σ`-algebra.

* `FengHuExactDim`: exact-dimensionality of the projections of ergodic measures under the
  self-similar system `Ψ`, without separation, from Feng–Hu, Comm. Pure Appl. Math. 62 (2009),
  Theorem 2.8. The article uses it in `sec:dimension_of_projections`.
* `FengKaenmakiUnique`: the uniqueness part of `thm:irred_eq_state`, from Feng–Käenmäki,
  Discrete Contin. Dyn. Syst. 30 (2011), Proposition 1.2, applied with `q = s` for
  `0 < s ≤ 1` and to a rescaled tuple with `q = 2 - s` for `1 < s < 2`.

The statements were compared with the sources on 2026-09-21 (arXiv:1002.2036v1 and the journal
version of Feng–Hu, arXiv:1009.3129v1 and the journal version of Feng–Käenmäki); `docs/correspondence.md`,
"Fidelity boundary", records the reductions.

Each statement quantifies over every finite alphabet `ι : Type u` with the discrete
`σ`-algebra, as in `BoxLike/Literature.lean`.
-/
public import BoxLike.MeasureDim
public import BoxLike.Proximal
public import BoxLike.Thermodynamic

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- Feng–Hu, Theorem 2.8, for the projective system `Ψ`: if `ν` is an ergodic shift-invariant
probability measure, then `\overline{π}_*ν` is exact-dimensional. The source treats a `C^1`
iterated function system that is `m`-conformal for the invariant measure `m`; the maps of `Ψ`
are similarities of the line, so `Ψ` is weakly conformal and hence `m`-conformal for every `m`.
No separation condition is assumed, the maps need not be distinct, and the measure need not be
carried by `Σ_Z`. The source works on the one-sided shift with closed balls; `\overline{π}`
depends on the non-negative coordinates only, and the measure obtained by forgetting the
negative coordinates is invariant and ergodic. -/
def FengHuExactDim : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν], Ergodic (shift 1) ν →
    ∃ d : ℝ, IsExactDim (ν.map S.projBar) d

/-- The uniqueness part of `thm:irred_eq_state`. Feng–Käenmäki, Proposition 1.2: if a tuple
of real `d × d` matrices has no common invariant proper subspace, then for each `q > 0` the
potential `‖·‖^q` has a unique `q`-equilibrium state. For `0 < s ≤ 1` the singular value
function is `‖·‖^s` and `q = s`. For `1 < s < 2` and planar matrices
`φ^s(A) = |det A|^{s-1} ‖A‖^{2-s} = ‖A'‖^{2-s}` with the rescaled tuple
`A'_i = |det A_i|^{(s-1)/(2-s)} A_i`, which is irreducible when `𝖠` is, so the proposition
applies with `q = 2 - s`. The source works on the one-sided shift; pressure, entropy and energy
depend on the cylinders at non-negative positions only, and an invariant measure on `Σ` is
determined by them. For `s ≥ 2` the potential is multiplicative and the library proves
uniqueness directly. -/
def FengKaenmakiUnique : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.Irreducible → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ μ' : Measure (ℤ → ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'],
    MeasurePreserving (shift 1) μ μ → MeasurePreserving (shift 1) μ' μ' →
    S.IsEquilibriumState s μ → S.IsEquilibriumState s μ' → μ = μ'

end BoxLike
