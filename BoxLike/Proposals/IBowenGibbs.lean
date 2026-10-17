module

/-
PROPOSAL, NOT AUTHORISED. A proposed literature premise for the existence half of the sentence
of `sec:gibbs_measures`, tex lines 2536 to 2538: "since the sub-shift `Σ_Z` is mixing, for each
Hölder continuous potential `f` there exists a unique ergodic Gibbs measure", cited there to
Sarig's lecture notes, Theorem 4.7 and Corollary 4.2. Nothing outside `BoxLike/Proposals/` may
import this file, and no result of the library takes the premise.

The uniqueness half is proved without any premise (`IsGibbsPotential.eq_of_ergodic_of_isHolder`
in `BoxLike/Support/GibbsUniqueness.lean`), and the constant of a Gibbs measure is identified
with `P_Z(f)` without any premise (`IsGibbsPotential.pressure_eq_of_isHolder` in
`BoxLike/Support/HolderPressure.lean`). The existing premise `FraserJordanJurgaDecomposition`
supplies ergodic Gibbs measures only for the two locally constant potentials `f_{1,s}` and
`f_{2,s}`, as part of `System.GibbsDecomposition`; it does not cover an arbitrary Hölder
potential.

* `BowenGibbsExistence`: the proposed premise.
* `existsUnique_ergodic_isGibbsPotential`: conditional on the premise, existence and uniqueness
  of the ergodic Gibbs measure of a Hölder potential, with constant `P_Z(f)`.
-/
public import BoxLike.Support.GibbsUniqueness

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- PROPOSED LITERATURE PREMISE, not authorised. Existence of an ergodic Gibbs measure for a
Hölder potential on the topologically mixing sub-shift `Σ_Z`.

Source. R. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, Lecture
Notes in Mathematics 470, Springer 1975, revised edition 2008 (the article's `Bowen2008`),
Chapter 1, Theorem 1.4 (existence and uniqueness of the invariant Gibbs measure `μ_φ`) with the
mixing of `μ_φ` proved in the same chapter. The article cites instead O. Sarig, *Lecture notes on
thermodynamic formalism for topological Markov shifts* (2009/2013), Theorem 4.7 and Corollary
4.2; those notes could not be accessed while this record was prepared, and their numbering and
hypotheses are unverified here. The theorem numbers of Bowen's book above are also from memory
and must be checked against the book before authorisation.

Source hypotheses (Bowen, Chapter 1): `Σ_A ⊆ {1, …, n}^ℤ` the two-sided sub-shift of finite type
of a `0`-`1` matrix `A` with `A^M > 0` for some `M` (topologically mixing); `φ ∈ ℱ_A`, that is,
`var_k φ ≤ b α^k` for all `k ≥ 0` with `b > 0`, `0 < α < 1`, where
`var_k φ = sup{|φ(x) - φ(y)| : x_i = y_i for |i| ≤ k}`. Conclusion: there is a unique
`σ`-invariant Borel probability measure `μ` on `Σ_A` with constants `c_1, c_2 > 0` and `P` such
that `c_1 ≤ μ{y : y_i = x_i, 0 ≤ i < m} / exp(-Pm + ∑_{k<m} φ(σ^k x)) ≤ c_2` for all `x ∈ Σ_A`
and `m ≥ 0`; `P = P(φ)`, and `μ` is mixing, hence ergodic.

Specialisation. `A = Z` of `sec:subshift` over the alphabet `ι × ZMod 2`; `Z² > 0` exactly when
both orientations occur (`transMatrix_sq_pos`, `isTopologicallyMixing_subshiftShift_iff`).
`IsHolderPotential o f` (Hölder for the standard metric) implies `f ∈ ℱ_Z`
(`IsHolderPotential.exists_abs_sub_le_pow`), so the premise asks for less than the source gives.
A measure on `Σ_Z` is a measure on `(ι × ZMod 2)^ℤ` carried by `Σ_Z`. Only existence, ergodicity
and the bounds are kept; uniqueness and `P = P_Z(f)` are theorems of the library. The potential
is only evaluated on `Σ_Z`, so no measurability hypothesis is needed.

Degenerate-instance test. One letter: the two orientation hypotheses cannot both hold and the
statement is silent; the same for the empty alphabet. Two letters `i_0` diagonal and `i_1`
anti-diagonal with `f = 0`: the conclusion is the existence of the measure of maximal entropy of
`Σ_Z` (the Parry measure), a Markov measure with the Gibbs bounds for `P = log 2`, which exists.
-/
def BowenGibbsExistence : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (o : ι → ZMod 2),
    (∃ i, o i = 0) → (∃ i, o i = 1) → ∀ f : (ℤ → ι × ZMod 2) → ℝ, IsHolderPotential o f →
      ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
        Ergodic (shift 1) ν ∧ ∃ P C : ℝ, IsGibbsPotential o f ν P C

/-- CONDITIONAL ON THE UNAUTHORISED PREMISE `BowenGibbsExistence`. Tex lines 2539 to 2541: for a
box-like tuple with rotations and a Hölder potential `f : Σ_Z → ℝ` there is a unique ergodic
Gibbs probability measure carried by `Σ_Z`, and its constant is `P_Z(f)`. Uniqueness and the
value of the constant are proved in the library; only existence uses the premise. -/
theorem existsUnique_ergodic_isGibbsPotential (hbowen : BowenGibbsExistence.{u}) {ι : Type u}
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (o : ι → ZMod 2)
    (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) (f : (ℤ → ι × ZMod 2) → ℝ)
    (hf : IsHolderPotential o f) :
    ∃! ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
      Ergodic (shift 1) ν ∧ ∃ C : ℝ, IsGibbsPotential o f ν (pressureZPot o f) C := by
  obtain ⟨ν, hprob, hsupp, herg, P, C, hg⟩ := hbowen o h0 h1 f hf
  have hP : P = pressureZPot o f := hg.pressure_eq_of_isHolder h0 hsupp hf
  subst hP
  refine ⟨ν, ⟨hprob, hsupp, herg, C, hg⟩, ?_⟩
  rintro ν' ⟨hprob', hsupp', herg', C', hg'⟩
  exact hg.eq_of_ergodic_of_isHolder hsupp hsupp' hg' hf herg herg'.toMeasurePreserving

end BoxLike
