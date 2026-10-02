module

/-
The uniqueness part of `thm:irred_eq_state` for proximal box-like tuples with rotations, as the
article uses it in the phrase "the unique `s`-equilibrium state" of `thm:main1`, `thm:main2`,
`thm:eq_state_proj_dim` and `thm:main_extended`.

* `System.unique_equilibrium_of_lt_two`: for `0 < s < 2` two `s`-equilibrium states coincide,
  from the uniqueness part of Feng–Käenmäki, `FengKaenmakiUnique`, and the irreducibility of the
  tuple.
* `System.unique_equilibrium_of_two_le`: for `s ≥ 2` both are the Bernoulli measure with the
  weights `|det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`; no hypothesis on the tuple is needed.
* `System.unique_equilibrium`: uniqueness for every `s > 0`.
-/
public import BoxLike.BernoulliEquilibrium
public import BoxLike.LiteratureRemarks
public import BoxLike.SigmaMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- `thm:irred_eq_state`, uniqueness, for a proximal box-like tuple with rotations and
`0 < s < 2`: the tuple is irreducible, so the `s`-equilibrium state is unique. -/
theorem unique_equilibrium_of_lt_two (hfku : FengKaenmakiUnique.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2) (μ μ' : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hinv : MeasurePreserving (shift 1) μ μ)
    (hinv' : MeasurePreserving (shift 1) μ' μ') (heq : S.IsEquilibriumState s μ)
    (heq' : S.IsEquilibriumState s μ') : μ = μ' :=
  hfku S (S.irreducible_of_proximal hrot hprox) hs0 hs2 μ μ' hinv hinv' heq heq'

/-- `thm:irred_eq_state`, uniqueness, for `s ≥ 2` (`sec:normalisation`): every
`s`-equilibrium state is the Bernoulli measure with the weights
`|det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`. -/
theorem unique_equilibrium_of_two_le (hs : 2 ≤ s) (μ μ' : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hinv : MeasurePreserving (shift 1) μ μ)
    (hinv' : MeasurePreserving (shift 1) μ' μ') (heq : S.IsEquilibriumState s μ)
    (heq' : S.IsEquilibriumState s μ') : μ = μ' :=
  (heq.eq_bernoulli hinv hs).trans (heq'.eq_bernoulli hinv' hs).symm

/-- `thm:irred_eq_state`, uniqueness, for a proximal box-like tuple with rotations and every
`s > 0`. -/
theorem unique_equilibrium (hfku : FengKaenmakiUnique.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (hs0 : 0 < s) (μ μ' : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hinv : MeasurePreserving (shift 1) μ μ)
    (hinv' : MeasurePreserving (shift 1) μ' μ') (heq : S.IsEquilibriumState s μ)
    (heq' : S.IsEquilibriumState s μ') : μ = μ' := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · exact S.unique_equilibrium_of_lt_two hfku hrot hprox hs0 hs2 μ μ' hinv hinv' heq heq'
  · exact S.unique_equilibrium_of_two_le hs2 μ μ' hinv hinv' heq heq'

end System

end BoxLike
