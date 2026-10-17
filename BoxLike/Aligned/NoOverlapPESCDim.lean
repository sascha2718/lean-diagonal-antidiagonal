module

/-
The paragraph after the proof of `prop:ssc_no_overlap_not_pesc` (tex lines 1558 to 1561): the
example satisfies the hypotheses of `thm:main2`, so `\dim_H X = dimaff(X)` although the projective
exponential separation condition fails. The theorem of Bárány and Käenmäki enters in the form of
the source, `NoOverlap.BaranyKaenmakiTheorem`.

* `NoOverlap.dimH_eq_dimaff_of_baranyKaenmakiTheorem`: the statement of
  `NoOverlap.dimH_eq_dimaff`, from `NoOverlap.BaranyKaenmakiTheorem` and the system of
  `NoOverlap.prop_ssc_no_overlap_not_pesc`.
-/
public import BoxLike.Aligned.NoOverlapPESC
public import BoxLike.MainTwoFree

@[expose] public section

namespace BoxLike

/-- The example of `prop:ssc_no_overlap_not_pesc` satisfies the hypotheses of `thm:main2` and
`\dim_H X = dimaff(X)` (tex lines 1558 to 1561): it satisfies the strong separation condition,
hence the strong open set condition, its projective system has no exact overlaps, it fails the
projective exponential separation condition, and `dimaff(X) < 2` since `∑_i |det A_i| < 1`.
The theorem of Bárány and Käenmäki enters as the hypothesis `NoOverlap.BaranyKaenmakiTheorem`,
the form of the source; the other hypotheses are the cited theorems that `thm:main2` uses. -/
theorem NoOverlap.dimH_eq_dimaff_of_baranyKaenmakiTheorem (h : NoOverlap.BaranyKaenmakiTheorem)
    (hms : MorrisShmerkinLyapunov.{0}) (hfk : FengKaenmakiGibbs.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hfib : FengInfoSumBar.{0})
    (hly : FengLedrappierYoung.{0}) (hlyb : FengLedrappierYoungBar.{0})
    (hkk : KittleKoglerDimension.{0}) :
    ∃ S : System (Fin 4), S.StrongSeparation ∧ S.NoExactOverlaps ∧ ¬ S.ProjExpSeparation ∧
      S.dimaff < 2 ∧ dimH S.attractor = ENNReal.ofReal S.dimaff := by
  obtain ⟨S, ho, hprox, -, -, -, -, hsep, hfree, hpesc, hdet⟩ :=
    NoOverlap.prop_ssc_no_overlap_not_pesc h
  have hrot : S.WithRotations := ⟨⟨0, by rw [ho]; rfl⟩, ⟨3, by rw [ho]; rfl⟩⟩
  have hfree' : S.NoExactOverlaps := S.noExactOverlaps_iff.2 hfree
  have h2 := S.dimaff_lt_two_of_sum_abs_det_lt_one hdet
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState S.dimaff_nonneg
  exact ⟨S, hsep, hfree', hpesc, h2, S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot
    hprox hfree' h2 μ hinv heq (Or.inr hsep.strongOpenSet)⟩

end BoxLike
