module

public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MainTwoFree
public import BoxLike.DimensionFormula

@[expose] public section

/-!
The full parameter range of `thm:main2`. Below two this uses the manuscript's finite
diagonal subsystems. At and above two the threshold alternative is impossible and
the strong open set condition forces affinity dimension two by the determinant sum.
-/

namespace BoxLike.System

open MeasureTheory

universe u

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) [Nonempty ι]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The determinant argument in the proof of `thm:main_extended`, also used at the
endpoint of `thm:main2`: under SOSC, affinity dimension at least two equals two. -/
theorem StrongOpenSet.dimaff_eq_two (h : S.StrongOpenSet) (h2 : 2 ≤ S.dimaff) :
    S.dimaff = 2 := by
  have hsum := (h.sum_abs_det_eq_one S h2 S.pressure_dimaff).2
  apply S.dimaff_eq zero_le_two
  rw [S.pressure_of_two_le le_rfl]
  simpa using congrArg Real.log hsum

/-- `thm:main2` without an extra `dimaff < 2` assumption. The seven hypotheses on statements
are used only in the finite-subsystem branch below two; `FengLedrappierYoung` and
`KittleKoglerDimension` are cited theorems, and the library proves the other five,
`FengLedrappierYoungBar` from `FengLedrappierYoung`
(`fengLedrappierYoungBar_of_fengLedrappierYoung`). -/
theorem main2_noExactOverlaps_all (hms : BoxLike.MorrisShmerkinLyapunov.{u})
    (hfk : BoxLike.EquilibriumGibbsStatement.{u})
    (hfjj : BoxLike.FraserJordanJurgaDecomposition.{u})
    (hfib : BoxLike.FengInfoSumBar.{u}) (hly : BoxLike.FengLedrappierYoung.{u})
    (hlyb : BoxLike.FengLedrappierYoungBar.{u}) (hkk : BoxLike.KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (BoxLike.shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  rcases lt_or_ge S.dimaff 2 with h2 | h2
  · exact S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot hprox hfree h2 μ
      hinv heq hor
  · have h1neg := S.lyapunov₁_neg hinv
    have h2neg := (S.lyapunov₂_le_lyapunov₁ hinv).trans_lt h1neg
    have hratio : 0 < S.lyapunov₁ μ / S.lyapunov₂ μ := div_pos_of_neg_of_neg h1neg h2neg
    have hsosc : S.StrongOpenSet := hor.resolve_left (by linarith)
    rw [S.dimH_attractor_of_two_le hsosc h2, hsosc.dimaff_eq_two S h2]
    norm_num

end BoxLike.System

namespace BoxLike

open MeasureTheory

/-- The example of `prop:ssc_no_overlap_not_pesc` satisfies the hypotheses of `thm:main2` and
`\dim_H X = dimaff(X)` (tex lines 1522 to 1525): it satisfies the strong separation condition,
hence the strong open set condition, its projective system has no exact overlaps, it fails the
projective exponential separation condition, and `dimaff(X) < 2` since `∑_i |det A_i| < 1`.
The theorem of Bárány and Käenmäki enters as the hypothesis `NoOverlap.BaranyKaenmakiTheorem`. -/
theorem NoOverlap.dimH_eq_dimaff' (h : NoOverlap.BaranyKaenmakiTheorem)
    (hms : MorrisShmerkinLyapunov.{0}) (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hfib : FengInfoSumBar.{0})
    (hly : FengLedrappierYoung.{0}) (hlyb : FengLedrappierYoungBar.{0})
    (hkk : KittleKoglerDimension.{0}) :
    ∃ S : System (Fin 4), S.StrongSeparation ∧ S.NoExactOverlaps ∧ ¬ S.ProjExpSeparation ∧
      S.dimaff < 2 ∧ dimH S.attractor = ENNReal.ofReal S.dimaff := by
  obtain ⟨S, ho, hprox, -, -, -, -, hsep, hfree, hpesc, hdet⟩ :=
    NoOverlap.ssc_no_overlap_not_pesc' h
  have hrot : S.WithRotations := ⟨⟨0, by rw [ho]; rfl⟩, ⟨3, by rw [ho]; rfl⟩⟩
  have hfree' : S.NoExactOverlaps := S.noExactOverlaps_iff.2 hfree
  have h2 := S.dimaff_lt_two_of_sum_abs_det_lt_one hdet
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState S.dimaff_nonneg
  exact ⟨S, hsep, hfree', hpesc, h2, S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot
    hprox hfree' h2 μ hinv heq (Or.inr hsep.strongOpenSet)⟩


end BoxLike
