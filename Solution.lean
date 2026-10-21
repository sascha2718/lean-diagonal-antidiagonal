module

public import Solution.Transport

@[expose] public section

/-!
# Proofs of the challenge statements

Each headline proof applies the library theorem to `toLib S` through `Solution.Transport`.
The second part has one entry per numbered statement of the manuscript, listing the Lean
declarations that cover it; `docs/correspondence.md` records the assessment and the proof
deviations.
-/

namespace Challenge

universe u

open MeasureTheory Solution.Transport

/-! ## Dimension of the projections of the equilibrium state -/

/-- Theorem 1.2 (`thm:main1`), for every `s`-equilibrium state with `s = dimaff(X)`. -/
theorem audit_main1 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ) (c : ZMod 2) :
    IsDoubleDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔
        S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep hinv heq
  simp only [isDoubleDim_iff, isExactDim_iff, marginal_eq, entropy_eq, lyapunov₁_eq,
    lyapunov₂_eq, dimaff_eq]
  exact (toLib S).main1_dimaff_all BoxLike.morrisShmerkinLyapunov_holds BoxLike.equilibriumGibbs
    BoxLike.fraserJordanJurgaDecomposition_holds hjr hrot hprox hsep μ
    hinv heq c

/-- Theorem 4.4 (`thm:eq_state_proj_dim`), for every `s`-equilibrium state, `s > 0`. -/
theorem audit_eq_state_proj_dim {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) {s : ℝ}
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    IsDoubleDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep hinv heq
  simp only [isDoubleDim_iff, upperPackingDim_eq, lowerHausdorffDim_eq, marginal_eq, entropy_eq,
    lyapunov₁_eq, lyapunov₂_eq]
  exact (toLib S).eq_state_proj_dim_all BoxLike.morrisShmerkinLyapunov_holds
    BoxLike.equilibriumGibbs BoxLike.fraserJordanJurgaDecomposition_holds
    hjr hrot hprox hsep hs0 μ hinv heq c

/-! ## Dimension of the equilibrium state and of the self-affine set -/

/-- Theorem 1.3 (`thm:main2`), for every `s`-equilibrium state with `s = dimaff(X)`. -/
theorem audit_main2 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  simp only [withRotations_iff, proximal_iff, noExactOverlaps_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, lyapunov₁_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hfree hinv heq hor
  rw [attractor_eq, dimaff_eq]
  exact (toLib S).main2_prose BoxLike.shannonMcMillanBreiman BoxLike.morrisShmerkinLyapunov_holds
    BoxLike.equilibriumGibbs BoxLike.fraserJordanJurgaDecomposition_holds
    BoxLike.fengLedrappierYoung_holds
    BoxLike.kittleKoglerDimension_holds hrot hprox hfree μ hinv heq hor

/-- Theorem 4.16 (`thm:main_extended`), for every `s`-equilibrium state with `s = dimaff(X)`. -/
theorem audit_main_extended {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) (min 2 S.dimaff) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, entropy_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep hinv heq hor
  rw [isExactDim_iff, proj_eq, dimaff_eq]
  exact (toLib S).main_extended_min BoxLike.morrisShmerkinLyapunov_holds BoxLike.equilibriumGibbs
    BoxLike.fraserJordanJurgaDecomposition_holds hjr
    BoxLike.fengInfoSum_holds BoxLike.fengInfoSumBar_holds BoxLike.fengLedrappierYoung_holds
    BoxLike.fengLedrappierYoungBar_holds hrot hprox
    hsep μ hinv heq hor

/-- Theorem 4.16 (`thm:main_extended`) for `s ≥ 2` under the strong open set condition:
`π_*μ` is exact-dimensional of dimension two. Rotations, proximality and separation are not
needed. -/
theorem audit_main_extended_ge_two {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) {s : ℝ} (hsosc : S.StrongOpenSet) (hs : 2 ≤ s)
    (hP : S.pressure s = 0) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    IsExactDim (μ.map S.proj) 2 := by
  rw [strongOpenSet_iff] at hsosc
  rw [pressure_eq] at hP
  rw [shift_eq] at hinv
  rw [isEquilibriumState_iff] at heq
  rw [isExactDim_iff, proj_eq]
  exact (toLib S).main_extended_ge_two hsosc hs hP μ hinv heq

/-- `dim_H(X) = min{2, dimaff(X)}` under the hypotheses of Theorem 4.16, the formula of the
paragraph after (4.4): Theorem 4.16 and Falconer's bound `eq:hausdorff_affinity_upper_bound`. -/
theorem audit_dimH_eq_min {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, entropy_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep hinv heq hor
  rw [attractor_eq, dimaff_eq]
  exact (toLib S).dimH_attractor_eq_min BoxLike.morrisShmerkinLyapunov_holds
    BoxLike.equilibriumGibbs BoxLike.fraserJordanJurgaDecomposition_holds
    hjr BoxLike.fengInfoSum_holds BoxLike.fengInfoSumBar_holds
    BoxLike.fengLedrappierYoung_holds
    BoxLike.fengLedrappierYoungBar_holds hrot hprox
    hsep μ hinv heq hor

/-- `dim_H(X) = 2` when `dimaff(X) ≥ 2` and `X` satisfies the strong open set condition. -/
theorem audit_dimH_of_two_le {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) [Nonempty ι] (hsosc : S.StrongOpenSet)
    (h2 : 2 ≤ S.dimaff) : dimH S.attractor = 2 := by
  rw [strongOpenSet_iff] at hsosc
  rw [dimaff_eq] at h2
  rw [attractor_eq]
  exact (toLib S).dimH_attractor_of_two_le hsosc h2

end Challenge



/-! ## Numbered manuscript entries

One entry per numbered statement, with the declarations that cover it. An alias keeps the
hypotheses of its declaration. No entry takes a literature hypothesis; `docs/correspondence.md`
records the inputs and the proof deviations.
-/

namespace Solution.Paper

universe u

-- PAPER_ENTRY thm:fraser
/-! 1.1 (`thm:fraser`): formalized.
Both parts of Fraser's Theorem 2.3 (`paper_1_1_0`) and Corollary 2.5 (`paper_1_1_13`,
`paper_1_1_14`), along Fraser's proof. Deviation: in the super-multiplicative case of his
Lemma 5.1 (2) a block sum replaces the `k`-block stopping set, which need not be prefix-free.
-/
/-- `thm:fraser`: both parts of Fraser's Theorem 2.3. -/
theorem paper_1_1_0 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι) :
    S.FraserBound ∧ S.FraserROSC :=
  ⟨S.fraserBound_holds, S.fraserROSC_holds⟩
noncomputable abbrev paper_1_1_1 := @BoxLike.System.FraserBound
noncomputable abbrev paper_1_1_2 := @BoxLike.System.FraserROSC
noncomputable abbrev paper_1_1_3 := @BoxLike.System.packingDim_attractor
noncomputable abbrev paper_1_1_4 := @BoxLike.System.FraserROSC.dimmaff_eq_dimaff
noncomputable abbrev paper_1_1_5 := @BoxLike.System.FraserROSC.dim_eq_dimaff
noncomputable abbrev paper_1_1_6 := @BoxLike.System.fraserBound_holds
noncomputable abbrev paper_1_1_7 := @BoxLike.System.fraserROSC_holds
noncomputable abbrev paper_1_1_8 := @BoxLike.System.upperBoxDim_attractor_le_dimmaff
noncomputable abbrev paper_1_1_9 := @BoxLike.System.upperBoxDim_attractor_le_of_modPressure_neg
noncomputable abbrev paper_1_1_10 := @BoxLike.System.dimmaff_le_lowerBoxDim
noncomputable abbrev paper_1_1_11 := @BoxLike.System.exists_le_fraserStopSum
noncomputable abbrev paper_1_1_12 := @BoxLike.System.fraserROSC_of_fraserBound
/-- `thm:fraser`, third part (Fraser's Corollary 2.5). -/
theorem paper_1_1_13 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι)
    (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, BoxLike.upperBoxDim (BoxLike.System.coord c '' S.attractor) = 1) :
    BoxLike.packingDim S.attractor = ENNReal.ofReal S.dimaff ∧
      BoxLike.lowerBoxDim S.attractor = ENNReal.ofReal S.dimaff ∧
      BoxLike.upperBoxDim S.attractor = ENNReal.ofReal S.dimaff :=
  S.fraserROSC_holds.dim_eq_dimaff hrosc hproj
/-- `thm:fraser`, third part, as the paper states it: `dimmaff(X) = dimaff(X)`. -/
theorem paper_1_1_14 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι)
    (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, BoxLike.upperBoxDim (BoxLike.System.coord c '' S.attractor) = 1) :
    S.dimmaff = S.dimaff :=
  S.fraserROSC_holds.dimmaff_eq_dimaff hrosc hproj

-- PAPER_ENTRY thm:main1
/-! 1.2 (`thm:main1`): formalized.
For every `s`-equilibrium state; uniqueness and ergodicity are not needed. Jordan–Rapaport
gives exact-dimensionality under separation directly, so Feng–Hu is not used.
-/
noncomputable abbrev paper_1_2_1 := @Challenge.audit_main1
noncomputable abbrev paper_1_2_2 := @BoxLike.System.main1_dimaff_all
noncomputable abbrev paper_1_2_3 := @BoxLike.System.main1_all
noncomputable abbrev paper_1_2_4 := @BoxLike.System.main1_of_two_le
noncomputable abbrev paper_1_2_5 := @BoxLike.System.main1
noncomputable abbrev paper_1_2_6 := @BoxLike.System.eq_state_proj_dim_all

-- PAPER_ENTRY thm:main2
/-! 1.3 (`thm:main2`): formalized.
For every value of `dimaff` and every equilibrium state, along the prose (`System.main2_prose`).
Deviations: the returns to horizontal orientation come from ergodicity, not mixing; the scalar
Ledrappier–Young formula for the diagonal subsystem comes from the planar `FengLedrappierYoung`
applied to an auxiliary box-like system; Falconer's bound is proved.
-/
noncomputable abbrev paper_1_3_1 := @Challenge.audit_main2
noncomputable abbrev paper_1_3_2 := @BoxLike.System.main2_prose
noncomputable abbrev paper_1_3_3 := @BoxLike.System.main2_noExactOverlaps_prose
noncomputable abbrev paper_1_3_4 := @BoxLike.System.main2_prose_all
noncomputable abbrev paper_1_3_5 := @BoxLike.System.StrongOpenSet.dimaff_eq_two
noncomputable abbrev paper_1_3_6 := @BoxLike.System.exists_typical_words_prose
noncomputable abbrev paper_1_3_7 := @BoxLike.System.IsHomDiag.isExactDim_map_proj
noncomputable abbrev paper_1_3_8 := @BoxLike.System.le_dimH_attractor_of_family
noncomputable abbrev paper_1_3_9 := @BoxLike.System.subsystem_strongSeparation
noncomputable abbrev paper_1_3_10 := @BoxLike.System.main2_noExactOverlaps_all

-- PAPER_ENTRY q:coincident-projection-dimensions
/-! 1.4 (`q:coincident-projection-dimensions`): intentionally_unformalized.
Open; recorded as a proposition with no answer asserted.
-/
/-- Question 1.4 as a proposition; no answer is asserted. -/
abbrev paper_1_4_1 : Prop := BoxLike.CoincidentProjectionDimensionsQuestion

-- PAPER_ENTRY thm:box_like_sa
/-! 2.1 (`thm:box_like_sa`): formalized.
"Rotating" is read as exchanging the coordinate axes, the convention of tex 389 to 392.
-/
noncomputable abbrev paper_2_1_1 := @BoxLike.box_like_sa_of_contracting
noncomputable abbrev paper_2_1_2 := @BoxLike.PlanarSystem.box_like_sa
noncomputable abbrev paper_2_1_3 := @BoxLike.box_like_sa
noncomputable abbrev paper_2_1_4 := @BoxLike.System.isBoxLikeWithRotations_iff
noncomputable abbrev paper_2_1_5 := @BoxLike.PlanarSystem.isBoxLikeWithRotations_iff_exists_system
noncomputable abbrev paper_2_1_6 := @BoxLike.isSquareIsometry_iff
noncomputable abbrev paper_2_1_7 := @BoxLike.isBoxLikeMatrix_iff
noncomputable abbrev paper_2_1_8 := @BoxLike.IsSquareIsometry.boxMat_zero_mul_orientation
noncomputable abbrev paper_2_1_9 := @BoxLike.System.WithRotations

-- PAPER_ENTRY thm:A_classification
/-! 2.2 (`thm:A_classification`): formalized.
Proved directly for arbitrary planar tuples; the cited theorems of Bárány–Käenmäki–Rossi and
Bárány–Käenmäki–Yu are not used.
-/
noncomputable abbrev paper_2_2_1 := @BoxLike.tuple_classification
noncomputable abbrev paper_2_2_2 := @BoxLike.tuple_trichotomy
noncomputable abbrev paper_2_2_3 := @BoxLike.simultaneouslyBoxLike_iff
noncomputable abbrev paper_2_2_4 := @BoxLike.not_tupleIrreducible_iff_simultaneouslyTriangular
noncomputable abbrev paper_2_2_5 := @BoxLike.tupleIrreducible_iff_lines
noncomputable abbrev paper_2_2_6 := @BoxLike.tupleStronglyIrreducible_iff_lines

-- PAPER_ENTRY thm:box_like_proximal
/-! 2.3 (`thm:box_like_proximal`): formalized.
Along the prose (`System.Proximal.box_like_proximal`).
-/
noncomputable abbrev paper_2_3_1 := @BoxLike.System.Proximal.box_like_proximal
noncomputable abbrev paper_2_3_2 := @BoxLike.System.isProximalMatrix_matWord
noncomputable abbrev paper_2_3_3 := @BoxLike.System.absMat_matWord_eq_smul_pairs
noncomputable abbrev paper_2_3_4 := @BoxLike.System.sq_o_of_mem_pairs
noncomputable abbrev paper_2_3_5 := @BoxLike.System.prod_absMat_sq_mat_eq_smul
noncomputable abbrev paper_2_3_6 := @BoxLike.System.exists_anti_of_isProximalMatrix
noncomputable abbrev paper_2_3_7 := @BoxLike.System.Proximal.hasProximalDiagonal_or_sq

-- PAPER_ENTRY thm:tau_omega_sigma_commutative
/-! 2.4 (`thm:tau_omega_sigma_commutative`): formalized.
For every integer `n`.
-/
noncomputable abbrev paper_2_4_1 := @BoxLike.tau_shift_of_eps_eq_zero
noncomputable abbrev paper_2_4_2 := @BoxLike.omega_shift_of_eps_eq_zero
noncomputable abbrev paper_2_4_3 := @BoxLike.tau_shift_of_eps_eq_one
noncomputable abbrev paper_2_4_4 := @BoxLike.omega_shift_of_eps_eq_one
noncomputable abbrev paper_2_4_5 := @BoxLike.eps_shift

-- PAPER_ENTRY thm:matrix_products_g_derivatives
/-! 2.5 (`thm:matrix_products_g_derivatives`): formalized.
Proximality and rotations are not used.
-/
noncomputable abbrev paper_2_5_1 := @BoxLike.System.abs_matWord_pastWord_e1
noncomputable abbrev paper_2_5_2 := @BoxLike.System.abs_matWord_pastWord_e2
noncomputable abbrev paper_2_5_3 := @BoxLike.System.matWord_eq
noncomputable abbrev paper_2_5_4 := @BoxLike.System.codeWord_pastWord_tau
noncomputable abbrev paper_2_5_5 := @BoxLike.System.codeWord_pastWord_omega

-- PAPER_ENTRY lem:proj_gap_dominated
/-! 2.6 (`lem:proj_gap_dominated`): formalized.
An empty infimum is `⊤`.
-/
noncomputable abbrev paper_2_6_1 := @BoxLike.System.diagGap
noncomputable abbrev paper_2_6_2 := @BoxLike.System.gap_le_diagGap

-- PAPER_ENTRY prop:ssc_no_overlap_not_pesc
/-! 2.7 (`prop:ssc_no_overlap_not_pesc`): formalized.
Along the prose, with `BaranyKaenmakiPair`, the form of Bárány–Käenmäki's theorem the proof
uses, proved (`baranyKaenmakiPair_holds`). Theorem 2.1 of the source as stated is false
(`not_baranyKaenmakiTheorem`); the citation at tex lines 1424 to 1429 needs a fix.
-/
noncomputable abbrev paper_2_7_1 := @BoxLike.NoOverlap.prop_ssc_no_overlap_not_pesc
noncomputable abbrev paper_2_7_2 := @BoxLike.NoOverlap.baranyKaenmakiPair_holds
noncomputable abbrev paper_2_7_3 := @BoxLike.NoOverlap.exists_params_not_mem_exceptionalSet
noncomputable abbrev paper_2_7_4 := @BoxLike.NoOverlap.Params.mulIndependent
noncomputable abbrev paper_2_7_5 := @BoxLike.NoOverlap.Params.count_eq_of_gDeriv_eq
noncomputable abbrev paper_2_7_6 := @BoxLike.NoOverlap.eq_of_valPoly_eq
noncomputable abbrev paper_2_7_7 := @BoxLike.NoOverlap.Params.freeProjective_of_mulIndependent
noncomputable abbrev paper_2_7_8 := @BoxLike.NoOverlap.Params.strongSeparation
noncomputable abbrev paper_2_7_9 := @BoxLike.NoOverlap.Params.not_projExpSeparation
noncomputable abbrev paper_2_7_10 := @BoxLike.NoOverlap.prop_ssc_no_overlap_not_pesc_holds

-- PAPER_ENTRY thm:lyapunov_exponents_via_g_system
/-! 3.1 (`thm:lyapunov_exponents_via_g_system`): formalized.
`MatrixTuple.OseledetsSet` is the article's `Σ'` with its filtration; Oseledets and
Froyland–Lloyd–Quas are proved for box-like tuples. The Furstenberg measure is not formalised
beyond the support of `V¹` on the axes.
-/
noncomputable abbrev paper_3_1_1 := @BoxLike.System.lyapunov_exponents_via_g_system_manuscript
noncomputable abbrev paper_3_1_2 := @BoxLike.System.lyapunov_exponents_via_g_system_oseledets
noncomputable abbrev paper_3_1_3 := @BoxLike.System.oseledetsSet
noncomputable abbrev paper_3_1_4 := @BoxLike.System.V_one_eq_axis
noncomputable abbrev paper_3_1_5 := @BoxLike.System.V_eq_oseledetsSub
noncomputable abbrev paper_3_1_6 := @BoxLike.System.sigmaTau_ae_eq
noncomputable abbrev paper_3_1_7 := @BoxLike.System.sigmaOmega_ae_eq
noncomputable abbrev paper_3_1_8 := @BoxLike.System.sigmaTau_union_sigmaOmega
noncomputable abbrev paper_3_1_9 :=
  @BoxLike.MatrixTuple.OseledetsSet.disjoint_sigmaTau_sigmaOmega
noncomputable abbrev paper_3_1_10 := @BoxLike.MatrixTuple.OseledetsSet.mem_V_one_iff
noncomputable abbrev paper_3_1_11 := @BoxLike.System.condMeas_fengXi_ae_eq
noncomputable abbrev paper_3_1_12 := @BoxLike.System.condEntropy_oseledetsXi_eq
noncomputable abbrev paper_3_1_13 := @BoxLike.System.lyapunov_exponents_via_g_system
noncomputable abbrev paper_3_1_14 := @BoxLike.System.measure_SigmaPrime_compl

-- PAPER_ENTRY thm:conditional_measures_of_a_conditional_measure
/-! 3.2 (`thm:conditional_measures_of_a_conditional_measure`): formalized.
For every standard Borel space.
-/
noncomputable abbrev paper_3_2_1 := @BoxLike.condMeas_cond
noncomputable abbrev paper_3_2_2 := @BoxLike.condMeas_cond_of_saturated

-- PAPER_ENTRY thm:double_conditional
/-! 3.3 (`thm:double_conditional`): formalized.
For every standard Borel space; Einsiedler–Ward, Proposition 5.20 and Theorem 5.14, are proved
directly.
-/
noncomputable abbrev paper_3_3_1 := @BoxLike.double_conditional

-- PAPER_ENTRY thm:finer_partition_dirac_mass
/-! 3.4 (`thm:finer_partition_dirac_mass`): formalized.
-/
noncomputable abbrev paper_3_4_1 := @BoxLike.finer_partition_dirac_mass
noncomputable abbrev paper_3_4_2 := @BoxLike.condMeas_dirac

-- PAPER_ENTRY thm:feng_entropy_as_limit
/-! 3.5 (`thm:feng_entropy_as_limit`): formalized.
At the article's scope; Feng's identity (Lemma 4.6, (4.16)) and the planar Oseledets theorem
are proved.
-/
noncomputable abbrev paper_3_5_1 := @BoxLike.System.feng_entropy_as_limit
noncomputable abbrev paper_3_5_2 := @BoxLike.System.feng_entropy_as_limit_bar
noncomputable abbrev paper_3_5_3 := @BoxLike.tendsto_neg_log_condMeas_cylinder
noncomputable abbrev paper_3_5_4 := @BoxLike.feng_entropy_as_limit_boxLike
noncomputable abbrev paper_3_5_5 := @BoxLike.PlanarSystem.feng_entropy_as_limit_of_infoSum
noncomputable abbrev paper_3_5_6 := @BoxLike.feng_entropy_as_limit_boxLike_holds
noncomputable abbrev paper_3_5_7 := @BoxLike.feng_entropy_as_limit_of_full
noncomputable abbrev paper_3_5_8 := @BoxLike.PlanarSystem.feng_entropy_as_limit_of_full
noncomputable abbrev paper_3_5_9 := @BoxLike.PlanarSystem.infoSum_xi
noncomputable abbrev paper_3_5_10 := @BoxLike.fengInfoSum_holds
noncomputable abbrev paper_3_5_11 := @BoxLike.fengInfoSumBar_holds
noncomputable abbrev paper_3_5_12 := @BoxLike.infoSum_of_pullShift
noncomputable abbrev paper_3_5_13 := @BoxLike.feng_entropy_as_limit_general

-- PAPER_ENTRY thm:feng_entropy_kolmogorov_sinai
/-! 3.6 (`thm:feng_entropy_kolmogorov_sinai`): formalized.
At the article's scope, through the Shannon–McMillan–Breiman theorem, the Kolmogorov–Sinai
generator theorem and the planar Oseledets theorem, all proved.
-/
noncomputable abbrev paper_3_6_1 := @BoxLike.PlanarSystem.feng_entropy_kolmogorov_sinai_general
noncomputable abbrev paper_3_6_2 := @BoxLike.System.feng_entropy_kolmogorov_sinai
noncomputable abbrev paper_3_6_3 :=
  @BoxLike.PlanarSystem.tendsto_neg_log_cylinder_dimEntropyAt_of_ergodic
noncomputable abbrev paper_3_6_4 :=
  @BoxLike.PlanarSystem.feng_entropy_kolmogorov_sinai_of_oseledetsSet
noncomputable abbrev paper_3_6_5 := @BoxLike.PlanarSystem.oseledetsSetOfErgodic
noncomputable abbrev paper_3_6_6 := @BoxLike.MatrixTuple.measure_regularSet_compl_of_ergodic
noncomputable abbrev paper_3_6_7 := @BoxLike.shannonMcMillanBreiman
noncomputable abbrev paper_3_6_8 := @BoxLike.tendsto_neg_log_cylinder_localEntropy_of_atoms
noncomputable abbrev paper_3_6_9 := @BoxLike.ksEntropy_shift_eq_entropy
noncomputable abbrev paper_3_6_10 := @BoxLike.PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_ergodic
noncomputable abbrev paper_3_6_11 := @BoxLike.System.feng_entropy_kolmogorov_sinai_toPlanar
noncomputable abbrev paper_3_6_12 := @BoxLike.System.feng_entropy_kolmogorov_sinai_bar
noncomputable abbrev paper_3_6_13 := @BoxLike.kingman_ergodic

-- PAPER_ENTRY thm:feng_entropy_zero
/-! 3.7 (`thm:feng_entropy_zero`): formalized.
The pointwise equivalence `h_i(μ, 𝐢) = 0 ⟺ μ_𝐢^{ξ_i} = δ_𝐢`, at the article's scope.
-/
noncomputable abbrev paper_3_7_1 := @BoxLike.System.feng_entropy_zero
noncomputable abbrev paper_3_7_2 := @BoxLike.System.feng_entropy_zero_bar
noncomputable abbrev paper_3_7_3 := @BoxLike.localEntropy_eq_zero_iff_condMeas_eq_dirac
noncomputable abbrev paper_3_7_4 := @BoxLike.feng_entropy_zero_boxLike
noncomputable abbrev paper_3_7_5 := @BoxLike.PlanarSystem.feng_entropy_zero_of_infoSum
noncomputable abbrev paper_3_7_6 := @BoxLike.feng_entropy_zero_boxLike_holds
noncomputable abbrev paper_3_7_7 := @BoxLike.feng_entropy_zero_of_full
noncomputable abbrev paper_3_7_8 := @BoxLike.PlanarSystem.feng_entropy_zero_of_full
noncomputable abbrev paper_3_7_9 := @BoxLike.fengInfoSum_holds
noncomputable abbrev paper_3_7_10 := @BoxLike.fengInfoSumBar_holds
noncomputable abbrev paper_3_7_11 := @BoxLike.feng_entropy_zero_general

-- PAPER_ENTRY thm:partitions_xi1
/-! 3.8 (`thm:partitions_xi1`): formalized.
The combined wrapper carries unused binders; the component lemmas do not.
-/
noncomputable abbrev paper_3_8_1 := @BoxLike.System.partitions_xi1
noncomputable abbrev paper_3_8_2 := @BoxLike.System.xi_one_of_mem_SigmaTau
noncomputable abbrev paper_3_8_3 := @BoxLike.System.xiPerp_of_mem_SigmaTau
noncomputable abbrev paper_3_8_4 := @BoxLike.System.xi_one_of_mem_SigmaOmega
noncomputable abbrev paper_3_8_5 := @BoxLike.System.xiPerp_of_mem_SigmaOmega

-- PAPER_ENTRY thm:partition_tau_conj
/-! 3.9 (`thm:partition_tau_conj`): formalized.
For every `n`; the combined wrapper carries unused binders.
-/
noncomputable abbrev paper_3_9_1 := @BoxLike.System.partition_tau_conj
noncomputable abbrev paper_3_9_2 := @BoxLike.System.image_unCode_xiBar_inter_cylinder_tau
noncomputable abbrev paper_3_9_3 := @BoxLike.System.image_unCode_xiBar_inter_cylinder_omega

-- PAPER_ENTRY thm:irred_eq_state
/-! 3.10 (`thm:irred_eq_state`): formalized.
At the article's scope, every irreducible tuple in `GL_2(ℝ)^N` and `s > 0` (`paper_3_10_25`),
from Feng–Käenmäki's Proposition 1.2 in the form of the source, proved (`paper_3_10_27`);
for box-like tuples with rotations, irreducible or not, with no literature input
(`System.irred_eq_state_of_withRotations`, `paper_3_10_24`).
-/
noncomputable abbrev paper_3_10_0 := @BoxLike.MatrixTuple.irred_eq_state_of_fengKaenmaki
noncomputable abbrev paper_3_10_1 := @BoxLike.System.irred_eq_state
noncomputable abbrev paper_3_10_2 := @BoxLike.System.unique_of_irreducible
noncomputable abbrev paper_3_10_3 := @BoxLike.System.IsEquilibriumState.ergodic_of_irreducible
noncomputable abbrev paper_3_10_4 :=
  @BoxLike.System.IsEquilibriumState.hasGibbsBounds_of_irreducible
noncomputable abbrev paper_3_10_5 := @BoxLike.MatrixTuple.exists_isEquilibriumState
noncomputable abbrev paper_3_10_6 := @BoxLike.MatrixTuple.irred_eq_state_of_two_le
noncomputable abbrev paper_3_10_7 := @BoxLike.MatrixTuple.ergodic_of_unique
noncomputable abbrev paper_3_10_8 := @BoxLike.MatrixTuple.isEquilibriumState_iff_rescale
noncomputable abbrev paper_3_10_9 := @BoxLike.MatrixTuple.hasGibbsBounds_iff_rescale
noncomputable abbrev paper_3_10_10 := @BoxLike.MatrixTuple.isNormEquilibriumPlus_map_eta_iff
noncomputable abbrev paper_3_10_11 := @BoxLike.MatrixTuple.exists_ergodic_isEquilibriumState
noncomputable abbrev paper_3_10_12 := @BoxLike.FengKaenmakiNormEquilibrium.svf
noncomputable abbrev paper_3_10_13 := @BoxLike.FengKaenmakiNormEquilibrium.twoSided
noncomputable abbrev paper_3_10_14 := @BoxLike.FengKaenmakiNormEquilibrium.fengKaenmakiGibbs
noncomputable abbrev paper_3_10_15 := @BoxLike.FengKaenmakiNormEquilibrium.fengKaenmakiUnique
noncomputable abbrev paper_3_10_16 := @BoxLike.System.irred_eq_state_of_withRotations
noncomputable abbrev paper_3_10_17 := @BoxLike.System.unique_of_withRotations
noncomputable abbrev paper_3_10_18 := @BoxLike.System.IsEquilibriumState.ergodic_of_withRotations
noncomputable abbrev paper_3_10_19 :=
  @BoxLike.System.IsEquilibriumState.hasGibbsBounds_of_withRotations
noncomputable abbrev paper_3_10_20 :=
  @BoxLike.System.existsUnique_isEquilibriumState_of_withRotations
noncomputable abbrev paper_3_10_21 := @BoxLike.System.IsEquilibriumState.eq_map_unCode
noncomputable abbrev paper_3_10_22 := @BoxLike.System.IsEquilibriumState.blockRelEntropy_le
noncomputable abbrev paper_3_10_23 := @BoxLike.absolutelyContinuous_of_blockRelEntropy_le
/-- The Gibbs bounds of `thm:irred_eq_state` for tuples with rotations. -/
theorem paper_3_10_24 : BoxLike.EquilibriumGibbsStatement.{u} := BoxLike.equilibriumGibbs
open MeasureTheory in
/-- `thm:irred_eq_state` for every irreducible tuple of invertible planar matrices and `s > 0`. -/
theorem paper_3_10_25 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i, (A i).det ≠ 0)
    (hirr : BoxLike.TupleIrreducible A) {s : ℝ} (hs0 : 0 < s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (BoxLike.shift 1) μ μ ∧
      BoxLike.MatrixTuple.IsEquilibriumState A s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (BoxLike.shift 1) ν ν →
        BoxLike.MatrixTuple.IsEquilibriumState A s ν → ν = μ) ∧
      Ergodic (BoxLike.shift 1) μ ∧ BoxLike.MatrixTuple.HasGibbsBounds A s μ :=
  BoxLike.MatrixTuple.irred_eq_state_of_fengKaenmaki BoxLike.fengKaenmakiNormEquilibrium_holds A hA
    hirr hs0
open MeasureTheory in
/-- `thm:irred_eq_state` for irreducible box-like systems. -/
theorem paper_3_10_26 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : BoxLike.System ι) (hirr : S.Irreducible) {s : ℝ} (hs0 : 0 < s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (BoxLike.shift 1) μ μ ∧
      S.IsEquilibriumState s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (BoxLike.shift 1) ν ν →
        S.IsEquilibriumState s ν → ν = μ) ∧
      Ergodic (BoxLike.shift 1) μ ∧ S.HasGibbsBounds s μ :=
  S.irred_eq_state BoxLike.fengKaenmakiGibbs_holds BoxLike.fengKaenmakiUnique_holds hirr hs0
/-- Feng–Käenmäki, Proposition 1.2, in the form of the source. -/
theorem paper_3_10_27 : BoxLike.FengKaenmakiNormEquilibrium.{u} :=
  BoxLike.fengKaenmakiNormEquilibrium_holds
/-- The Gibbs bounds of `thm:irred_eq_state` for irreducible box-like tuples, `0 < s < 2`. -/
theorem paper_3_10_28 : BoxLike.FengKaenmakiGibbs.{u} := BoxLike.fengKaenmakiGibbs_holds
/-- Uniqueness in `thm:irred_eq_state` for irreducible box-like tuples, `0 < s < 2`. -/
theorem paper_3_10_29 : BoxLike.FengKaenmakiUnique.{u} := BoxLike.fengKaenmakiUnique_holds
noncomputable abbrev paper_3_10_30 := @BoxLike.fengKaenmakiNormEquilibrium_of_normGibbsExistence
noncomputable abbrev paper_3_10_31 := @BoxLike.normGibbsExistence
noncomputable abbrev paper_3_10_32 := @BoxLike.MatrixTuple.normQuasiMultiplicative_of_irreducible
noncomputable abbrev paper_3_10_33 := @BoxLike.MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs
noncomputable abbrev paper_3_10_34 := @BoxLike.MatrixTuple.HasNormGibbs.ergodic
noncomputable abbrev paper_3_10_35 := @BoxLike.MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq
noncomputable abbrev paper_3_10_36 :=
  @BoxLike.MatrixTuple.NormQuasiMultiplicative.exists_ergodic_hasNormGibbs

-- PAPER_ENTRY thm:two-block-normalisation
/-! 3.11 (`thm:two-block-normalisation`): formalized.
Uniqueness and ergodicity of `μ^(2)` come from 3.10 for `𝖠²`, which has rotations.
-/
noncomputable abbrev paper_3_11_1 := @BoxLike.System.two_block_normalisation
noncomputable abbrev paper_3_11_2 := @BoxLike.System.two_block_normalisation_consequences
noncomputable abbrev paper_3_11_3 := @BoxLike.System.Proximal.sq_hasProximalDiagonal
noncomputable abbrev paper_3_11_4 := @BoxLike.System.sq_irreducible
noncomputable abbrev paper_3_11_5 := @BoxLike.IsBernoulli.map_group
noncomputable abbrev paper_3_11_6 := @BoxLike.System.IsEquilibriumState.map_group

-- PAPER_ENTRY thm:bernoulli_equilibrium
/-! 3.12 (`thm:bernoulli_equilibrium`): formalized.
-/
noncomputable abbrev paper_3_12_1 := @BoxLike.System.pressure_of_two_le
noncomputable abbrev paper_3_12_2 := @BoxLike.System.detWeight
noncomputable abbrev paper_3_12_3 := @BoxLike.System.isEquilibriumState_bernoulli
noncomputable abbrev paper_3_12_4 := @BoxLike.System.IsEquilibriumState.eq_bernoulli
noncomputable abbrev paper_3_12_5 := @BoxLike.System.existsUnique_isEquilibriumState_of_two_le
noncomputable abbrev paper_3_12_6 := @BoxLike.bernoulli_cylinder

-- PAPER_ENTRY thm:sigma_tau_omega_positive_eq_measure
/-! 3.13 (`thm:sigma_tau_omega_positive_eq_measure`): formalized.
Proximality is not used.
-/
noncomputable abbrev paper_3_13_1 := @BoxLike.System.sigma_tau_omega_positive_eq_measure
noncomputable abbrev paper_3_13_2 := @BoxLike.System.measureReal_antiDiagSet_le
noncomputable abbrev paper_3_13_3 := @BoxLike.System.birkhoffSum_antiDiagSet_le
noncomputable abbrev paper_3_13_4 := @BoxLike.System.indicator_antiDiagSet_le
noncomputable abbrev paper_3_13_5 := @BoxLike.System.sigma_tau_omega_positive
noncomputable abbrev paper_3_13_6 := @BoxLike.System.measure_cylinder_le_two_mul

-- PAPER_ENTRY thm:eq_state_is_sum
/-! 3.14 (`thm:eq_state_is_sum`): formalized.
`FraserJordanJurgaDecomposition` is proved (`paper_3_14_0`); proximality is not used.
-/
/-- `thm:eq_state_is_sum`: `FraserJordanJurgaDecomposition` holds. -/
theorem paper_3_14_0 : BoxLike.FraserJordanJurgaDecomposition.{u} :=
  BoxLike.fraserJordanJurgaDecomposition_holds
noncomputable abbrev paper_3_14_1 := @BoxLike.FraserJordanJurgaDecomposition.{u}
noncomputable abbrev paper_3_14_2 := @BoxLike.System.GibbsDecomposition
noncomputable abbrev paper_3_14_3 := @BoxLike.System.pressure_eq_pressureZ₁
noncomputable abbrev paper_3_14_4 := @BoxLike.System.pressure_eq_pressureZ₂
noncomputable abbrev paper_3_14_5 := @BoxLike.System.GibbsDecomposition.lyapunov₁_eq_integral
noncomputable abbrev paper_3_14_6 := @BoxLike.System.GibbsDecomposition.lyapunov₂_eq_integral
noncomputable abbrev paper_3_14_7 :=
  @BoxLike.System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂
noncomputable abbrev paper_3_14_8 :=
  @BoxLike.System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂
noncomputable abbrev paper_3_14_9 := @BoxLike.System.GibbsDecomposition.map_flip
noncomputable abbrev paper_3_14_10 := @BoxLike.System.decomposition₂_of_decompositions
noncomputable abbrev paper_3_14_20 := @BoxLike.System.eq_of_hasGibbsBounds
noncomputable abbrev paper_3_14_21 := @BoxLike.System.hasGibbsBounds_map_unCode
noncomputable abbrev paper_3_14_22 := @BoxLike.System.lyapunov_map_unCode_of_isGibbs
noncomputable abbrev paper_3_14_23 := @BoxLike.System.exists_isGibbs_potential₁
noncomputable abbrev paper_3_14_24 := @BoxLike.System.IsEquilibriumState.eq_map_unCode

-- PAPER_ENTRY thm:exact-dimensional-mixture
/-! 4.1 (`thm:exact-dimensional-mixture`): formalized.
The manuscript omits the proof.
-/
noncomputable abbrev paper_4_1_1 := @BoxLike.IsExactDim.ae_hasLocalDim_add_left
noncomputable abbrev paper_4_1_2 := @BoxLike.IsExactDim.ae_hasLocalDim_add_right
noncomputable abbrev paper_4_1_3 := @BoxLike.IsExactDim.isDoubleDim_add
noncomputable abbrev paper_4_1_4 := @BoxLike.IsExactDim.measure_hasLocalDim_add_left_pos
noncomputable abbrev paper_4_1_5 := @BoxLike.IsExactDim.measure_hasLocalDim_add_right_pos
noncomputable abbrev paper_4_1_6 := @BoxLike.isExactDim_add_iff

-- PAPER_ENTRY thm:feng1
/-! 4.2 (`thm:feng1`): formalized.
Both parts at the article's scope from `PlanarFengLedrappierYoung` (`paper_4_2_11`), which is
proved (`paper_4_2_12`).
-/
noncomputable abbrev paper_4_2_1 := @BoxLike.planar_feng1
noncomputable abbrev paper_4_2_2 := @BoxLike.PlanarSystem.feng1
noncomputable abbrev paper_4_2_3 := @BoxLike.PlanarFengLedrappierYoung.{u}
noncomputable abbrev paper_4_2_4 := @BoxLike.PlanarFengLedrappierYoung.fengLedrappierYoung
noncomputable abbrev paper_4_2_5 := @BoxLike.planarFengLedrappierYoung_of_fengXi
noncomputable abbrev paper_4_2_6 := @BoxLike.FengLedrappierYoung.{u}
noncomputable abbrev paper_4_2_7 := @BoxLike.FengLedrappierYoungBar.{u}
noncomputable abbrev paper_4_2_8 := @BoxLike.fengLedrappierYoungBar_of_fengLedrappierYoung
noncomputable abbrev paper_4_2_9 := @BoxLike.System.isExactDim_map_projBar_of_fengLedrappierYoung
/-- `thm:feng1`, second part, from the first. -/
theorem paper_4_2_10 (h : BoxLike.PlanarFengLedrappierYoung.{u}) :
    BoxLike.FengLedrappierYoungBar.{u} :=
  BoxLike.fengLedrappierYoungBar_of_fengLedrappierYoung h.fengLedrappierYoung
open MeasureTheory BoxLike in
/-- `thm:feng1`, both parts, from `PlanarFengLedrappierYoung`. -/
theorem paper_4_2_11 (h : PlanarFengLedrappierYoung.{u}) :
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
  planar_feng1 h (paper_4_2_10 h)
noncomputable abbrev paper_4_2_12 := @BoxLike.planarFengLedrappierYoung_holds
noncomputable abbrev paper_4_2_13 := @BoxLike.fengLedrappierYoung_holds
noncomputable abbrev paper_4_2_14 := @BoxLike.fengLedrappierYoungBar_holds

-- PAPER_ENTRY thm:entropy_eq_gibbs
/-! 4.3 (`thm:entropy_eq_gibbs`): formalized.
The endpoint states the conditional-past entropies, through `PastEntropy`.
-/
noncomputable abbrev paper_4_3_1 := @BoxLike.System.GibbsDecomposition.dimEntropy_zero_eq_gibbs
noncomputable abbrev paper_4_3_2 := @BoxLike.System.GibbsDecomposition.dimEntropy_zero_eq_gibbs
noncomputable abbrev paper_4_3_3 := @BoxLike.System.GibbsDecomposition.zero_entropy_identities
noncomputable abbrev paper_4_3_4 := @BoxLike.System.GibbsDecomposition.entropy_eq₁
noncomputable abbrev paper_4_3_5 := @BoxLike.System.GibbsDecomposition.entropy_eq₂
noncomputable abbrev paper_4_3_6 := @BoxLike.entropy_map_unCode
noncomputable abbrev paper_4_3_7 := @BoxLike.System.dimEntropy_zero_eq_entropy'
noncomputable abbrev paper_4_3_8 := @BoxLike.System.dimEntropyBar_zero_eq_entropy'

-- PAPER_ENTRY thm:eq_state_proj_dim
/-! 4.4 (`thm:eq_state_proj_dim`): formalized.
For every `s > 0` and every `s`-equilibrium state; for `s ≥ 2` through the orientation lift of
the Bernoulli state.
-/
noncomputable abbrev paper_4_4_1 := @BoxLike.System.eq_state_proj_dim_all
noncomputable abbrev paper_4_4_2 := @BoxLike.System.eq_state_proj_dim_of_two_le
noncomputable abbrev paper_4_4_3 := @BoxLike.System.isExactDim_marginal_of_two_le
noncomputable abbrev paper_4_4_4 := @BoxLike.System.IsEquilibriumState.lyapunov_eq_of_two_le
noncomputable abbrev paper_4_4_5 :=
  @BoxLike.System.IsEquilibriumState.ergodic_orientationLift_of_two_le
noncomputable abbrev paper_4_4_6 := @BoxLike.ergodic_orientationLift_bernoulli
noncomputable abbrev paper_4_4_7 := @BoxLike.tendsto_orientationLift_bernoulli_cylinder_inter
noncomputable abbrev paper_4_4_8 := @BoxLike.orientationLift_bernoulli_cylinder
noncomputable abbrev paper_4_4_9 := @BoxLike.entropy_orientationLift
noncomputable abbrev paper_4_4_10 := @BoxLike.System.lyapunov_eq_of_ergodic_orientationLift
noncomputable abbrev paper_4_4_11 := @BoxLike.System.map_projBar_orientationLift
noncomputable abbrev paper_4_4_12 := @BoxLike.System.eq_state_proj_dim
noncomputable abbrev paper_4_4_13 := @BoxLike.System.marginal_decomposition
noncomputable abbrev paper_4_4_14 := @BoxLike.System.marginal_decomposition_normalised

-- PAPER_ENTRY ex:projection_double_dimensional
/-! 4.5 (`ex:projection_double_dimensional`): formalized.
For every `0 < s₂ < s₁ ≤ 1`. The Markov measure is identified by Gibbs uniqueness.
-/
noncomputable abbrev paper_4_5_1 := @BoxLike.PrescribedExample.projection_double_dimensional
noncomputable abbrev paper_4_5_2 :=
  @BoxLike.PrescribedExample.projection_double_dimensional_of_geometry
noncomputable abbrev paper_4_5_3 := @BoxLike.PrescribedExample.equilibrium_spec
noncomputable abbrev paper_4_5_4 := @BoxLike.PrescribedExample.Gibbs.isEquilibriumState_spec
noncomputable abbrev paper_4_5_5 := @BoxLike.PrescribedExample.Gibbs.isEquilibriumState_ratios
noncomputable abbrev paper_4_5_6 := @BoxLike.PrescribedExample.Gibbs.marginal_spec
noncomputable abbrev paper_4_5_7 := @BoxLike.PrescribedExample.Gibbs.GibbsDecomposition.eq_markov
noncomputable abbrev paper_4_5_8 := @BoxLike.PrescribedExample.Gibbs.markov_cylinder_eq_Q
noncomputable abbrev paper_4_5_9 := @BoxLike.PrescribedExample.exists_geometry
noncomputable abbrev paper_4_5_10 := @BoxLike.PrescribedExample.existsUnique_p
noncomputable abbrev paper_4_5_11 := @BoxLike.PrescribedExample.pressure_eq
noncomputable abbrev paper_4_5_12 := @BoxLike.PrescribedExample.exists_translation
noncomputable abbrev paper_4_5_13 := @BoxLike.PrescribedExample.volume_badSet_le

-- PAPER_ENTRY thm:gibbs_tau_omega_positive
/-! 4.6 (`thm:gibbs_tau_omega_positive`): formalized.
-/
noncomputable abbrev paper_4_6_1 := @BoxLike.System.gibbs_tau_omega_positive

-- PAPER_ENTRY thm:conditional_two_ways
/-! 4.7 (`thm:conditional_two_ways`): formalized.
-/
noncomputable abbrev paper_4_7_1 := @BoxLike.System.conditional_two_ways_normalised
noncomputable abbrev paper_4_7_2 := @BoxLike.System.conditional_two_ways_normalised_case
noncomputable abbrev paper_4_7_3 := @BoxLike.System.normalised_orientation_restrictions
noncomputable abbrev paper_4_7_4 := @BoxLike.condMeas_map_of_ae_mem
noncomputable abbrev paper_4_7_5 := @BoxLike.System.conditional_two_ways
noncomputable abbrev paper_4_7_6 := @BoxLike.System.conditional_two_ways_aux
noncomputable abbrev paper_4_7_7 := @BoxLike.condMeas_transport

-- PAPER_ENTRY thm:overline_h1_zero
/-! 4.8 (`thm:overline_h1_zero`): formalized.
Feng–Hu is not used: Jordan–Rapaport gives exact-dimensionality.
-/
noncomputable abbrev paper_4_8_1 := @BoxLike.System.overline_h1_zero

-- PAPER_ENTRY thm:overline_h1_zero_large
/-! 4.9 (`thm:overline_h1_zero_large`): formalized.
Takes `entropy μ ≤ -λ₂` only.
-/
noncomputable abbrev paper_4_9_1 := @BoxLike.System.overline_h1_zero_large

-- PAPER_ENTRY thm:overline_h1_large
/-! 4.10 (`thm:overline_h1_large`): formalized.
-/
noncomputable abbrev paper_4_10_1 := @BoxLike.System.overline_h1_large

-- PAPER_ENTRY thm:eq_state_h1_zero
/-! 4.11 (`thm:eq_state_h1_zero`): formalized.
Stated on all sequences, since `Σ'` is conull.
-/
noncomputable abbrev paper_4_11_1 := @BoxLike.System.eq_state_h1_zero

-- PAPER_ENTRY thm:eq_state_h1_large
/-! 4.12 (`thm:eq_state_h1_large`): formalized.
-/
noncomputable abbrev paper_4_12_1 := @BoxLike.System.eq_state_h1_large

-- PAPER_ENTRY thm:eq_state_h2_zero
/-! 4.13 (`thm:eq_state_h2_zero`): formalized.
-/
noncomputable abbrev paper_4_13_1 := @BoxLike.System.eq_state_h2_zero

-- PAPER_ENTRY thm:orto_partition_dirac
/-! 4.14 (`thm:orto_partition_dirac`): formalized.
Takes `entropy μ ≤ -λ₂` only.
-/
noncomputable abbrev paper_4_14_1 := @BoxLike.System.orto_partition_dirac

-- PAPER_ENTRY thm:SOSC_h2_zero
/-! 4.15 (`thm:SOSC_h2_zero`): formalized.
Takes ergodicity, which holds for every equilibrium state of a tuple with rotations.
-/
noncomputable abbrev paper_4_15_1 := @BoxLike.System.SOSC_h2_zero

-- PAPER_ENTRY thm:main_extended
/-! 4.16 (`thm:main_extended`): formalized.
For every `s`; for `s ≥ 2` the equilibrium state is Bernoulli and the open set condition gives
dimension two.
-/
noncomputable abbrev paper_4_16_1 := @BoxLike.System.main_extended_min
noncomputable abbrev paper_4_16_2 := @BoxLike.System.main_extended
noncomputable abbrev paper_4_16_3 := @BoxLike.System.main_extended_normalised
noncomputable abbrev paper_4_16_4 := @BoxLike.System.main_extended_ge_two

/-! ## Unnumbered claims

Rossi's bound `eq:hausdorff_ergodic_lyapunov` (tex lines 2728 to 2731), proved by a covering
argument; equality holds for the equilibrium state of `thm:main_extended`.
-/
/-- Rossi's bound `eq:hausdorff_ergodic_lyapunov` for every box-like system. -/
theorem prose_rossi_0 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : BoxLike.System ι) : S.RossiBound :=
  S.rossiBound
noncomputable abbrev prose_rossi_1 := @BoxLike.System.RossiBound
noncomputable abbrev prose_rossi_2 := @BoxLike.System.ae_lowerLocalDim_map_proj_le
noncomputable abbrev prose_rossi_3 := @BoxLike.System.essSup_lowerLocalDim_map_proj_le
noncomputable abbrev prose_rossi_4 := @BoxLike.System.exists_dimH_le_of_add_energy_neg
noncomputable abbrev prose_rossi_5 := @BoxLike.System.ae_tendsto_log_norm_matWord
noncomputable abbrev prose_rossi_6 := @BoxLike.System.ae_tendsto_log_alpha₂_matWord
noncomputable abbrev prose_rossi_7 := @BoxLike.ae_lowerLocalDim_le_of_dimH_le
noncomputable abbrev prose_rossi_8 := @BoxLike.System.upperHausdorffDim_map_proj_eq

/-! The squeeze `dimmaff(X) = dimaff(X)` of tex lines 548 to 550, from the first part of
`thm:fraser`.
-/
/-- If `dim_H X = dimaff(X)`, then `dimmaff(X) = dimaff(X)` (tex lines 548 to 550). -/
theorem prose_squeeze_0 {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι)
    (hH : dimH S.attractor = ENNReal.ofReal S.dimaff) : S.dimmaff = S.dimaff :=
  S.dimmaff_eq_dimaff S.fraserBound_holds hH

end Solution.Paper
