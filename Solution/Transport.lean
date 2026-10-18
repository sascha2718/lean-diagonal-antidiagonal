module

public import Solution.Extras
public import BoxLike

@[expose] public section

/-!
# Transport between the challenge vocabulary and the library

`toLib` and `ofLib` identify a `Challenge.System` with the `BoxLike.System` carrying the same
data. Every challenge notion that the three headline statements and the internal supporting statements use agrees with its library
namesake on the identified system. Most agreements hold by `rfl`. The structurally recursive
`pastWord` and `gWord` agree by induction, since the elaborator does not unfold their recursors
at a variable, and the notions built on them (`HasBackRate`, `Σ'`, `ξ_i`, `h_i`, the projective
gap) follow by rewriting. The challenge `dimaff` takes no `[Nonempty ι]` and chooses a zero of
the pressure when a unique one exists; `dimaff_eq` identifies it with the library's under
`[Nonempty ι]`. Each cited theorem in the challenge vocabulary implies its library statement.
-/

open MeasureTheory

universe u

namespace Solution.Transport

/-! ## Systems -/

section Systems

variable {ι : Type*}

/-- The library system with the data of a challenge system. -/
def toLib (S : Challenge.System ι) : BoxLike.System ι :=
  ⟨S.o, S.a, S.b, S.v, S.a_ne_zero, S.b_ne_zero, S.abs_a_lt_one, S.abs_b_lt_one⟩

/-- The challenge system with the data of a library system. -/
def ofLib (S : BoxLike.System ι) : Challenge.System ι :=
  ⟨S.o, S.a, S.b, S.v, S.a_ne_zero, S.b_ne_zero, S.abs_a_lt_one, S.abs_b_lt_one⟩

theorem toLib_ofLib (S : BoxLike.System ι) : toLib (ofLib S) = S := rfl

theorem ofLib_toLib (S : Challenge.System ι) : ofLib (toLib S) = S := rfl

end Systems

/-! ## The notions of the audited statements -/

section Notions

variable {ι : Type*}

theorem shift_eq (n : ℤ) : (Challenge.shift n : (ℤ → ι) → ℤ → ι) = BoxLike.shift n := rfl

theorem entropy_eq {α : Type*} [Fintype α] [MeasurableSpace α] (μ : Measure (ℤ → α)) :
    Challenge.entropy μ = BoxLike.entropy μ := rfl

theorem isExactDim_iff {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X)
    (d : ℝ) : Challenge.IsExactDim μ d ↔ BoxLike.IsExactDim μ d := Iff.rfl

theorem isDoubleDim_iff {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X)
    (d₁ d₂ : ℝ) : Challenge.IsDoubleDim μ d₁ d₂ ↔ BoxLike.IsDoubleDim μ d₁ d₂ := Iff.rfl

theorem upperPackingDim_eq {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : Challenge.upperPackingDim μ = BoxLike.upperPackingDim μ := rfl

theorem lowerHausdorffDim_eq {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : Challenge.lowerHausdorffDim μ = BoxLike.lowerHausdorffDim μ := rfl

/-- The composition of similarities, by induction on the word. -/
theorem simWord_eq {κ : Type*} (r t : κ → ℝ) : Challenge.simWord r t = BoxLike.simWord r t := by
  funext u
  induction u with
  | nil => rfl
  | cons j u ih => exact congrArg ((fun x => r j * x + t j) ∘ ·) ih

/-- `pastWord`, by induction on the length. -/
theorem pastWord_eq {α : Type*} (x : ℤ → α) : Challenge.pastWord x = BoxLike.pastWord x := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (x (-((n : ℤ) + 1)) :: ·) ih

variable (S : Challenge.System ι)

theorem withRotations_iff : S.WithRotations ↔ (toLib S).WithRotations := Iff.rfl

theorem proximal_iff : S.Proximal ↔ (toLib S).Proximal := Iff.rfl

/-- `g_𝐣(t)`, by induction on the word. -/
theorem gWord_eq (u : List (ι × ZMod 2)) (t : ℝ) : S.gWord u t = (toLib S).gWord u t := by
  induction u generalizing t with
  | nil => rfl
  | cons p u ih =>
    change S.g p (S.gWord u t) = (toLib S).g p ((toLib S).gWord u t)
    rw [ih]
    rfl

theorem gap_eq (n : ℕ) : S.gap n = (toLib S).gap n := by
  simp only [Challenge.System.gap, gWord_eq]
  rfl

theorem projExpSeparation_iff : S.ProjExpSeparation ↔ (toLib S).ProjExpSeparation := by
  simp only [Challenge.System.ProjExpSeparation, gap_eq]
  rfl

theorem noExactOverlaps_iff : S.NoExactOverlaps ↔ (toLib S).NoExactOverlaps := by
  simp only [Challenge.System.NoExactOverlaps, BoxLike.System.NoExactOverlaps]
  constructor
  · intro h u u' hne heq
    exact h u u' hne (by funext t; rw [gWord_eq, gWord_eq, heq])
  · intro h u u' hne heq
    exact h u u' hne (by funext t; rw [← gWord_eq, ← gWord_eq, heq])

theorem strongOpenSet_iff : S.StrongOpenSet ↔ (toLib S).StrongOpenSet := Iff.rfl

theorem proj_eq : S.proj = (toLib S).proj := rfl

theorem attractor_eq : S.attractor = (toLib S).attractor := rfl

theorem marginal_eq [MeasurableSpace ι] (c : ZMod 2) (μ : Measure (ℤ → ι)) :
    S.marginal c μ = (toLib S).marginal c μ := rfl

theorem lyapunov₁_eq [MeasurableSpace ι] (μ : Measure (ℤ → ι)) :
    S.lyapunov₁ μ = (toLib S).lyapunov₁ μ := rfl

theorem lyapunov₂_eq [MeasurableSpace ι] (μ : Measure (ℤ → ι)) :
    S.lyapunov₂ μ = (toLib S).lyapunov₂ μ := rfl

theorem pressure_eq [Fintype ι] (s : ℝ) : S.pressure s = (toLib S).pressure s := rfl

theorem isEquilibriumState_iff [Fintype ι] [MeasurableSpace ι] (s : ℝ) (μ : Measure (ℤ → ι)) :
    S.IsEquilibriumState s μ ↔ (toLib S).IsEquilibriumState s μ := Iff.rfl

/-- The two affinity dimensions agree for a non-empty alphabet, where the pressure has a unique
zero on `[0, ∞)`. -/
theorem dimaff_eq [Fintype ι] [Nonempty ι] : S.dimaff = (toLib S).dimaff := by
  have h : ∃! s, 0 ≤ s ∧ S.pressure s = 0 := (toLib S).existsUnique_pressure_eq_zero
  rw [Challenge.System.dimaff, dite_eq_left h]
  rfl

end Notions

/-! ## The partitions `ξ_i` and the entropies `h_i` -/

section Partitions

variable {ι : Type*} (S : Challenge.System ι)

theorem hasBackRate_iff (y : ℤ → ι × ZMod 2) (l : ℝ) :
    S.HasBackRate y l ↔ (toLib S).HasBackRate y l := by
  rw [Challenge.System.HasBackRate, pastWord_eq]
  rfl

variable [MeasurableSpace ι] (μ : Measure (ℤ → ι))

theorem sigmaTau_eq : S.SigmaTau μ = (toLib S).SigmaTau μ := by
  simp only [Challenge.System.SigmaTau, hasBackRate_iff]
  rfl

theorem sigmaOmega_eq : S.SigmaOmega μ = (toLib S).SigmaOmega μ := by
  simp only [Challenge.System.SigmaOmega, hasBackRate_iff]
  rfl

theorem sigmaPrime_eq : S.SigmaPrime μ = (toLib S).SigmaPrime μ := by
  rw [Challenge.System.SigmaPrime, sigmaTau_eq, sigmaOmega_eq]
  rfl

theorem slowAxis_eq (x : ℤ → ι) : S.slowAxis μ x = (toLib S).slowAxis μ x := by
  rw [Challenge.System.slowAxis, sigmaTau_eq]
  rfl

theorem oseledets_eq (x : ℤ → ι) (i : ℕ) : S.oseledets μ x i = (toLib S).oseledets μ x i := by
  rcases i with _ | _ | i
  · rfl
  · change {v | Challenge.System.coord (S.slowAxis μ x + 1) v = 0} = _
    rw [slowAxis_eq]
    rfl
  · rfl

theorem xi_eq (i : ℕ) : S.xi μ i = (toLib S).xi μ i := by
  simp only [Challenge.System.xi, sigmaPrime_eq, oseledets_eq]
  rfl

theorem dimEntropy_eq [Fintype ι] [MeasurableSingletonClass ι] [IsFiniteMeasure μ] (i : ℕ) :
    S.dimEntropy μ i = (toLib S).dimEntropy μ i := by
  rw [Challenge.System.dimEntropy, xi_eq]
  rfl

end Partitions

/-! ## The cited theorems -/

section Literature

/-- Morris–Shmerkin, `eq:simple_lyapunov`. -/
theorem morrisShmerkinLyapunov (h : Challenge.MorrisShmerkinLyapunov.{u}) :
    BoxLike.MorrisShmerkinLyapunov.{u} := by
  intro ι _ _ _ S hrot hdiag s hs0 hs2 μ _ hinv heq
  exact h (ofLib S) hrot hdiag hs0 hs2 μ hinv heq

/-- Feng–Käenmäki, the Gibbs bounds of `thm:irred_eq_state`. -/
theorem fengKaenmakiGibbs (h : Challenge.FengKaenmakiGibbs.{u}) :
    BoxLike.FengKaenmakiGibbs.{u} := by
  intro ι _ _ _ S hirr s hs0 hs2 μ _ hinv heq
  exact h (ofLib S) hirr hs0 hs2 μ hinv heq

/-- Jordan–Rapaport, the dimension of `\overline{π}_*ν`. -/
theorem jordanRapaportDimension (h : Challenge.JordanRapaportDimension.{u}) :
    BoxLike.JordanRapaportDimension.{u} := by
  intro ι _ _ _ S hsep ν _ herg
  exact h (ofLib S) ((projExpSeparation_iff _).2 hsep) ν herg

/-- Kittle–Kogler, the dimension of self-similar measures without exact overlaps. -/
theorem kittleKoglerDimension (h : Challenge.KittleKoglerDimension.{u}) :
    BoxLike.KittleKoglerDimension.{u} := by
  intro κ _ r t p hr hr1 hp hsum hfree ν _ hν
  exact h r t p hr hr1 hp hsum (by rwa [simWord_eq]) ν hν

/-- Feng, the Ledrappier–Young formula `eq:feng1_1` for `π_*μ`. -/
theorem fengLedrappierYoung (h : Challenge.FengLedrappierYoung.{u}) :
    BoxLike.FengLedrappierYoung.{u} := by
  intro ι _ _ _ S μ _ hinv herg hl
  have key := h (ofLib S) μ hinv herg hl
  simp only [dimEntropy_eq] at key
  exact key

/-- Feng, the Ledrappier–Young formula for `\overline{π}_*ν`. -/
theorem fengLedrappierYoungBar (h : Challenge.FengLedrappierYoungBar.{u}) :
    BoxLike.FengLedrappierYoungBar.{u} := by
  intro ι _ _ _ S hrot hprox ν _ hinv herg hsupp
  exact h (ofLib S) hrot hprox ν hinv herg hsupp

end Literature

end Solution.Transport
