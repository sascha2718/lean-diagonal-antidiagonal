module

/-
PROPOSAL FOR THE PROJECT OWNER'S REVIEW. This file is not part of the authorised literature
boundary, nothing outside `BoxLike/Proposals/` imports it, and every result in it that takes
`FengLedrappierYoungBarScalar` is conditional on an unauthorised premise. The certified proof of
`thm:main2` along the prose (`BoxLike/MainTwoProse/Endpoint.lean`) does not use it: the scalar
Ledrappier–Young formula for the diagonal subsystems is derived there from the authorised planar
statement `FengLedrappierYoung` (`BoxLike/MainTwoProse/ScalarFeng.lean`).

The proof of `thm:main2` (tex lines 3716 to 3721) cites Feng, Theorems 1.2 and 1.3, for the
coordinate projections of the finite diagonal subsystems `Φ_n`. The authorised scalar statement
`FengLedrappierYoungBar` transcribes the second part of `thm:feng1`, which the article states for
proximal box-like systems with rotations; a diagonal subsystem has no rotation, so the authorised
statement does not apply to it. The premise below is Feng's theorem in dimension one for the
projective system `Ψ` of an arbitrary box-like system, without the hypotheses `WithRotations` and
`Proximal`; it implies `FengLedrappierYoungBar`
(`FengLedrappierYoungBarScalar.fengLedrappierYoungBar`).

* `FengLedrappierYoungBarScalar`: Feng, Theorems 1.2 and 1.3, for `d = 1` and the system `Ψ`.
* `FengLedrappierYoungBarScalar.fengLedrappierYoungBar`: the authorised statement is a
  specialisation.
* `System.IsHomDiag.measurePreserving_map_tau`, `…ergodic_map_tau`, `…map_tau_subshift_compl`,
  `…map_projBar_map_tau`, `…lyapBar_map_tau`: the coded measure `τ_*ν` of a diagonal system.
* `System.IsHomDiag.marginal_zero_isExactDim_scalar`: the scalar formula for the horizontal
  marginal of a diagonal system, conditional.
-/
public import BoxLike.HomogeneousSubsystem
public import BoxLike.LiteratureFeng
public import BoxLike.MainTwoProse.DiagonalSubsystem

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- **Proposed literature premise, not authorised.** Feng, Theorems 1.2 and 1.3, in dimension
one, for the projective system `Ψ = (g_j)_{j ∈ ι × ZMod 2}` of an arbitrary box-like system: if
`ν` is an ergodic invariant probability measure carried by `Σ_Z`, then `\overline{π}_*ν` is
exact-dimensional with
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`.

Source. D.-J. Feng, *Dimension of invariant measures for affine iterated function systems*,
Duke Math. J. 172 (2023), arXiv:1901.01691v2, Theorems 1.2 and 1.3; the authorised transcription
`FengLedrappierYoungBar` records the comparison with arXiv v2 (2026-09-20). The manuscript cites
the theorems for the diagonal subsystems at tex lines 3716 to 3721.

Source hypotheses. An affine iterated function system `S_j(x) = M_j x + a_j` on `ℝ^d` with
invertible contracting `M_j`, and an ergodic shift-invariant probability measure `m` on the
one-sided full shift; then `π_*m` is exact-dimensional (Theorem 1.2) and its dimension is given
by the Ledrappier–Young formula with the projection entropies of the transversal partitions
(Theorem 1.3). No separation condition, no irreducibility and no relation between the maps is
assumed.

Specialisation. `d = 1`; the maps `g_j(t) = r_j t + t_j`, `0 < |r_j| < 1`, of `Ψ` over the
alphabet `ι × ZMod 2`; `ν` on the two-sided shift, restricted to the non-negative coordinates;
the single Lyapunov exponent `\overline{λ}(𝖠, ν) = ∫ log |r_{j_0}| dν`, and the entropies
`\overline{h}_0`, `\overline{h}_1` of the partitions `\overline{ξ}_0`, `\overline{ξ}_1` by the past
and by the past and `\overline{π}`; the hypothesis that `ν` is carried by `Σ_Z` restricts the
statement and is harmless. The reductions are those recorded for `FengLedrappierYoungBar`; the
statement differs from it only by dropping `S.WithRotations` and `S.Proximal`, which the source
does not assume.

Degenerate instances. One symbol and the Dirac mass on a constant sequence: `\overline{π}_*ν` is a
Dirac mass of dimension `0`, both entropies vanish, and the formula gives `0`. All translations
zero: `\overline{π}_*ν = δ_0`, the partition `\overline{ξ}_1` equals `\overline{ξ}_0` up to the
null atom, and the formula gives `0`. `\overline{λ}(𝖠, ν) < 0` always, so the quotient is not a
junk value of a division by zero. -/
def FengLedrappierYoungBarScalar : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    MeasurePreserving (shift 1) ν ν → Ergodic (shift 1) ν → ν (subshift S.o)ᶜ = 0 →
    IsExactDim (ν.map S.projBar)
      ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν)

/-- The authorised `FengLedrappierYoungBar` is the specialisation of the proposed premise to
proximal box-like systems with rotations. -/
theorem FengLedrappierYoungBarScalar.fengLedrappierYoungBar
    (h : FengLedrappierYoungBarScalar.{u}) : FengLedrappierYoungBar.{u} :=
  fun S _ _ ν _ hinv herg hsupp => h S ν hinv herg hsupp

namespace System.IsHomDiag

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

omit [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- `τ ∘ σ = σ ∘ τ` for a diagonal system: no orientation changes. -/
theorem tau_comp_shift : tau T.o ∘ shift 1 = shift 1 ∘ tau T.o := by
  funext x
  exact tau_shift_of_eps_eq_zero (hT.eps_eq_zero x 1)

/-- `τ_*ν` is invariant for every invariant `ν`. -/
theorem measurePreserving_map_tau {ν : Measure (ℤ → κ)} (hinv : MeasurePreserving (shift 1) ν ν) :
    MeasurePreserving (shift 1) (ν.map (tau T.o)) (ν.map (tau T.o)) := by
  refine ⟨measurable_shift 1, ?_⟩
  rw [Measure.map_map (measurable_shift 1) (measurable_tau T.o), ← hT.tau_comp_shift,
    ← Measure.map_map (measurable_tau T.o) (measurable_shift 1), hinv.map_eq]

/-- `τ_*ν` is ergodic for every ergodic `ν`. -/
theorem ergodic_map_tau {ν : Measure (ℤ → κ)} (herg : Ergodic (shift 1) ν) :
    Ergodic (shift 1) (ν.map (tau T.o)) :=
  ergodic_of_ae_semiconj herg (hT.measurePreserving_map_tau herg.toMeasurePreserving)
    ⟨measurable_tau T.o, rfl⟩ (Filter.Eventually.of_forall fun x => congrFun hT.tau_comp_shift x)

omit hT in
/-- `τ_*ν` is carried by `Σ_Z`. -/
theorem map_tau_subshift_compl (ν : Measure (ℤ → κ)) : ν.map (tau T.o) (subshift T.o)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_tau T.o) (measurableSet_subshift T.o).compl]
  exact measure_mono_null (fun x hx => (hx (tau_mem_subshift x)).elim) measure_empty

omit hT in
/-- `\overline{π}_*(τ_*ν)` is the horizontal marginal of `ν` (`eq:commutative_diagram`). -/
theorem map_projBar_map_tau (ν : Measure (ℤ → κ)) :
    (ν.map (tau T.o)).map T.projBar = T.marginal 0 ν := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  rw [Measure.map_map hS.measurable_projBar (measurable_tau T.o), T.marginal_eq_map hS]
  rfl

/-- `\overline{λ}(𝖠, τ_*ν) = log |a|` for every probability measure `ν`. -/
theorem lyapBar_map_tau (ν : Measure (ℤ → κ)) [IsProbabilityMeasure ν] :
    T.lyapBar (ν.map (tau T.o)) = Real.log |a| := by
  have hmeas : Measurable fun y : ℤ → κ × ZMod 2 => Real.log |T.ratio (y 0)| :=
    (Measurable.of_discrete (f := fun p : κ × ZMod 2 => Real.log |T.ratio p|)).comp
      (measurable_pi_apply 0)
  rw [lyapBar, integral_map (measurable_tau T.o).aemeasurable hmeas.aestronglyMeasurable]
  simp only [hT.tau_eq, hT.ratio_eq, ite_true, integral_const, probReal_univ, one_smul]

/-- The scalar Ledrappier–Young formula for the horizontal marginal of a diagonal system,
conditional on the proposed premise: `dim (proj_x)_*(π_*ν) = (\overline{h}_1(τ_*ν) -
\overline{h}_0(τ_*ν)) / log |a|` for every ergodic invariant `ν`. This is the form in which the
proof of `thm:main2` cites Feng, before the identification of `\overline{h}_1(τ_*ν)` with the
planar entropy `h_1(ν)`.
**Conditional on the unauthorised premise `FengLedrappierYoungBarScalar`.** -/
theorem marginal_zero_isExactDim_scalar (h : FengLedrappierYoungBarScalar.{u})
    {ν : Measure (ℤ → κ)} [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν) :
    IsExactDim (T.marginal 0 ν)
      ((T.dimEntropyBar (ν.map (tau T.o)) 1 - T.dimEntropyBar (ν.map (tau T.o)) 0) /
        Real.log |a|) := by
  have hLY := h T (ν.map (tau T.o)) (hT.measurePreserving_map_tau herg.toMeasurePreserving)
    (hT.ergodic_map_tau herg) (map_tau_subshift_compl ν)
  rwa [map_projBar_map_tau, hT.lyapBar_map_tau] at hLY

end System.IsHomDiag

end BoxLike
