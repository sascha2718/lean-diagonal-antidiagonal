/-
The literature theorems behind the results off the main line, as axioms: Fraser's dimension
theorem for box-like self-affine sets and the condensation theorem of Bárány and Käenmäki. Both
concern objects that the modules `BoxLike/FraserChain.lean` and `BoxLike/NoOverlapExample.lean`
define, which is why they are declared here and not in `BoxLike/Literature.lean`. No main result
depends on them. The rules of `PLAN.md`, "Fidelity boundary", apply, and every axiom lists its
instance arguments in its own signature.

* `fraserBound`, `fraserROSC`: Fraser, Nonlinearity 25 (2012), Theorem 2.3 (numbering of
  arXiv:1108.2639v1), in the two parts of `thm:fraser`.
* `baranyKaenmakiTheorem`: Bárány–Käenmäki, Adv. Math. 379 (2021), Theorem 2.1 (numbering of
  arXiv:1910.04623v4), in `prop:ssc_no_overlap_not_pesc`.

The consequences that the article states are derived here without hypotheses:

* `System.fraser_packingDim_eq`, `System.fraser_upperBoxDim_le_dimmaff`: `thm:fraser`, first
  part.
* `System.dimmaff_eq_dimaff_of_dimH`, `System.dimmaff_eq_dimaff_main2'`: the squeeze of tex
  lines 578 to 581.
* `System.dim_eq_dimaff_of_rectangularOpenSet`: `thm:fraser`, third part.
* `NoOverlap.exists_system_ssc_not_pesc`, `NoOverlap.exists_system_planar_not_pesc`:
  `prop:ssc_no_overlap_not_pesc` and the paragraph after its proof.
-/
import BoxLike.FraserChain
import BoxLike.NoOverlapExample

namespace BoxLike

open MeasureTheory Matrix

/-- Fraser, Theorem 2.3, first part: for a box-like self-affine set,
`\dim_P X = \overline{\dim}_M X ≤ dimmaff(X)`, with no separation condition. -/
axiom fraserBound {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) : S.FraserBound

/-- Fraser, Theorem 2.3, second part: under the rectangular open set condition the packing and
the Minkowski dimensions of a box-like self-affine set exist and equal `dimmaff(X)`. -/
axiom fraserROSC {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) : S.FraserROSC

/-- Bárány–Käenmäki, Theorem 2.1: for every monotone decreasing sequence `(η_n)` of positive
numbers with `n⁻¹ log η_n → -∞` the set of pairs `(λ, t)` with `0 < λ < 1/3`,
`0 < t < λ/(1-λ)`, free homogeneous system and `Δ_n^{λ,t} < η_n` for all `n ≥ 1` is
uncountable. -/
axiom baranyKaenmakiTheorem : NoOverlap.BaranyKaenmakiTheorem

namespace System

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)

/-- `thm:fraser`, first part: `\dim_P X = \overline{\dim}_M X`. This equality holds for every
box-like self-affine set without Fraser's theorem (`System.packingDim_attractor`). -/
theorem fraser_packingDim_eq : packingDim S.attractor = upperBoxDim S.attractor :=
  (fraserBound S).1

/-- `thm:fraser`, first part: `\overline{\dim}_M X ≤ dimmaff(X)`. -/
theorem fraser_upperBoxDim_le_dimmaff :
    upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff := (fraserBound S).2

/-- `thm:fraser`, second part: under the rectangular open set condition the packing dimension,
the lower and the upper Minkowski dimensions of `X` all equal `dimmaff(X)`. -/
theorem dim_eq_dimaff_of_rectangularOpenSet (hrosc : S.RectangularOpenSet) :
    packingDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimmaff := fraserROSC S hrosc

variable {S}

/-- The squeeze of tex lines 578 to 581: if `\dim_H X = dimaff(X)`, then `dimmaff(X)` is
squeezed between the Minkowski dimension and the affinity dimension, so
`dimmaff(X) = dimaff(X)`. Neither the rectangular open set condition nor full projections are
assumed. -/
theorem dimmaff_eq_dimaff_of_dimH (hH : dimH S.attractor = ENNReal.ofReal S.dimaff) :
    S.dimmaff = S.dimaff := dimmaff_eq_dimaff (fraserBound S) hH

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The squeeze of tex lines 578 to 581 under the hypotheses of `thm:main2`:
`dimmaff(X) = dimaff(X)`. -/
theorem dimmaff_eq_dimaff_main2' (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    S.dimmaff = S.dimaff :=
  dimmaff_eq_dimaff_main2 (fraserBound S) hrot hprox hsep h2 μ hinv heq hor

end System

namespace NoOverlap

/-- `prop:ssc_no_overlap_not_pesc`: there is a system of four maps, three diagonal and one
anti-diagonal, that is proximal and irreducible but not strongly irreducible, whose linear
parts preserve the union of the coordinate axes, which has a diagonal generator with entries of
distinct moduli, which satisfies the strong separation condition and whose projective system
generates a free semigroup, and which fails the projective exponential separation condition. -/
theorem exists_system_ssc_not_pesc :
    ∃ S : System (Fin 4), S.o = ![0, 0, 0, 1] ∧ S.Proximal ∧ S.Irreducible ∧
      ¬ TupleStronglyIrreducible S.mat ∧
      (∀ i (v : Fin 2 → ℝ), v 0 = 0 ∨ v 1 = 0 → (S.mat i *ᵥ v) 0 = 0 ∨ (S.mat i *ᵥ v) 1 = 0) ∧
      (∃ i₀, S.o i₀ = 0 ∧ |S.a i₀| ≠ |S.b i₀|) ∧
      S.StrongSeparation ∧ S.FreeProjective ∧ ¬ S.ProjExpSeparation :=
  ssc_no_overlap_not_pesc' baranyKaenmakiTheorem

/-- The paragraph after `prop:ssc_no_overlap_not_pesc` (tex lines 1583 to 1595): exponential
separation of the planar maps does not imply the projective one. The system of the proposition
satisfies the strong separation condition, so distinct words of length `n` have images at
distance at least `δ r^{n-1}`, and it fails the projective exponential separation condition. -/
theorem exists_system_planar_not_pesc :
    ∃ S : System (Fin 4), S.StrongSeparation ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ w w' : List (Fin 4), w.length = w'.length →
        w ≠ w' → ∀ x ∈ S.attractor, ∀ y ∈ S.attractor,
          δ * S.minSingular ^ (w.length - 1) ≤ dist (S.phiWord w x) (S.phiWord w' y)) ∧
      ¬ S.ProjExpSeparation ∧ ¬ TupleStronglyIrreducible S.mat := by
  obtain ⟨S, -, -, -, hsi, -, -, hsep, -, hpesc⟩ := exists_system_ssc_not_pesc
  exact ⟨S, hsep, hsep.exists_le_dist_phiWord, hpesc, hsi⟩

end NoOverlap

end BoxLike
