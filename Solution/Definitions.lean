module

public import Mathlib

@[expose] public section

/-!
# The challenge vocabulary

The definitions of `Challenge.lean`, repeated so that the solution does not import it. The
definition block must stay identical to that of `Challenge.lean`.
-/

namespace Challenge

universe u

/-! ## The two-sided shift and the codings -/

section Shift

open Finset

variable {ι : Type*}

/-- The left shift `σ^n` (`sec:two_sided_shift_space`). -/
def shift (n : ℤ) (x : ℤ → ι) : ℤ → ι := fun k => x (n + k)

/-- The orientation cocycle `ε_n`, counting anti-diagonal symbols modulo two (`eq:def_of_eps_mod2`). -/
def eps (o : ι → ZMod 2) (x : ℤ → ι) : ℤ → ZMod 2
  | Int.ofNat n => ∑ j ∈ range n, o (x j)
  | Int.negSucc n => ∑ j ∈ range (n + 1), o (x (-(j + 1 : ℤ)))

end Shift

section Coding

variable {ι : Type*} (o : ι → ZMod 2)

/-- The coding `τ` of `eq:def_of_tau_omega`: `τ_n(𝐢) = i_n + N ε_n(𝐢)`. -/
def tau (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n)

/-- The coding `ω` of `eq:def_of_tau_omega`: `ω_n(𝐢) = i_n + N (1 - ε_n(𝐢))`. -/
def omega (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n + 1)

end Coding

/-! ## Box-like systems and the projective system -/

section Systems

open Matrix

/-- Diagonal for `c = 0`, anti-diagonal for `c = 1`, with row entries `a`, `b`. -/
def boxMat (c : ZMod 2) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if c = 0 then !![a, 0; 0, b] else !![0, a; b, 0]

/-- A contractive, invertible box-like affine system (`sec:projective_system`). -/
structure System (ι : Type*) where
  /-- The orientation: `0` for a diagonal linear part, `1` for an anti-diagonal one. -/
  o : ι → ZMod 2
  /-- The non-zero entry `a_i` of the first row of `A_i`. -/
  a : ι → ℝ
  /-- The non-zero entry `b_i` of the second row of `A_i`. -/
  b : ι → ℝ
  /-- The translation part `v_i = (v_i^{(1)}, v_i^{(2)})`. -/
  v : ι → ℝ × ℝ
  /-- `a_i ≠ 0`. -/
  a_ne_zero : ∀ i, a i ≠ 0
  /-- `b_i ≠ 0`. -/
  b_ne_zero : ∀ i, b i ≠ 0
  /-- `|a_i| < 1`. -/
  abs_a_lt_one : ∀ i, |a i| < 1
  /-- `|b_i| < 1`. -/
  abs_b_lt_one : ∀ i, |b i| < 1

namespace System

variable {ι : Type*} (S : System ι)

/-- Both diagonal and anti-diagonal generators occur (`thm:box_like_sa`). -/
def WithRotations : Prop := (∃ i, S.o i = 0) ∧ ∃ i, S.o i = 1

/-- The linear part `A_i`. -/
def mat (i : ι) : Matrix (Fin 2) (Fin 2) ℝ := boxMat (S.o i) (S.a i) (S.b i)

/-- The coordinate `proj_x` for `c = 0` and `proj_y` for `c = 1`. -/
def coord (c : ZMod 2) (z : ℝ × ℝ) : ℝ := if c = 0 then z.1 else z.2

/-- The contraction ratio of the projective map indexed by `(i, c)`. -/
def ratio (p : ι × ZMod 2) : ℝ := if p.2 = 0 then S.a p.1 else S.b p.1

/-- The translation of the projective map indexed by `(i, c)`. -/
def trans (p : ι × ZMod 2) : ℝ := coord p.2 (S.v p.1)

/-- The maps `g_j` of the projective system `Ψ` of `eq:def_of_g_system`. -/
def g (p : ι × ZMod 2) (t : ℝ) : ℝ := S.ratio p * t + S.trans p

/-- The affine map `φ_i(z) = A_i z + v_i`. -/
def phi (i : ι) (z : ℝ × ℝ) : ℝ × ℝ :=
  (S.a i * coord (S.o i) z + (S.v i).1, S.b i * coord (S.o i + 1) z + (S.v i).2)

/-- The product `A_𝐢 = A_{i_0} ⋯ A_{i_{n-1}}`. -/
def matWord (w : List ι) : Matrix (Fin 2) (Fin 2) ℝ := (w.map S.mat).prod

/-- The derivative `g_𝐣'` of `g_𝐣 = g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}`, a constant. -/
def gDeriv (u : List (ι × ZMod 2)) : ℝ := (u.map S.ratio).prod

end System

end Systems

/-! ## The singular value pressure and the affinity dimension -/

section SingularValue

open scoped Matrix.Norms.L2Operator

/-- The singular value function `φ^s`, using the Euclidean operator norm (`sec:Singular_value_function`). -/
noncomputable def svf (s : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  if s ≤ 1 then ‖A‖ ^ s
  else if s ≤ 2 then ‖A‖ ^ (2 - s) * |A.det| ^ (s - 1)
  else |A.det| ^ (s / 2)

end SingularValue

section Pressure

namespace System

variable {ι : Type*} (S : System ι) [Fintype ι]

/-- The sum `∑_{|𝐢| = n} φ^s(A_𝐢)` of `sec:affinity_dim`. -/
noncomputable def svfSum (s : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, svf s (S.matWord (List.ofFn w))

/-- The singular value pressure `P(𝖠, s)` of `sec:affinity_dim`. -/
noncomputable def pressure (s : ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (S.svfSum s n) / n) '' Set.Ici 1)

end System

end Pressure

/-! ## Projective exponential separation -/

section Separation

open scoped ENNReal

namespace System

variable {ι : Type*} (S : System ι)

/-- The composition `g_𝐣 = g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}` of `sec:exponential_separation`. -/
def gWord : List (ι × ZMod 2) → ℝ → ℝ
  | [] => id
  | p :: u => S.g p ∘ gWord u

/-- The projective gap `Δ_n^Ψ` between equal-derivative words; an empty infimum is `∞`. -/
noncomputable def gap (n : ℕ) : ℝ≥0∞ :=
  ⨅ (u : List (ι × ZMod 2)) (u' : List (ι × ZMod 2)) (_ : u.length = n) (_ : u'.length = n)
    (_ : u ≠ u') (_ : S.gDeriv u = S.gDeriv u'), ENNReal.ofReal |S.gWord u 0 - S.gWord u' 0|

/-- Projective exponential separation (`sec:exponential_separation`). -/
def ProjExpSeparation : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (c ^ n k) ≤ S.gap (n k)

/-- No exact overlaps among all finite projective words (`sec:exponential_separation`). -/
def NoExactOverlaps : Prop := ∀ u u' : List (ι × ZMod 2), u ≠ u' → S.gWord u ≠ S.gWord u'

end System

end Separation

/-! ## The canonical projections and the self-affine set -/

section Projection

/-- The prefix `𝐢|_n = i_0 ⋯ i_{n-1}` of a two-sided sequence. -/
def futureWord {α : Type*} (x : ℤ → α) (n : ℕ) : List α :=
  (List.range n).map fun k : ℕ => x (k : ℤ)

namespace System

variable {ι : Type*} (S : System ι)

/-- The `k`-th term `g'_{𝐣|_k} g_{j_k}(0)` of the series defining `\overline{π}(𝐣)`. -/
def projBarTerm (y : ℤ → ι × ZMod 2) (k : ℕ) : ℝ := S.gDeriv (futureWord y k) * S.trans (y k)

/-- The canonical projection `\overline{π}` on all projective sequences (`sec:projective_system`). -/
noncomputable def projBar (y : ℤ → ι × ZMod 2) : ℝ := ∑' k, S.projBarTerm y k

/-- The canonical projection `π`, expressed through its two coordinates (`eq:canonical_projection`). -/
noncomputable def proj (x : ℤ → ι) : ℝ × ℝ :=
  (S.projBar (tau S.o x), S.projBar (omega S.o x))

/-- The self-affine set `X = π(Σ)`. -/
def attractor : Set (ℝ × ℝ) := Set.range S.proj

end System

end Projection

section Affinity

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

open Classical in
/-- The non-negative zero of the pressure, with default value `0` (`sec:affinity_dim`). -/
noncomputable def dimaff : ℝ :=
  if h : ∃! s, 0 ≤ s ∧ S.pressure s = 0 then h.exists.choose else 0

end System

end Affinity

/-! ## Proximality and the strong open set condition -/

section Proximal

open Matrix

/-- Two real eigenvalues of different absolute values (`sec:irreducibility`). -/
def IsProximalMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ l₁ l₂ : ℝ, |l₁| ≠ |l₂| ∧
    A.charpoly = (Polynomial.X - Polynomial.C l₁) * (Polynomial.X - Polynomial.C l₂)

namespace System

variable {ι : Type*}

/-- Some non-empty product is proximal (`sec:irreducibility`). -/
def Proximal (S : System ι) : Prop :=
  ∃ w : List ι, w ≠ [] ∧ IsProximalMatrix (S.matWord w)

end System

end Proximal

section SeparationConditions

namespace System

variable {ι : Type*} (S : System ι)

/-- The strong open set condition (`sec:box_like_self_affine`). -/
def StrongOpenSet : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (U ∩ S.attractor).Nonempty ∧ (∀ i, S.phi i '' U ⊆ U) ∧
    Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)

end System

end SeparationConditions

/-! ## Cylinders and the Kolmogorov–Sinai entropy -/

section Cylinder

variable {α : Type*}

/-- The cylinder `[w] = {x : x_0 ⋯ x_{n-1} = w}` of `sec:two_sided_shift_space`. -/
def cylinder {α : Type*} {n : ℕ} (w : Fin n → α) : Set (ℤ → α) :=
  {x | ∀ k : Fin n, x (k : ℤ) = w k}

end Cylinder

section Entropy

open Filter MeasureTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α]

/-- The entropy `H_μ(𝒫_0^{n-1})` of the partition into cylinders of length `n`. -/
noncomputable def blockEntropy (μ : Measure (ℤ → α)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, Real.negMulLog (μ.real (cylinder w))

/-- The Kolmogorov–Sinai entropy `h(μ) = lim_n H_μ(𝒫_0^{n-1}) / n`. -/
noncomputable def entropy (μ : Measure (ℤ → α)) : ℝ :=
  limUnder atTop fun n : ℕ => blockEntropy μ n / n

end Entropy

/-! ## Pointwise dimensions of measures -/

section MeasureDim

open MeasureTheory Filter Topology Metric

/-- Pointwise dimension `d`, using closed balls and `Real.log 0 = 0` (`sec:ledrappier_young_formula`). -/
def HasLocalDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) (d : ℝ) : Prop :=
  Tendsto (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 d)

/-- Pointwise dimension equals `d` almost everywhere (`sec:ledrappier_young_formula`). -/
def IsExactDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d

/-- Pointwise dimension equals `d₁` or `d₂` almost everywhere (`sec:ledrappier_young_formula`). -/
def IsDoubleDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d₁ d₂ : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d₁ ∨ HasLocalDim μ x d₂

end MeasureDim

/-! ## Lyapunov exponents and equilibrium states -/

section Thermodynamic

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [MeasurableSpace ι]

namespace System

variable (S : System ι)

/-- The larger Lyapunov exponent `λ_1(𝖠, μ)` (`sec:lyapunov_exponents`). -/
noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n

/-- The smaller Lyapunov exponent `λ_2(𝖠, μ)` (`sec:lyapunov_exponents`). -/
noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n

/-- The `s`-energy `Λ(𝖠, μ, s)` (`eq:energy_def`). -/
noncomputable def energyLim (s : ℝ) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) / n

/-- `μ` is an `s`-equilibrium state, `eq:eq_state_def`: `P(𝖠, s) = h_0(μ) + Λ(𝖠, μ, s)`. -/
def IsEquilibriumState [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  S.pressure s = entropy μ + S.energyLim s μ

/-- The coordinate marginal of `π_*μ`, with `c = 0` for `x` and `c = 1` for `y`. -/
noncomputable def marginal (c : ZMod 2) (μ : Measure (ℤ → ι)) : Measure ℝ :=
  (μ.map S.proj).map (coord c)

end System

end Thermodynamic

end Challenge
