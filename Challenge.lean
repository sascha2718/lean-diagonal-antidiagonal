module

public import Mathlib

@[expose] public section

/-!
# Hausdorff dimension of planar box-like self-affine sets with rotations

Three headline statements from D. Allen, A. Käenmäki, R. D. Prokaj, K. Simon and S. Troscheit,
*Hausdorff dimension of planar box-like self-affine sets with rotations*: Theorems 1.2, 1.3,
and 4.16. Theorem and equation numbers refer to the manuscript; the doc
comments also give the labels of its LaTeX source, such as `thm:main1` or `sec:affinity_dim`.

The statements and their vocabulary use Mathlib alone. The symbolic space is the two-sided shift
`Σ = ℤ → ι` over a finite alphabet `ι` with the discrete `σ`-algebra
(`MeasurableSingletonClass ι`), and `shift n` is the iterate `σ^n` of the left shift. A box-like
system is a `System ι`: the linear part `A_i` of its `i`-th map is diagonal or anti-diagonal
with non-zero entries `a_i`, `b_i ∈ (-1, 1)`, and its translation part is `v_i`. The plane is
`ℝ × ℝ`, whose Mathlib metric is the supremum norm; pointwise dimensions use its closed balls.
Measures on `Σ` are Borel probability measures invariant under `shift 1`, that is
`IsProbabilityMeasure μ` and `MeasurePreserving (shift 1) μ μ`, and ergodicity is
`Ergodic (shift 1) μ`. The projective system of the coordinate projections is coded by
sequences in `ℤ → ι × ZMod 2`.

The paper's notation reads as follows: `X = π(Σ)` is `S.attractor` with `π = S.proj`,
`dimaff(X)` is `S.dimaff`, `P(𝖠, s)` is `S.pressure s`, `h_0(μ)` is `entropy μ`,
`λ_1(𝖠, μ)` and `λ_2(𝖠, μ)` are `S.lyapunov₁ μ` and `S.lyapunov₂ μ`, the coordinate
projections `(proj_x)_*(π_*μ)` and `(proj_y)_*(π_*μ)` are `S.marginal 0 μ` and
`S.marginal 1 μ`, and `dim_H` is Mathlib's Hausdorff dimension `dimH`, with values in `ℝ≥0∞`.

These three statements use six named literature hypotheses. They are the `Prop`s of the
section "Cited theorems", stated about the objects defined here, with the exact citations in
their doc comments. The headline theorems take them as explicit hypotheses.
-/

namespace Challenge

universe u

/-! ## The two-sided shift and the codings -/

section Shift

open Finset

variable {ι : Type*}

/-- The iterate `σ^n`, `n ∈ ℤ`, of the left shift of `sec:two_sided_shift_space`:
`(σ^n 𝐢)_k = i_{n+k}`. -/
def shift (n : ℤ) (x : ℤ → ι) : ℤ → ι := fun k => x (n + k)

/-- The orientation cocycle `ε_n(𝐢)` of `eq:def_of_eps_mod2`: the parity of the number of
anti-diagonal symbols among `i_0, …, i_{n-1}` when `n ≥ 0`, and among `i_{-1}, …, i_n`
when `n < 0`. -/
def eps (o : ι → ZMod 2) (x : ℤ → ι) : ℤ → ZMod 2
  | Int.ofNat n => ∑ j ∈ range n, o (x j)
  | Int.negSucc n => ∑ j ∈ range (n + 1), o (x (-(j + 1 : ℤ)))

end Shift

section Coding

variable {ι : Type*} (o : ι → ZMod 2)

/-- The transition rule of the matrix `Z` of `sec:subshift`: the symbol `(i, c)` may be
followed by `(j, c')` exactly when `c' = c + o(i)`. -/
def Trans (p q : ι × ZMod 2) : Prop := q.2 = p.2 + o p.1

/-- The two-sided sub-shift of finite type `Σ_Z` of `sec:subshift`. -/
def subshift : Set (ℤ → ι × ZMod 2) := {y | ∀ n, Trans o (y n) (y (n + 1))}

/-- The coding `τ` of `eq:def_of_tau_omega`: `τ_n(𝐢) = i_n + N ε_n(𝐢)`. -/
def tau (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n)

/-- The coding `ω` of `eq:def_of_tau_omega`: `ω_n(𝐢) = i_n + N (1 - ε_n(𝐢))`. -/
def omega (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n + 1)


end Coding

/-! ## Box-like systems and the projective system -/

section Systems

open Matrix

/-- The diagonal matrix `diag(a, b)` for `c = 0` and the anti-diagonal matrix with
first-row entry `a` and second-row entry `b` for `c = 1`. -/
def boxMat (c : ZMod 2) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if c = 0 then !![a, 0; 0, b] else !![0, a; b, 0]

/-- A planar box-like affine iterated function system in box-like coordinates, as in
`sec:subshift` and `sec:projective_system`: the linear part of the `i`-th map is
`diag(a_i, b_i)` when `o i = 0` and the anti-diagonal matrix with first-row entry `a_i` and
second-row entry `b_i` when `o i = 1`; the translation part is `v_i`. -/
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

/-- The system is box-like with rotations: both diagonal and anti-diagonal linear parts
occur, as in `thm:box_like_sa`. -/
def WithRotations : Prop := (∃ i, S.o i = 0) ∧ ∃ i, S.o i = 1

/-- The normalisation of `sec:gibbs_measures`: some diagonal generator has entries of distinct
absolute values, that is, the tuple contains a proximal diagonal generator. -/
def HasProximalDiagonal : Prop := ∃ i, S.o i = 0 ∧ |S.a i| ≠ |S.b i|

/-- The linear part `A_i`. -/
def mat (i : ι) : Matrix (Fin 2) (Fin 2) ℝ := boxMat (S.o i) (S.a i) (S.b i)

/-- The coordinate `proj_x` for `c = 0` and `proj_y` for `c = 1`. -/
def coord (c : ZMod 2) (z : ℝ × ℝ) : ℝ := if c = 0 then z.1 else z.2

/-- The contraction ratio `g_j'` of the projective system: `a_i` for the symbol `(i, 0)`
and `b_i` for the symbol `(i, 1)`. -/
def ratio (p : ι × ZMod 2) : ℝ := if p.2 = 0 then S.a p.1 else S.b p.1

/-- The translation `g_j(0)` of the projective system: `v_i^{(1)}` for the symbol `(i, 0)`
and `v_i^{(2)}` for the symbol `(i, 1)`. -/
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

/-- The word `i_{-n} ⋯ i_{-1}` of the past of `𝐢`. -/
def pastWord {α : Type*} (x : ℤ → α) : ℕ → List α
  | 0 => []
  | n + 1 => x (-((n : ℤ) + 1)) :: pastWord x n

end Systems

/-! ## The singular value pressure and the affinity dimension -/

section SingularValue

open scoped Matrix.Norms.L2Operator

/-- The singular value function `φ^s(A)` of `sec:Singular_value_function`, with
`‖A‖ = α_1(A)` the `ℓ²` operator norm and `|det A| = α_1(A) α_2(A)`. -/
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

/-- The projective gap `Δ_n^Ψ`: the least `|g_𝐢(0) - g_𝐣(0)|` over distinct words `𝐢, 𝐣` of
length `n` with `g_𝐢' = g_𝐣'`. The minimum of the empty set is `⊤`. -/
noncomputable def gap (n : ℕ) : ℝ≥0∞ :=
  ⨅ (u : List (ι × ZMod 2)) (u' : List (ι × ZMod 2)) (_ : u.length = n) (_ : u'.length = n)
    (_ : u ≠ u') (_ : S.gDeriv u = S.gDeriv u'), ENNReal.ofReal |S.gWord u 0 - S.gWord u' 0|

/-- The projective exponential separation condition of `sec:exponential_separation`: there
are `c > 0` and a strictly increasing sequence `(n_k)` with `Δ_{n_k}^Ψ ≥ c^{n_k}`. -/
def ProjExpSeparation : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (c ^ n k) ≤ S.gap (n k)

/-- The projective system has no exact overlaps (`sec:exponential_separation`): `g_𝐢 ≠ g_𝐣` for
any two distinct finite words `𝐢`, `𝐣` over the alphabet of `Ψ`, that is, the maps of `Ψ`
generate a free semigroup. The separation hypothesis of `thm:main2`. -/
def NoExactOverlaps : Prop := ∀ u u' : List (ι × ZMod 2), u ≠ u' → S.gWord u ≠ S.gWord u'

end System

/-- The composition `g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}` of the similarities `g_j(x) = r_j x + t_j` of
the line indexed by `κ`; the maps of a self-similar system on `ℝ` generate a free semigroup
exactly when this composition is injective. -/
def simWord {κ : Type*} (r t : κ → ℝ) : List κ → ℝ → ℝ
  | [] => id
  | j :: u => (fun x => r j * x + t j) ∘ simWord r t u

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

/-- The canonical projection `\overline{π}` of `sec:projective_system`. It is defined on every
sequence over `ι × ZMod 2`, in particular on `Σ_Z`. -/
noncomputable def projBar (y : ℤ → ι × ZMod 2) : ℝ := ∑' k, S.projBarTerm y k

/-- The canonical projection `π` of `sec:two_sided_shift_space`, given through its
coordinates `π(𝐢) = (\overline{π}(τ(𝐢)), \overline{π}(ω(𝐢)))`; it is the limit of
`eq:canonical_projection`. -/
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
/-- The affinity dimension `dimaff(𝖠)` of `sec:affinity_dim`: the unique `s ≥ 0` for which
`P(𝖠, s) = 0`. For a non-empty alphabet such an `s` exists and is unique, since `s ↦ P(𝖠, s)`
is continuous and strictly decreasing with `P(𝖠, 0) = log N ≥ 0` and `P(𝖠, s) → -∞`; the
value `0` otherwise is a convention. -/
noncomputable def dimaff : ℝ :=
  if h : ∃! s, 0 ≤ s ∧ S.pressure s = 0 then h.exists.choose else 0

end System

end Affinity

/-! ## Proximality, irreducibility and the strong open set condition -/

section Proximal

open Matrix

/-- A `2 × 2` real matrix is proximal, as in `sec:irreducibility`, if it has two real
eigenvalues with different absolute values. The eigenvalues are stated through the
characteristic polynomial: it is the product of `X - l₁` and `X - l₂` with `|l₁| ≠ |l₂|`.
The paper states the definition for `A ∈ GL_2(ℝ)`; the products `A_𝐢` of a `System` are
invertible. -/
def IsProximalMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ l₁ l₂ : ℝ, |l₁| ≠ |l₂| ∧
    A.charpoly = (Polynomial.X - Polynomial.C l₁) * (Polynomial.X - Polynomial.C l₂)

namespace System

variable {ι : Type*}

/-- The tuple `𝖠` is proximal, as in `sec:irreducibility`: the semigroup generated by `𝖠`
contains a proximal matrix, that is, some product `A_𝐢` over a non-empty word is proximal. -/
def Proximal (S : System ι) : Prop :=
  ∃ w : List ι, w ≠ [] ∧ IsProximalMatrix (S.matWord w)

/-- The tuple `𝖠` is irreducible (`sec:irreducibility`): no line through the origin is
invariant under every `A_i`, that is, the matrices have no common eigenvector. -/
def Irreducible (S : System ι) : Prop :=
  ¬ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, ∃ c : ℝ, S.mat i *ᵥ v = c • v

end System

end Proximal

section SeparationConditions

namespace System

variable {ι : Type*} (S : System ι)

/-- The strong open set condition of `sec:box_like_self_affine`: there is an open set `U` with
`U ∩ X ≠ ∅`, `⋃_i φ_i(U) ⊆ U`, and `φ_i(U) ∩ φ_j(U) = ∅` whenever `i ≠ j`. -/
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

/-! ## Measurable partitions, conditional measures and conditional entropy -/

section Partition

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*}

open Classical in
/-- A partition of a subset `D` of `Ω`, given by its atom map `ξ`, extended to a partition of
`Ω` by the single extra atom `Ω ∖ D`. The paper's partitions `ξ_i`, `ξ_1^⊥` live on the
full-measure set `Σ'` and `\overline{ξ}_i` on `Σ_Z` (`sec:entropies`); the conditional measures
of a measure on `Σ` or on `{1, …, 2N}^ℤ` giving full mass to `D` do not see the extra atom. -/
def atomsOn (D : Set Ω) (ξ : Ω → Set Ω) (x : Ω) : Set Ω :=
  if x ∈ D then ξ x ∩ D else Dᶜ

/-- The `σ`-algebra `\widehat{ξ}` of a partition `ξ` given by its atom map (`sec:conditional`;
Feng, Section 2.1): the Borel sets that are unions of atoms. A set `A` is saturated when
`x ∈ A ↔ y ∈ A` for all `y ∈ ξ(x)`; for an atom map of a partition this says that `A` is a union
of atoms, and in this form the sets form a `σ`-algebra for every map `ξ`. -/
@[implicit_reducible]
def saturated [m : MeasurableSpace Ω] (ξ : Ω → Set Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[m] A ∧ ∀ x y, y ∈ ξ x → (x ∈ A ↔ y ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun x y h => not_congr (hA.2 x y h)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun n => (hf n).1, fun x y h => by
    rw [mem_iUnion, mem_iUnion]
    exact exists_congr fun n => (hf n).2 x y h⟩

variable [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The conditional measure `μ_x^ξ` of `sec:conditional`: the value at `x` of Mathlib's regular
conditional probability kernel of `μ` given `\widehat{ξ}`. It needs a standard Borel space `Ω`
and a finite measure `μ`. The kernel is `\widehat{ξ}`-measurable and satisfies
`∫_B μ_x^ξ(A) dμ(x) = μ(A ∩ B)` for `B ∈ \widehat{ξ}` by construction; it is determined up to a
`μ`-null set of points `x`. -/
noncomputable def condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) (x : Ω) :
    Measure Ω :=
  condExpKernel μ (saturated ξ) x

end Partition

section ShiftEntropy

open MeasureTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The conditional information `I_μ(𝒫 | \widehat{ξ})(x) = -log E_μ(1_{[x_0]} | \widehat{ξ})(x)`
of the canonical partition `𝒫 = {[i]}` given `\widehat{ξ}` (`sec:conditional`), with the
conditional expectation realised by the kernel: `-log μ_x^ξ([x_0])`. The value is non-negative.
Where `μ_x^ξ([x_0]) = 0` Lean gives `0` and the paper `+∞`; this happens on a `μ`-null set
(Feng, Lemma 2.2). -/
noncomputable def condInfo (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : ℝ :=
  -Real.log ((condMeas μ ξ x).real {y | y 0 = x 0})

/-- The conditional entropy `H_μ(𝒫 | \widehat{ξ}) = ∫ I_μ(𝒫 | \widehat{ξ}) dμ`
(`sec:conditional`). -/
noncomputable def condEntropy (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : ℝ :=
  ∫ x, condInfo μ ξ x ∂μ

end ShiftEntropy

/-! ## Pointwise dimensions of measures -/

section MeasureDim

open MeasureTheory Filter Topology Metric

/-- The pointwise dimension of `μ` at `x` exists and equals `d`, that is `dimloc(μ, x) = d`:
the quotient `log μ(B(x, r)) / log r` tends to `d` as `r ↓ 0`. The balls are closed. At a point
`x` with `μ(B(x, r)) = 0` for small `r`, the convention `Real.log 0 = 0` gives
`dimloc(μ, x) = 0`; such points lie outside the support of `μ`. -/
def HasLocalDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) (d : ℝ) : Prop :=
  Tendsto (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 d)

/-- The measure `μ` is exact-dimensional with `dim μ = d`: `dimloc(μ, x) = d` for `μ`-almost
every `x`. -/
def IsExactDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d

/-- The measure `μ` is double-dimensional with values `d₁`, `d₂`: for `μ`-almost every `x` the
pointwise dimension `dimloc(μ, x)` exists and equals `d₁` or `d₂`. -/
def IsDoubleDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d₁ d₂ : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d₁ ∨ HasLocalDim μ x d₂

end MeasureDim

/-! ## Lyapunov exponents, equilibrium states and Gibbs measures -/

section Thermodynamic

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [MeasurableSpace ι]

namespace System

variable (S : System ι)

/-- The Lyapunov exponent `λ_1(𝖠, μ) = lim_n n⁻¹ ∫ log α_1(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`. -/
noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n

/-- The Lyapunov exponent `λ_2(𝖠, μ) = lim_n n⁻¹ ∫ log α_2(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`, with `α_2(A) = |det A| / ‖A‖`. -/
noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n

/-- The Lyapunov exponent `\overline{λ}(𝖠, ν)` of the projective system. For an invariant
measure the limit defining it in `sec:lyapunov_exponents` is the integral
`∫ log |g'_{j_0}(0)| dν(𝐣) = ∫ f_{1,1} dν` of `thm:eq_state_is_sum`. -/
noncomputable def lyapBar (ν : Measure (ℤ → ι × ZMod 2)) : ℝ :=
  ∫ y, Real.log |S.ratio (y 0)| ∂ν

/-- The `s`-energy `Λ(𝖠, μ, s) = lim_n n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` of `eq:energy_def`, first
line. -/
noncomputable def energyLim (s : ℝ) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) / n

/-- `μ` is an `s`-equilibrium state, `eq:eq_state_def`: `P(𝖠, s) = h_0(μ) + Λ(𝖠, μ, s)`. -/
def IsEquilibriumState [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  S.pressure s = entropy μ + S.energyLim s μ

/-- The Gibbs bounds of `thm:irred_eq_state` for a measure `μ` on `Σ`:
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢 ∈ Σ_*^+`, with a constant `C ≥ 1`. -/
def HasGibbsBounds [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)))

/-- The coordinate marginals `ν_x = (proj_x)_*(π_*μ)` for `c = 0` and `ν_y = (proj_y)_*(π_*μ)`
for `c = 1` of `sec:dimension_of_projections`. -/
noncomputable def marginal (c : ZMod 2) (μ : Measure (ℤ → ι)) : Measure ℝ :=
  (μ.map S.proj).map (coord c)

end System

end Thermodynamic

/-! ## The Oseledets filtration -/

section SlowAxis

open MeasureTheory Filter Topology Set

/-- `𝐢^- = 𝐣^-`: the two sequences agree at all negative coordinates
(`sec:two_sided_shift_space`). -/
def SamePast {α : Type*} (x y : ℤ → α) : Prop := ∀ n : ℤ, n < 0 → x n = y n

namespace System

section BackRate

variable {ι : Type*} (S : System ι)

/-- The backward growth rate of `|g'|` along `𝐣 ∈ Σ_Z` exists and equals `l`:
`lim_n n⁻¹ log |g'_{j_{-n} ⋯ j_{-1}}(0)| = l`, as in `eq:lyapunov_exponent_gsystem`. By
`thm:matrix_products_g_derivatives`, for `𝐣 = τ(𝐢)` this is the growth rate of
`|A_{i_{-n}} ⋯ A_{i_{-1}} e_1|` and for `𝐣 = ω(𝐢)` that of `|A_{i_{-n}} ⋯ A_{i_{-1}} e_2|`. -/
def HasBackRate (y : ℤ → ι × ZMod 2) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log |S.gDeriv (pastWord y n)| / n) atTop (𝓝 l)

end BackRate

section Sigma

variable {ι : Type*} [MeasurableSpace ι] (S : System ι)

/-- `Σ^τ` of `eq:sigma_tau_omega`, in the box-like form of `sec:lyapunov_exponents`: the slow
subspace `V_𝐢^1` is the `y`-axis, that is, `e_1` grows backwards at the rate `λ_1(𝖠, μ)` and
`e_2` at the rate `λ_2(𝖠, μ)`. -/
noncomputable def SigmaTau (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  {x | S.HasBackRate (tau S.o x) (S.lyapunov₁ μ) ∧ S.HasBackRate (omega S.o x) (S.lyapunov₂ μ)}

/-- `Σ^ω` of `eq:sigma_tau_omega`: the slow subspace `V_𝐢^1` is the `x`-axis, that is, `e_1`
grows backwards at the rate `λ_2(𝖠, μ)` and `e_2` at the rate `λ_1(𝖠, μ)`. -/
noncomputable def SigmaOmega (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  {x | S.HasBackRate (tau S.o x) (S.lyapunov₂ μ) ∧ S.HasBackRate (omega S.o x) (S.lyapunov₁ μ)}

/-- The set `Σ'` of `sec:lyapunov_exponents` in the box-like case: "all sequences for which the
two backward coordinate growth rates exist and equal `λ_1(𝖠, μ)` and `λ_2(𝖠, μ)` in either
order". It depends on `μ` through the two exponents only. -/
noncomputable def SigmaPrime (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  S.SigmaTau μ ∪ S.SigmaOmega μ

open Classical in
/-- The slow subspace `V_𝐢^1` as a coordinate axis: `1` for the `y`-axis, on `Σ^τ`, and `0` for
the `x`-axis, on `Σ^ω`. Outside `Σ'` the value `0` is junk; when `λ_1 = λ_2` the sets `Σ^τ` and
`Σ^ω` coincide and the value is `1` on `Σ'`. -/
noncomputable def slowAxis (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ZMod 2 :=
  if x ∈ S.SigmaTau μ then 1 else 0

/-- The Oseledets filtration `ℝ² = V_𝐢^0 ⊋ V_𝐢^1 ⊋ V_𝐢^2 = {0}` of `sec:lyapunov_exponents` in
the box-like case: `V_𝐢^1` is the coordinate axis `slowAxis`, the set of vectors whose other
coordinate vanishes. Indices above `2` repeat `{0}`. -/
noncomputable def oseledets (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ℕ → Set (ℝ × ℝ)
  | 0 => univ
  | 1 => {v | coord (S.slowAxis μ x + 1) v = 0}
  | _ => {0}

end Sigma

end System

end SlowAxis

/-! ## The partitions `ξ_i` and the entropies `h_i` -/

section DimPartitions

open MeasureTheory Set

namespace System

section Planar

variable {ι : Type u} [MeasurableSpace ι] (S : System ι)

/-- The partitions `ξ_0, ξ_1, ξ_2` of `Σ'` (`sec:entropies`):
`ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ V_𝐢^i}`, extended to `Σ` by the atom `Σ ∖ Σ'`. -/
noncomputable def xi (μ : Measure (ℤ → ι)) (i : ℕ) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn (S.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ S.proj y - S.proj x ∈ S.oseledets μ x i}

end Planar

section Projective

variable {ι : Type u} (S : System ι)

/-- The partitions `\overline{ξ}_0`, `\overline{ξ}_1` of `Σ_Z` (`sec:entropies`), extended to
`{1, …, 2N}^ℤ` by the atom `{1, …, 2N}^ℤ ∖ Σ_Z`. They do not depend on a measure. Indices above
`1` repeat `\overline{ξ}_1`. -/
noncomputable def xiBar : ℕ → (ℤ → ι × ZMod 2) → Set (ℤ → ι × ZMod 2)
  | 0 => atomsOn (subshift S.o) fun y => {z | SamePast z y}
  | _ => atomsOn (subshift S.o) fun y => {z | SamePast z y ∧ S.projBar z = S.projBar y}

end Projective

section Entropies

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The `i`-dimensional entropy `h_i(μ) = H_μ(𝒫 | \widehat{ξ}_i)` (`sec:entropies`). -/
noncomputable def dimEntropy (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : ℝ :=
  condEntropy μ (S.xi μ i)

/-- The entropy `\overline{h}_i(ν) = H_ν(\overline{𝒫} | \widehat{\overline{ξ}}_i)`
(`sec:entropies`). -/
noncomputable def dimEntropyBar (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν] (i : ℕ) : ℝ :=
  condEntropy ν (S.xiBar i)

end Entropies

end System

end DimPartitions

/-! ## Cited theorems

The headlines use six theorems from the literature that the paper cites without proof. Each
is stated here as a `Prop` about the objects defined above, quantified over every finite
alphabet `ι : Type u` with the discrete `σ`-algebra and every system, with the hypotheses under
which the paper uses it; the doc comments give the exact citations and the reductions between each source and its statement. The
audited theorems take them as hypotheses.

The results of D.-J. Feng, *Dimension of invariant measures for affine iterated function
systems*, Duke Math. J. 172 (2023), arXiv:1901.01691, are used in `sec:entropies` and
`sec:ledrappier_young_formula`. Feng's set `Σ'` is an invariant Borel set of full measure on
which his properties (4.1) to (4.4) hold; it can be taken inside the paper's box-like set `Σ'`,
which is the one used here, with each partition extended to the whole shift by one null atom.
The partitions agree on a set of full measure, so their `σ`-algebras agree modulo null sets and
the conditional measures and entropies agree almost everywhere.
-/

section Literature

open MeasureTheory

/-- `eq:simple_lyapunov` for the normalised tuple. Morris–Shmerkin, Theorem 3.1: if
`A_1, …, A_M ∈ GL_2(ℝ)` have no common invariant line and one of them is hyperbolic, then for
`0 < s < 2` every equilibrium state of `φ^s` has unequal Lyapunov exponents. A diagonal
generator with `|a_i| ≠ |b_i|` is hyperbolic, and together with an anti-diagonal generator it
makes the tuple irreducible. The source works on the one-sided shift with the products
`A_{x_n} ⋯ A_{x_1}`; it applies to the transposed tuple, which has the same norms of products,
the same pressure and the same equilibrium states. -/
def MorrisShmerkinLyapunov : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.HasProximalDiagonal → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.IsEquilibriumState s μ → S.lyapunov₂ μ < S.lyapunov₁ μ

/-- The Gibbs bounds of `thm:irred_eq_state`. Feng–Käenmäki, Proposition 1.2: if a tuple of
real matrices has no common invariant proper subspace, then for each `q > 0` the
`q`-equilibrium state of the potential `‖·‖^q` satisfies
`C⁻¹ exp(-|𝐢| P(q)) ‖A_𝐢‖^q ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(q)) ‖A_𝐢‖^q`. For `0 < s ≤ 1` the singular
value function is `‖·‖^s` and `q = s`. For `1 < s < 2` and planar matrices
`φ^s(A) = |det A|^{s-1} ‖A‖^{2-s} = ‖A'‖^{2-s}` with the rescaled tuple
`A'_i = |det A_i|^{(s-1)/(2-s)} A_i`, which is irreducible when `𝖠` is, so the proposition
applies with `q = 2 - s`. The article states `thm:irred_eq_state` for every `s > 0`, with
uniqueness and ergodicity; the statement covers the range `0 < s < 2` and the Gibbs bounds,
which is what `thm:main1` uses. -/
def FengKaenmakiGibbs : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.Irreducible → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.IsEquilibriumState s μ → S.HasGibbsBounds s μ

/-- Jordan–Rapaport, Theorem 1.1, for the projective system `Ψ`: if the self-similar system
`Ψ = (g_j)` on `ℝ`, with ratios `0 < |r_j| < 1` of either sign, is exponentially separated,
which for `Ψ` is the projective exponential separation condition, and `ν` is an ergodic
shift-invariant probability measure, then `\overline{π}_*ν` is exact-dimensional with
`dim(\overline{π}_*ν) = min{1, -\overline{h}_0(ν) / \overline{λ}(𝖠, ν)}`. The source works on
the one-sided shift, with the Lyapunov exponent `∑_j ν[j] log |r_j|` and closed intervals in
the definition of exact-dimensionality. -/
def JordanRapaportDimension : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.ProjExpSeparation → ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    Ergodic (shift 1) ν → IsExactDim (ν.map S.projBar) (min 1 (-entropy ν / S.lyapBar ν))

/-- Kittle–Kogler, *The exact overlaps conjecture for self-similar measures on the real line*,
arXiv:2610.10511 (7 October 2026), Theorem 1.1, in the form the proof of `thm:main2` uses. Let
`μ = ∑_j p_j δ_{g_j}` be a probability measure on finitely many distinct contracting
similarities `g_j(x) = r_j x + t_j` of `ℝ`, with `0 < |r_j| < 1` of either sign and `p_j > 0`;
then the self-similar measure `ν`, the unique probability measure with
`∑_j p_j (g_j)_* ν = ν`, is exact-dimensional with `dim ν = min{1, h_μ / |χ_μ|}`, where `h_μ`
is the random walk entropy and `χ_μ = ∑_j p_j log |r_j|`. When the similarities generate a
free semigroup, `h_μ = H(p) = -∑_j p_j log p_j`, as the source notes; the statement takes this
hypothesis and the conclusion `dim ν = min{1, H(p) / |χ_μ|}`. Every solution of the
stationarity equation is the self-similar measure, by Hutchinson's uniqueness. -/
def KittleKoglerDimension : Prop :=
  ∀ {κ : Type u} [Fintype κ] (r t p : κ → ℝ), (∀ j, r j ≠ 0) → (∀ j, |r j| < 1) →
    (∀ j, 0 < p j) → ∑ j, p j = 1 → Function.Injective (simWord r t) →
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
    ν = ∑ j, ENNReal.ofReal (p j) • ν.map (fun x => r j * x + t j) →
    IsExactDim ν (min 1 ((∑ j, Real.negMulLog (p j)) / -(∑ j, p j * Real.log |r j|)))

/-- `thm:feng1`, first part, `eq:feng1_1`; Feng, Theorems 1.2 and 1.3, for `d = 2`
and simple Lyapunov spectrum: if `μ` is ergodic with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `π_*μ` is
exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`.
Feng works with closed Euclidean balls; `IsExactDim` on `ℝ × ℝ` uses closed balls of the
supremum norm, which gives the same pointwise dimension. -/
def FengLedrappierYoung : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    Ergodic (shift 1) μ → S.lyapunov₂ μ < S.lyapunov₁ μ →
    IsExactDim (μ.map S.proj)
      ((S.dimEntropy μ 1 - S.dimEntropy μ 0) / S.lyapunov₁ μ +
        (S.dimEntropy μ 2 - S.dimEntropy μ 1) / S.lyapunov₂ μ)

/-- `thm:feng1`, second part; Feng, Theorems 1.2 and 1.3, for the self-similar system
`Ψ` on `ℝ`: if `ν` is an ergodic invariant measure on `Σ_Z`, then `\overline{π}_*ν` is
exact-dimensional with
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`. -/
def FengLedrappierYoungBar : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.Proximal → ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    MeasurePreserving (shift 1) ν ν → Ergodic (shift 1) ν → ν (subshift S.o)ᶜ = 0 →
    IsExactDim (ν.map S.projBar)
      ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν)

end Literature

/-! ## Dimension of the projections of the equilibrium state -/

open MeasureTheory

/-- Theorem 1.2 (`thm:main1`). Let `X` be a proximal box-like self-affine set with rotations
satisfying the projective exponential separation condition, and let
`μ` be an `s`-equilibrium state for `s = dimaff(X)`. Then each coordinate projection of `μ`,
the marginal `(proj_x)_*(π_*μ)` for `c = 0` and `(proj_y)_*(π_*μ)` for `c = 1`, is
double-dimensional with the values `min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`.
It fails to be exact-dimensional, with any dimension, precisely when
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`; at equality and above it is exact-dimensional of dimension one.
The conclusion holds for every `s`-equilibrium state, so the uniqueness of the equilibrium state
in the paper is not needed. The proof uses the cited theorems of Morris–Shmerkin,
Feng–Käenmäki and Jordan–Rapaport. -/
theorem audit_main1 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) (hms : MorrisShmerkinLyapunov.{u}) (hfk : FengKaenmakiGibbs.{u})
    (hjr : JordanRapaportDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ) (c : ZMod 2) :
    IsDoubleDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔
        S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := sorry

/-! ## Dimension of the equilibrium state and of the self-affine set -/

/-- Theorem 1.3 (`thm:main2`). Let `X` be a proximal box-like self-affine set with rotations
whose projective system has no exact overlaps, and let `μ` be an
`s`-equilibrium state for `s = dimaff(X)`. If
`dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, or if `X` satisfies the strong open set condition, then
`dim_H(X) = dimaff(X)`. Any `s`-equilibrium state may serve as `μ`. The proof uses the cited
theorems of Morris–Shmerkin, Feng–Käenmäki, Feng (the planar Ledrappier–Young formula)
and Kittle–Kogler. -/
theorem audit_main2 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) (hms : MorrisShmerkinLyapunov.{u})
    (hfk : FengKaenmakiGibbs.{u})
    (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := sorry

/-- Theorem 4.16 (`thm:main_extended`). Let `X` be a proximal box-like self-affine set with
rotations satisfying the projective exponential separation condition, and let `μ` be an
`s`-equilibrium state for `s = dimaff(𝖠)`. If `h_0(μ) ≤ -λ_2(𝖠, μ)` or `X` satisfies the strong
open set condition, then `π_*μ` is exact-dimensional with `dim(π_*μ) = min{2, dimaff(𝖠)}`. The
conclusion holds for every `s`-equilibrium state, so its uniqueness in the paper is not needed.
The proof uses the cited theorems of Morris–Shmerkin, Feng–Käenmäki, Jordan–Rapaport and
Feng (the two Ledrappier–Young formulas). -/
theorem audit_main_extended {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hms : MorrisShmerkinLyapunov.{u})
    (hfk : FengKaenmakiGibbs.{u})
    (hjr : JordanRapaportDimension.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) (min 2 S.dimaff) := sorry

end Challenge
