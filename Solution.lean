module

public import Solution.Transport

@[expose] public section

/-!
# Definitions and numbered statements of the manuscript

The definitions below display the mathematical vocabulary used by the statements. A `recall`
command checks that both the displayed type and formula agree with the imported definition;
it introduces no new abbreviation. Recursive definitions are displayed through their defining
equations, checked by `rfl`. The numbered theorems follow the manuscript order and
apply the proofs in `BoxLike`. Supporting lemmas and proof comparisons are recorded in
`paper-correspondence.yaml` and `docs/correspondence.md`.

Theorem 1.1 is recorded as an unproved proposition and Question 1.4 as an open question.
Neither is an axiom. The final section proves the independent statements of `Challenge.lean`
under their existing names for the comparator.
-/

section Manuscript

open BoxLike BoxLike.System MeasureTheory ProbabilityTheory Filter Topology Set Matrix Metric Classical
open scoped ENNReal NNReal Matrix.Norms.L2Operator

universe u u_1 u_2 u_3

/-! ## Basic systems and codings -/

/-- A box-like system: orientations, row entries, translations, and invertible contractions. -/
recall BoxLike.System.mk {ι : Type u_1} (o : ι → ZMod 2) (a b : ι → ℝ) (v : ι → ℝ × ℝ) (a_ne_zero : ∀ (i : ι), a i ≠ 0)
  (b_ne_zero : ∀ (i : ι), b i ≠ 0) (abs_a_lt_one : ∀ (i : ι), |a i| < 1) (abs_b_lt_one : ∀ (i : ι), |b i| < 1) :
  System ι

/-- A planar system: invertible matrices of operator norm below one and translations. -/
recall BoxLike.PlanarSystem.mk {ι : Type u_1} (mat : ι → Matrix (Fin 2) (Fin 2) ℝ) (v : ι → ℝ × ℝ)
  (det_ne_zero : ∀ (i : ι), (mat i).det ≠ 0) (norm_lt_one : ∀ (i : ι), ‖mat i‖ < 1) : PlanarSystem ι

/-- The iterate `σ^n`, `n ∈ ℤ`, of the left shift of `sec:two_sided_shift_space`:
`(σ^n 𝐢)_k = i_{n+k}`. -/
recall BoxLike.shift {ι : Type u_1} (n : ℤ) (x : ℤ → ι) : ℤ → ι := fun k => x (n + k)

/-- The orientation cocycle `ε_n(𝐢)` of `eq:def_of_eps_mod2`: the parity of the number of
anti-diagonal symbols among `i_0, …, i_{n-1}` when `n ≥ 0`, and among `i_{-1}, …, i_n`
when `n < 0`. -/
recall BoxLike.eps {ι : Type u_1} (o : ι → ZMod 2) (x : ℤ → ι) : ℤ → ZMod 2
  | Int.ofNat n => ∑ j ∈ Finset.range n, o (x j)
  | Int.negSucc n => ∑ j ∈ Finset.range (n + 1), o (x (-(j + 1 : ℤ)))

/-- The coding `τ` of `eq:def_of_tau_omega`: `τ_n(𝐢) = i_n + N ε_n(𝐢)`. -/
recall BoxLike.tau {ι : Type u_1} (o : ι → ZMod 2) (x : ℤ → ι) : ℤ → ι × ZMod 2 :=
  fun n => (x n, eps o x n)

/-- The coding `ω` of `eq:def_of_tau_omega`: `ω_n(𝐢) = i_n + N (1 - ε_n(𝐢))`. -/
recall BoxLike.omega {ι : Type u_1} (o : ι → ZMod 2) (x : ℤ → ι) : ℤ → ι × ZMod 2 :=
  fun n => (x n, eps o x n + 1)

/-- The common inverse `\overline{τ}`, `\overline{ω}` of the codings: forget the axis. -/
recall BoxLike.unCode {ι : Type u_1} (y : ℤ → ι × ZMod 2) : ℤ → ι := fun n => (y n).1

/-- The two-sided sub-shift of finite type `Σ_Z` of `sec:subshift`. -/
recall BoxLike.subshift {ι : Type u_1} (o : ι → ZMod 2) : Set (ℤ → ι × ZMod 2) :=
  {y | ∀ n, Trans o (y n) (y (n + 1))}

/-- The diagonal matrix `diag(a, b)` for `c = 0` and the anti-diagonal matrix with
first-row entry `a` and second-row entry `b` for `c = 1`. -/
recall BoxLike.boxMat (c : ZMod 2) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if c = 0 then !![a, 0; 0, b] else !![0, a; b, 0]

/-- The system is box-like with rotations: both diagonal and anti-diagonal linear parts
occur, as in `thm:box_like_sa`. -/
recall BoxLike.System.WithRotations {ι : Type u_1} (S : System ι) : Prop :=
  (∃ i, S.o i = 0) ∧ ∃ i, S.o i = 1

/-- The normalisation of `sec:gibbs_measures`: some diagonal generator has entries of distinct
absolute values, that is, the tuple contains a proximal diagonal generator. -/
recall BoxLike.System.HasProximalDiagonal {ι : Type u_1} (S : System ι) : Prop :=
  ∃ i, S.o i = 0 ∧ |S.a i| ≠ |S.b i|

/-- The linear part `A_i`. -/
recall BoxLike.System.mat {ι : Type u_1} (S : System ι) (i : ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  boxMat (S.o i) (S.a i) (S.b i)

/-- The coordinate `proj_x` for `c = 0` and `proj_y` for `c = 1`. -/
recall BoxLike.System.coord (c : ZMod 2) (z : ℝ × ℝ) : ℝ := if c = 0 then z.1 else z.2

/-- The contraction ratio `g_j'` of the projective system: `a_i` for the symbol `(i, 0)`
and `b_i` for the symbol `(i, 1)`. -/
recall BoxLike.System.ratio {ι : Type u_1} (S : System ι) (p : ι × ZMod 2) : ℝ :=
  if p.2 = 0 then S.a p.1 else S.b p.1

/-- The translation `g_j(0)` of the projective system: `v_i^{(1)}` for the symbol `(i, 0)`
and `v_i^{(2)}` for the symbol `(i, 1)`. -/
recall BoxLike.System.trans {ι : Type u_1} (S : System ι) (p : ι × ZMod 2) : ℝ :=
  coord p.2 (S.v p.1)

/-- The maps `g_j` of the projective system `Ψ` of `eq:def_of_g_system`. -/
recall BoxLike.System.g {ι : Type u_1} (S : System ι) (p : ι × ZMod 2) (t : ℝ) : ℝ :=
  S.ratio p * t + S.trans p

/-- The affine map `φ_i(z) = A_i z + v_i`. -/
recall BoxLike.System.phi {ι : Type u_1} (S : System ι) (i : ι) (z : ℝ × ℝ) : ℝ × ℝ :=
  (S.a i * coord (S.o i) z + (S.v i).1, S.b i * coord (S.o i + 1) z + (S.v i).2)

/-- The product `A_𝐢 = A_{i_0} ⋯ A_{i_{n-1}}`. -/
recall BoxLike.System.matWord {ι : Type u_1} (S : System ι) (w : List ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  (w.map S.mat).prod

/-- The derivative `g_𝐣'` of `g_𝐣 = g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}`, a constant. -/
recall BoxLike.System.gDeriv {ι : Type u_1} (S : System ι) (u : List (ι × ZMod 2)) : ℝ :=
  (u.map S.ratio).prod

/-- The prefix `𝐢|_n = i_0 ⋯ i_{n-1}` of a two-sided sequence. -/
recall BoxLike.futureWord {α : Type u_1} (x : ℤ → α) (n : ℕ) : List α :=
  (List.range n).map fun k : ℕ => x (k : ℤ)

/-- The word `i_{-n} ⋯ i_{-1}` of the past of `𝐢`. -/
recall BoxLike.pastWord {α : Type u_1} (x : ℤ → α) : ℕ → List α
example {α : Type*} (x : ℤ → α) : pastWord x 0 = [] := rfl
example {α : Type*} (x : ℤ → α) (n : ℕ) :
    pastWord x (n + 1) = x (-((n : ℤ) + 1)) :: pastWord x n := rfl

/-- The canonical projection `\overline{π}` of `sec:projective_system`. It is defined on every
sequence over `ι × ZMod 2`, in particular on `Σ_Z`. -/
recall BoxLike.System.projBar {ι : Type u_1} (S : System ι) (y : ℤ → ι × ZMod 2) : ℝ :=
  ∑' k, S.projBarTerm y k

/-- The canonical projection `π` of `sec:two_sided_shift_space`, given through its
coordinates; `tendsto_phiWord` shows that it is the limit of `eq:canonical_projection`. -/
recall BoxLike.System.proj {ι : Type u_1} (S : System ι) (x : ℤ → ι) : ℝ × ℝ :=
  (S.projBar (tau S.o x), S.projBar (omega S.o x))

/-- The self-affine set `X = π(Σ)`. -/
recall BoxLike.System.attractor {ι : Type u_1} (S : System ι) : Set (ℝ × ℝ) := Set.range S.proj

/-! ## Pressure, separation and dimensions -/

/-- The singular value function `φ^s(A)` of `sec:Singular_value_function`, with
`‖A‖ = α_1(A)` the `ℓ²` operator norm and `|det A| = α_1(A) α_2(A)`. -/
recall BoxLike.svf (s : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := if s ≤ 1 then ‖A‖ ^ s
  else if s ≤ 2 then ‖A‖ ^ (2 - s) * |A.det| ^ (s - 1)
  else |A.det| ^ (s / 2)

/-- The sum `∑_{|𝐢| = n} φ^s(A_𝐢)` of `sec:affinity_dim`. -/
recall BoxLike.System.svfSum {ι : Type u_1} (S : System ι) [Fintype ι] (s : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, svf s (S.matWord (List.ofFn w))

/-- The singular value pressure `P(𝖠, s)` of `sec:affinity_dim`. -/
recall BoxLike.System.pressure {ι : Type u_1} (S : System ι) [Fintype ι] (s : ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (S.svfSum s n) / n) '' Set.Ici 1)

/-- The affinity dimension `dimaff(𝖠)` of `sec:affinity_dim`: the unique `s ≥ 0` for which
`P(𝖠, s) = 0`. -/
recall BoxLike.System.dimaff {ι : Type u_1} [Fintype ι] [Nonempty ι] (S : System ι) : ℝ :=
  (S.existsUnique_pressure_eq_zero).exists.choose

/-- The composition `g_𝐣 = g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}` of `sec:exponential_separation`. -/
recall BoxLike.System.gWord {ι : Type u_1} (S : System ι) : List (ι × ZMod 2) → ℝ → ℝ
example {ι : Type*} (S : System ι) : S.gWord [] = id := rfl
example {ι : Type*} (S : System ι) (p : ι × ZMod 2) (w : List (ι × ZMod 2)) :
    S.gWord (p :: w) = S.g p ∘ S.gWord w := rfl

/-- The projective gap `Δ_n^Ψ`: the least `|g_𝐢(0) - g_𝐣(0)|` over distinct words `𝐢, 𝐣` of
length `n` with `g_𝐢' = g_𝐣'`. The minimum of the empty set is `⊤`. -/
recall BoxLike.System.gap {ι : Type u_1} (S : System ι) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (u : List (ι × ZMod 2)) (u' : List (ι × ZMod 2)) (_ : u.length = n) (_ : u'.length = n)
    (_ : u ≠ u') (_ : S.gDeriv u = S.gDeriv u'), ENNReal.ofReal |S.gWord u 0 - S.gWord u' 0|

/-- The projective exponential separation condition of `sec:exponential_separation`: there
are `c > 0` and a strictly increasing sequence `(n_k)` with `Δ_{n_k}^Ψ ≥ c^{n_k}`. -/
recall BoxLike.System.ProjExpSeparation {ι : Type u_1} (S : System ι) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (c ^ n k) ≤ S.gap (n k)

/-- The projective system has no exact overlaps (`sec:exponential_separation`): `g_𝐢 ≠ g_𝐣` for
any two distinct finite words `𝐢`, `𝐣` over the alphabet of `Ψ`, that is, the maps of `Ψ`
generate a free semigroup. The separation hypothesis of `thm:main2`. -/
recall BoxLike.System.NoExactOverlaps {ι : Type u_1} (S : System ι) : Prop :=
  ∀ u u' : List (ι × ZMod 2), u ≠ u' → S.gWord u ≠ S.gWord u'

/-- A `2 × 2` real matrix is proximal, as in `sec:irreducibility`, if it has two real
eigenvalues with different absolute values. The eigenvalues are stated through the
characteristic polynomial: it is the product of `X - l₁` and `X - l₂` with `|l₁| ≠ |l₂|`.
The paper states the definition for `A ∈ GL_2(ℝ)`; the products `A_𝐢` of a `System` are
invertible. -/
recall BoxLike.IsProximalMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop := ∃ l₁ l₂ : ℝ, |l₁| ≠ |l₂| ∧
    A.charpoly = (Polynomial.X - Polynomial.C l₁) * (Polynomial.X - Polynomial.C l₂)

/-- The tuple `𝖠` is proximal, as in `sec:irreducibility`: the semigroup generated by `𝖠`
contains a proximal matrix, that is, some product `A_𝐢` over a non-empty word is proximal. -/
recall BoxLike.System.Proximal {ι : Type u_1} (S : System ι) : Prop :=
  ∃ w : List ι, w ≠ [] ∧ IsProximalMatrix (S.matWord w)

/-- The strong open set condition of `sec:box_like_self_affine`: there is an open set `U` with
`U ∩ X ≠ ∅`, `⋃_i φ_i(U) ⊆ U`, and `φ_i(U) ∩ φ_j(U) = ∅` whenever `i ≠ j`. -/
recall BoxLike.System.StrongOpenSet {ι : Type u_1} (S : System ι) : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (U ∩ S.attractor).Nonempty ∧ (∀ i, S.phi i '' U ⊆ U) ∧
    Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)

/-- The strong separation condition of `sec:box_like_self_affine`: the sets
`φ_1(X), …, φ_N(X)` are pairwise disjoint. -/
recall BoxLike.System.StrongSeparation {ι : Type u_1} (S : System ι) : Prop :=
  Pairwise fun i j => Disjoint (S.phi i '' S.attractor) (S.phi j '' S.attractor)

/-- The rectangular open set condition of `sec:box_like_self_affine`: there is a non-empty open
rectangle `R = (a, b) × (c, d)` with sides parallel to the coordinate axes such that the sets
`φ_1(R), …, φ_N(R)` are pairwise disjoint subsets of `R`. -/
recall BoxLike.System.RectangularOpenSet {ι : Type u_1} (S : System ι) : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧
    (∀ i, S.phi i '' (Set.Ioo a b ×ˢ Set.Ioo c d) ⊆ Set.Ioo a b ×ˢ Set.Ioo c d) ∧
    Pairwise fun i j => Disjoint (S.phi i '' (Set.Ioo a b ×ˢ Set.Ioo c d))
      (S.phi j '' (Set.Ioo a b ×ˢ Set.Ioo c d))

/-- The gap `Δ_n` of the system induced on the axis `c`: the least `|g_𝐢(0) - g_𝐣(0)|` over
distinct planar words `𝐢, 𝐣` of length `n` with `g_𝐢' = g_𝐣'` along the axis `c`. The minimum of
the empty set is `⊤`. -/
recall BoxLike.System.axisGap {ι : Type u_1} (S : System ι) (c : ZMod 2) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (u : List ι) (u' : List ι) (_ : u.length = n) (_ : u'.length = n) (_ : u ≠ u')
    (_ : S.gDeriv (axisWord c u) = S.gDeriv (axisWord c u')),
    ENNReal.ofReal |S.gWord (axisWord c u) 0 - S.gWord (axisWord c u') 0|

/-- The system induced on the axis `c` is exponentially separated: there are `r > 0` and a
strictly increasing sequence `(n_k)` with `Δ_{n_k} ≥ r^{n_k}`, the definition before
`thm:rapaport`. -/
recall BoxLike.System.AxisExpSeparation {ι : Type u_1} (S : System ι) (c : ZMod 2) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (r ^ n k) ≤ S.axisGap c (n k)

/-- The number `s_1` for `c = 0` and `s_2` for `c = 1` of Fraser, §2.1: the Minkowski dimension
of the coordinate projection `proj_c(X)`. It is the upper Minkowski dimension, converted to a
real number; it is finite by `projDim_le_one`, and the lower Minkowski dimension has the same
value by `lowerBoxDim_coord_eq`. -/
recall BoxLike.System.projDim {ι : Type u_1} (S : System ι) (c : ZMod 2) : ℝ :=
  (upperBoxDim (coord c '' S.attractor)).toReal

/-- Fraser's modified singular value function
`ψ^s(𝐢) = α_1(𝐢)^{s(𝐢)} α_2(𝐢)^{s - s(𝐢)}`, equation (2.1) of his article. -/
recall BoxLike.System.modSvf {ι : Type u_1} (S : System ι) (s : ℝ) (w : List ι) : ℝ :=
  S.alpha₁ w ^ S.wordDim w * S.alpha₂ w ^ (s - S.wordDim w)

/-- The modified pressure `lim_n n⁻¹ log Ψ_n^s`, the logarithm of Fraser's `P(s)`, §2.1. It is
defined as the `lim sup`; `tendsto_modPressure` shows that the limit exists. -/
recall BoxLike.System.modPressure {ι : Type u_1} (S : System ι) [Fintype ι] (s : ℝ) : ℝ :=
  limsup (fun n : ℕ => Real.log (S.modSvfSum s n) / n) atTop

/-- Fraser's modified affinity dimension `dimmaff(X)` of tex lines 2077 to 2077: the unique
`s ≥ 0` at which the modified pressure vanishes, that is, the unique solution of `P(s) = 1` in
Fraser's Theorem 2.3. It depends on the set `X` through `s_1` and `s_2`, not on the matrices
alone. -/
recall BoxLike.System.dimmaff {ι : Type u_1} (S : System ι) [Fintype ι] [Nonempty ι] : ℝ :=
  (S.existsUnique_modPressure_eq_zero).exists.choose

/-- The pointwise dimension of `μ` at `x` exists and equals `d`, that is `dimloc(μ, x) = d`:
the quotient `log μ(B(x, r)) / log r` tends to `d` as `r ↓ 0`. The balls are closed. At a point
`x` with `μ(B(x, r)) = 0` for small `r`, the convention `Real.log 0 = 0` gives
`dimloc(μ, x) = 0`; such points lie outside the support of `μ`. -/
recall BoxLike.HasLocalDim {X : Type u_1} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) (x : X) (d : ℝ) :
  Prop := Tendsto (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 d)

/-- The measure `μ` is exact-dimensional with `dim μ = d`: `dimloc(μ, x) = d` for `μ`-almost
every `x`. -/
recall BoxLike.IsExactDim {X : Type u_1} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) (d : ℝ) : Prop :=
  ∀ᵐ x ∂μ, HasLocalDim μ x d

/-- The measure `μ` is double-dimensional (`sec:ledrappier_young_formula`): its pointwise
dimension exists at `μ`-almost every point and takes exactly two values, each on a set of
positive `μ`-measure. -/
recall BoxLike.IsDoubleDim {X : Type u_1} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ (∀ᵐ x ∂μ, HasLocalDim μ x d₁ ∨ HasLocalDim μ x d₂) ∧
    0 < μ {x | HasLocalDim μ x d₁} ∧ 0 < μ {x | HasLocalDim μ x d₂}

/-- For `μ`-almost every `x` the pointwise dimension `dimloc(μ, x)` exists and equals `d₁` or
`d₂`. The article has no name for this; its double-dimensional measures are those for which,
in addition, the two values differ and each occurs on a set of positive measure
(`IsDoubleDim`). -/
recall BoxLike.HasLocalDimPair {X : Type u_1} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) (d₁ d₂ : ℝ) :
  Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d₁ ∨ HasLocalDim μ x d₂

/-- The upper packing dimension `\overline{dim}_p(μ)`: the essential supremum of the upper
pointwise dimension with respect to `μ`. The value is real. For a finite Borel measure on
`ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere, so the real-valued `essSup`
carries its usual meaning. -/
recall BoxLike.upperPackingDim {X : Type u_1} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) : ℝ :=
  essSup (upperLocalDim μ) μ

/-- The lower Hausdorff dimension `\underline{dim}_H(μ)`: the essential infimum of the lower
pointwise dimension with respect to `μ`. The value is real. For a finite Borel measure on
`ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere, so the real-valued `essInf`
carries its usual meaning. -/
recall BoxLike.lowerHausdorffDim {X : Type u_1} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) : ℝ :=
  essInf (lowerLocalDim μ) μ

/-! ## Entropy and equilibrium states -/

/-- The cylinder `[w] = {x : x_0 ⋯ x_{n-1} = w}` of `sec:two_sided_shift_space`. -/
recall BoxLike.cylinder {α : Type u_2} {n : ℕ} (w : Fin n → α) : Set (ℤ → α) :=
  {x | ∀ k : Fin n, x (k : ℤ) = w k}

/-- The block `x_0 ⋯ x_{n-1}` of a point `x`. -/
recall BoxLike.block {α : Type u_1} (n : ℕ) (x : ℤ → α) : Fin n → α := fun k => x k

/-- The entropy `H_μ(𝒫_0^{n-1})` of the partition into cylinders of length `n`. -/
recall BoxLike.blockEntropy {α : Type u_1} [Fintype α] [MeasurableSpace α] (μ : Measure (ℤ → α)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, Real.negMulLog (μ.real (cylinder w))

/-- The Kolmogorov–Sinai entropy `h(μ) = lim_n H_μ(𝒫_0^{n-1}) / n`. -/
recall BoxLike.entropy {α : Type u_1} [Fintype α] [MeasurableSpace α] (μ : Measure (ℤ → α)) : ℝ :=
  limUnder atTop fun n : ℕ => blockEntropy μ n / n

/-- The Lyapunov exponent `λ_1(𝖠, μ) = lim_n n⁻¹ ∫ log α_1(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`. -/
recall BoxLike.System.lyapunov₁ {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n

/-- The Lyapunov exponent `λ_2(𝖠, μ) = lim_n n⁻¹ ∫ log α_2(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`, with `α_2(A) = |det A| / ‖A‖`. -/
recall BoxLike.System.lyapunov₂ {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n

/-- The Lyapunov exponent `\overline{λ}(𝖠, ν)` of the projective system. For an invariant
measure the limit defining it in `sec:lyapunov_exponents` is the integral
`∫ log |g'_{j_0}(0)| dν(𝐣) = ∫ f_{1,1} dν` of `thm:eq_state_is_sum`. -/
recall BoxLike.System.lyapBar {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (ν : Measure (ℤ → ι × ZMod 2)) : ℝ :=
  ∫ y, Real.log |S.ratio (y 0)| ∂ν

/-- The `s`-energy `Λ(𝖠, μ, s) = lim_n n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` of `eq:energy_def`, first
line. -/
recall BoxLike.System.energyLim {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (s : ℝ) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) / n

/-- `μ` is an `s`-equilibrium state, `eq:eq_state_def`: `P(𝖠, s) = h_0(μ) + Λ(𝖠, μ, s)`. -/
recall BoxLike.System.IsEquilibriumState {ι : Type u_1} [MeasurableSpace ι] (S : System ι) [Fintype ι] (s : ℝ)
  (μ : Measure (ℤ → ι)) : Prop := S.pressure s = entropy μ + S.energyLim s μ

/-- The Gibbs bounds of `thm:irred_eq_state` for a measure `μ` on `Σ`:
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢 ∈ Σ_*^+`, with a constant `C ≥ 1`. -/
recall BoxLike.System.HasGibbsBounds {ι : Type u_1} [MeasurableSpace ι] (S : System ι) [Fintype ι] (s : ℝ)
  (μ : Measure (ℤ → ι)) : Prop := ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)))

/-- The coordinate marginals `ν_x = (proj_x)_*(π_*μ)` for `c = 0` and `ν_y = (proj_y)_*(π_*μ)`
for `c = 1` of `sec:dimension_of_projections`. -/
recall BoxLike.System.marginal {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (c : ZMod 2) (μ : Measure (ℤ → ι)) :
  Measure ℝ := (μ.map S.proj).map (coord c)

/-! ## Conditional measures and partitions -/

/-- `𝐢^- = 𝐣^-`: the two sequences agree at all negative coordinates
(`sec:two_sided_shift_space`, tex line 728). -/
recall BoxLike.SamePast {α : Type u_1} (x y : ℤ → α) : Prop := ∀ n : ℤ, n < 0 → x n = y n

/-- A partition of a subset `D` of `Ω`, given by its atom map `ξ`, extended to a partition of
`Ω` by the single extra atom `Ω ∖ D`. The article's partitions `ξ_i`, `ξ_1^⊥` live on the
full-measure set `Σ'` and `\overline{ξ}_i` on `Σ_Z` (`sec:entropies`, tex lines 1777 to 1788 and
1914 to 1920); the conditional measures of a measure on `Σ` or on `{1, …, 2N}^ℤ` giving full
mass to `D` do not see the extra atom. -/
recall BoxLike.atomsOn {Ω : Type u_1} (D : Set Ω) (ξ : Ω → Set Ω) (x : Ω) : Set Ω :=
  if x ∈ D then ξ x ∩ D else Dᶜ

set_option warn.classDefReducibility false in
/-- The sigma-algebra of measurable unions of atoms of the partition. -/
recall BoxLike.saturated {Ω : Type u_1} [m : MeasurableSpace Ω] (ξ : Ω → Set Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[m] A ∧ ∀ x y, y ∈ ξ x → (x ∈ A ↔ y ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun x y h => not_congr (hA.2 x y h)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun n => (hf n).1, fun x y h => by
    simp only [mem_iUnion]
    exact exists_congr fun n => (hf n).2 x y h⟩

/-- A measurable partition in the sense used by the article (`sec:conditional`, tex lines 1671
to 1750): the atoms are the fibres of a Borel map into a standard Borel space. Every standard
Borel space embeds measurably into `ℝ`, so the target is `ℝ`. -/
recall BoxLike.IsMeasurablePartition {Ω : Type u_1} [MeasurableSpace Ω] (ξ : Ω → Set Ω) : Prop :=
  ∃ f : Ω → ℝ, Measurable f ∧ ∀ x y, y ∈ ξ x ↔ f y = f x

/-- The conditional measure `μ_x^ξ` of `sec:conditional`: the value at
`x` of Mathlib's regular conditional probability kernel of `μ` given `\widehat{ξ}`. It needs a
standard Borel space `Ω` and a finite measure `μ`. The kernel is `\widehat{ξ}`-measurable and
satisfies `∫_B μ_x^ξ(A) dμ(x) = μ(A ∩ B)` for `B ∈ \widehat{ξ}` by construction; it is
determined up to a `μ`-null set of points `x`. -/
recall BoxLike.condMeas {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (ξ : Ω → Set Ω) (x : Ω) : Measure Ω := condExpKernel μ (saturated ξ) x

/-- The conditional information `I_μ(𝒫 | \widehat{ξ})(x) = -log E_μ(1_{[x_0]} | \widehat{ξ})(x)`
of the canonical partition `𝒫 = {[i]}` given `\widehat{ξ}` (`sec:conditional`, tex lines 1652 to
1734), with the conditional expectation realised by the kernel: `-log μ_x^ξ([x_0])`. The value is
non-negative. Where `μ_x^ξ([x_0]) = 0` Lean gives `0` and the article `+∞`; this happens on a
`μ`-null set (Feng, Lemma 2.2). -/
recall BoxLike.condInfo {α : Type u_1} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure (ℤ → α))
  [IsFiniteMeasure μ] (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : ℝ := -Real.log ((condMeas μ ξ x).real {y | y 0 = x 0})

/-- The conditional entropy `H_μ(𝒫 | \widehat{ξ}) = ∫ I_μ(𝒫 | \widehat{ξ}) dμ`
(`sec:conditional`, tex lines 1658 to 1662). -/
recall BoxLike.condEntropy {α : Type u_1} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] (ξ : (ℤ → α) → Set (ℤ → α)) : ℝ := ∫ x, condInfo μ ξ x ∂μ

/-- The pointwise entropy `E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)` of `sec:entropies`,
where `ℐ` is the `σ`-algebra of shift-invariant Borel sets. It is a conditional expectation and
so is determined up to a `μ`-null set; every statement about it is an almost-everywhere
statement. -/
recall BoxLike.localEntropy {α : Type u_1} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] (ξ : (ℤ → α) → Set (ℤ → α)) : (ℤ → α) → ℝ := μ[condInfo μ ξ | MeasurableSpace.invariants (shift 1 : (ℤ → α) → ℤ → α)]

/-- The backward growth rate of `|g'|` along `𝐣 ∈ Σ_Z` exists and equals `l`:
`lim_n n⁻¹ log |g'_{j_{-n} ⋯ j_{-1}}(0)| = l`, as in `eq:lyapunov_exponent_gsystem`. By
`thm:matrix_products_g_derivatives`, for `𝐣 = τ(𝐢)` this is the growth rate of
`|A_{i_{-n}} ⋯ A_{i_{-1}} e_1|` and for `𝐣 = ω(𝐢)` that of `|A_{i_{-n}} ⋯ A_{i_{-1}} e_2|`. -/
recall BoxLike.System.HasBackRate {ι : Type u_1} (S : System ι) (y : ℤ → ι × ZMod 2) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log |S.gDeriv (pastWord y n)| / n) atTop (𝓝 l)

/-- `Σ^τ` of `eq:sigma_tau_omega`, in the box-like form of `sec:lyapunov_exponents` (tex lines
1614 to 1625): the slow subspace `V_𝐢^1` is the `y`-axis, that is, `e_1` grows backwards at the
rate `λ_1(𝖠, μ)` and `e_2` at the rate `λ_2(𝖠, μ)`. -/
recall BoxLike.System.SigmaTau {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  {x | S.HasBackRate (tau S.o x) (S.lyapunov₁ μ) ∧ S.HasBackRate (omega S.o x) (S.lyapunov₂ μ)}

/-- `Σ^ω` of `eq:sigma_tau_omega`: the slow subspace `V_𝐢^1` is the `x`-axis, that is, `e_1`
grows backwards at the rate `λ_2(𝖠, μ)` and `e_2` at the rate `λ_1(𝖠, μ)`. -/
recall BoxLike.System.SigmaOmega {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  {x | S.HasBackRate (tau S.o x) (S.lyapunov₂ μ) ∧ S.HasBackRate (omega S.o x) (S.lyapunov₁ μ)}

/-- The set `Σ'` of `sec:lyapunov_exponents` in the box-like case: "all
sequences for which the two backward coordinate growth rates exist and equal `λ_1(𝖠, μ)` and
`λ_2(𝖠, μ)` in either order". It depends on `μ` through the two exponents only. -/
recall BoxLike.System.SigmaPrime {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  S.SigmaTau μ ∪ S.SigmaOmega μ

/-- The slow subspace `V_𝐢^1` as a coordinate axis: `1` for the `y`-axis, on `Σ^τ`, and `0` for
the `x`-axis, on `Σ^ω`. Outside `Σ'` the value `0` is junk; when `λ_1 = λ_2` the sets `Σ^τ` and
`Σ^ω` coincide and the value is `1` on `Σ'`. -/
recall BoxLike.System.slowAxis {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
  ZMod 2 := if x ∈ S.SigmaTau μ then 1 else 0

/-- The Oseledets filtration `ℝ² = V_𝐢^0 ⊋ V_𝐢^1 ⊋ V_𝐢^2 = {0}` of `sec:lyapunov_exponents` in
the box-like case: `V_𝐢^1` is the coordinate axis `slowAxis`, the set of vectors whose other
coordinate vanishes. Indices above `2` repeat `{0}`. -/
recall BoxLike.System.oseledets {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
  ℕ → Set (ℝ × ℝ)
  | 0 => univ
  | 1 => {v | coord (S.slowAxis μ x + 1) v = 0}
  | _ => {0}

/-- The partitions `ξ_0, ξ_1, ξ_2` of `Σ'` (`sec:entropies`, tex lines 1779 to 1784):
`ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ V_𝐢^i}`, extended to `Σ` by the atom `Σ ∖ Σ'`. -/
recall BoxLike.System.xi {ι : Type u} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) (i : ℕ) :
  (ℤ → ι) → Set (ℤ → ι) := atomsOn (S.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ S.proj y - S.proj x ∈ S.oseledets μ x i}

/-- The partition `ξ_1^⊥` of `Σ'` (`sec:entropies`, tex lines 1785 to 1788):
`ξ_1^⊥(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ⊥ V_𝐢^1}`, extended to `Σ` by the atom `Σ ∖ Σ'`.
Orthogonality to the axis `slowAxis` is the vanishing of that coordinate. -/
recall BoxLike.System.xiPerp {ι : Type u} [MeasurableSpace ι] (S : System ι) (μ : Measure (ℤ → ι)) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn (S.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ coord (S.slowAxis μ x) (S.proj y - S.proj x) = 0}

/-- The partitions `\overline{ξ}_0`, `\overline{ξ}_1` of `Σ_Z` (`sec:entropies`, tex lines 1836
to 1920), extended to `{1, …, 2N}^ℤ` by the atom `{1, …, 2N}^ℤ ∖ Σ_Z`. They do not depend on a
measure. Indices above `1` repeat `\overline{ξ}_1`. -/
recall BoxLike.System.xiBar {ι : Type u} (S : System ι) : ℕ → (ℤ → ι × ZMod 2) → Set (ℤ → ι × ZMod 2)
  | 0 => atomsOn (subshift S.o) fun y => {z | SamePast z y}
  | _ => atomsOn (subshift S.o) fun y => {z | SamePast z y ∧ S.projBar z = S.projBar y}

/-- The `i`-dimensional entropy `h_i(μ) = H_μ(𝒫 | \widehat{ξ}_i)` (`sec:entropies`, tex lines
1891 to 1897). -/
recall BoxLike.System.dimEntropy {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : ℝ := condEntropy μ (S.xi μ i)

/-- The pointwise `i`-dimensional entropy `h_i(μ, 𝐢) = E_μ(I_μ(𝒫 | \widehat{ξ}_i) | ℐ)(𝐢)`
(`sec:entropies`, tex lines 1805 to 1811), determined up to a `μ`-null set. -/
recall BoxLike.System.dimEntropyAt {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : (ℤ → ι) → ℝ := localEntropy μ (S.xi μ i)

/-- The entropy `\overline{h}_i(ν) = H_ν(\overline{𝒫} | \widehat{\overline{ξ}}_i)`
(`sec:entropies`, tex lines 1848 to 1853). -/
recall BoxLike.System.dimEntropyBar {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν] (i : ℕ) : ℝ := condEntropy ν (S.xiBar i)

/-- The pointwise entropy `\overline{h}_i(ν, 𝐢)` (`sec:entropies`, tex lines 1842 to 1847),
determined up to a `ν`-null set. -/
recall BoxLike.System.dimEntropyBarAt {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν] (i : ℕ) : (ℤ → ι × ZMod 2) → ℝ := localEntropy ν (S.xiBar i)

/-- The average `\overline{μ} = (μ_1 + μ_2) / 2` of `eq:average_gibbs`. The scalar lies in
`ℝ≥0`, for which Mathlib has the instance that a multiple of a finite measure is finite. -/
recall BoxLike.avgMeasure {Ω : Type u_1} [MeasurableSpace Ω] (μ₁ μ₂ : Measure Ω) : Measure Ω :=
  (2⁻¹ : ℝ≥0) • (μ₁ + μ₂)

instance {Ω : Type*} [MeasurableSpace Ω] (μ₁ μ₂ : Measure Ω) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] : IsFiniteMeasure (avgMeasure μ₁ μ₂) := by
  unfold avgMeasure
  infer_instance

/-! ## Gibbs measures and the second iterate -/

/-- The potential `f_{1,s}` of `sec:gibbs_measures`, as a function of the symbol `j_0`. -/
recall BoxLike.System.potential₁ {ι : Type u_1} (S : System ι) (s : ℝ) (p : ι × ZMod 2) : ℝ :=
  if s < 1 then s * Real.log |S.ratio p|
  else Real.log |S.ratio p| + (s - 1) * Real.log |S.ratio (p.1, p.2 + 1)|

/-- The potential `f_{2,s}` of `sec:gibbs_measures`: `f_{2,s}(j_0) = f_{1,s}` of the symbol on
the other axis. -/
recall BoxLike.System.potential₂ {ι : Type u_1} (S : System ι) (s : ℝ) (p : ι × ZMod 2) : ℝ :=
  S.potential₁ s (p.1, p.2 + 1)

/-- A Gibbs measure on `Σ_Z` for the one-symbol potential `φ`, as in `sec:gibbs_measures`:
`C⁻¹ exp(-nP + S_n φ(𝐣)) ≤ ν([𝐣|_n]) ≤ C exp(-nP + S_n φ(𝐣))` for all `𝐣 ∈ Σ_Z` and `n ≥ 1`.
The constant `P` is the pressure `P_Z(φ)`; the bounds determine it. -/
recall BoxLike.IsGibbs {ι : Type u_1} [MeasurableSpace ι] (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ)
  (ν : Measure (ℤ → ι × ZMod 2)) : Prop := ∃ P C : ℝ, 0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k))

/-- The Gibbs decomposition: probability, ergodicity, support, Gibbs bounds, the four
measure identities, and the two Lyapunov exponents. -/
recall BoxLike.System.GibbsDecomposition.mk {ι : Type u_1} [MeasurableSpace ι] {S : System ι} {s : ℝ}
  {μ : Measure (ℤ → ι)} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (prob₁ : IsProbabilityMeasure μ₁)
  (prob₂ : IsProbabilityMeasure μ₂) (ergodic₁ : Ergodic (shift 1) μ₁) (ergodic₂ : Ergodic (shift 1) μ₂)
  (supp₁ : μ₁ (subshift S.o)ᶜ = 0) (supp₂ : μ₂ (subshift S.o)ᶜ = 0) (gibbs₁ : IsGibbs S.o (S.potential₁ s) μ₁)
  (gibbs₂ : IsGibbs S.o (S.potential₂ s) μ₂)
  (eq_tau : μ = Measure.map unCode (μ₁.restrict (range (tau S.o))) + Measure.map unCode (μ₂.restrict (range (tau S.o))))
  (eq_omega :
    μ = Measure.map unCode (μ₁.restrict (range (omega S.o))) + Measure.map unCode (μ₂.restrict (range (omega S.o))))
  (eq₁ : μ = Measure.map unCode (μ₁.restrict (range (tau S.o))) + Measure.map unCode (μ₁.restrict (range (omega S.o))))
  (eq₂ : μ = Measure.map unCode (μ₂.restrict (range (tau S.o))) + Measure.map unCode (μ₂.restrict (range (omega S.o))))
  (lyapunov₁_eq : S.lyapunov₁ μ = S.lyapBar μ₁) (lyapunov₂_eq : S.lyapunov₂ μ = S.lyapBar μ₂) :
  S.GibbsDecomposition s μ μ₁ μ₂

/-- The grouping map `β` of `sec:normalisation`. -/
recall BoxLike.group {α : Type u_2} (x : ℤ → α) : ℤ → α × α := fun n => (x (2 * n), x (2 * n + 1))

/-- The weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` of tex line 2261. -/
recall BoxLike.System.detWeight {ι : Type u_1} [Fintype ι] (S : System ι) (s : ℝ) (i : ι) : ℝ :=
  |(S.mat i).det| ^ (s / 2) / ∑ j, |(S.mat j).det| ^ (s / 2)

/-- The Bernoulli measure on `Σ = ℤ → ι` with the one-symbol distribution `p`, tex lines 2236 to
2360: the product of copies of `p` over `ℤ`. It is used for a probability measure `p`. -/
recall BoxLike.bernoulli {ι : Type u_1} [MeasurableSpace ι] (p : Measure ι) : Measure (ℤ → ι) :=
  Measure.infinitePi fun _ : ℤ => p

/-! ## Classification -/

/-- The tuple `𝖠` is irreducible (`sec:irreducibility`, tex lines 641 to 642): no line through
the origin is invariant under every `A_i`. A line is given by a non-zero vector `v` spanning
it, and `A_i v = c v` says that `A_i` maps the line into itself. For `S : System ι` this is
`System.Irreducible`. The form with lines as subspaces and `A_i V = V` is
`tupleIrreducible_iff_lines`. -/
recall BoxLike.TupleIrreducible {ι : Type u_1} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ¬ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, ∃ c : ℝ, A i *ᵥ v = c • v

/-- The tuple `𝖠` is strongly irreducible (`sec:irreducibility`, tex lines 643 to 644): no
non-empty finite set of lines through the origin is invariant under every `A_i`. The lines are
spanned by the non-zero vectors of a finite set `s`, and `A_i v = c w` with `w ∈ s` says that
`A_i` maps the line of `v` into the line of `w`. The form with sets `𝒱` of lines and
`A_i 𝒱 = 𝒱` is `tupleStronglyIrreducible_iff_lines`. -/
recall BoxLike.TupleStronglyIrreducible {ι : Type u_1} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ¬ ∃ s : Finset (Fin 2 → ℝ), s.Nonempty ∧ (∀ v ∈ s, v ≠ 0) ∧
    ∀ i, ∀ v ∈ s, ∃ w ∈ s, ∃ c : ℝ, A i *ᵥ v = c • w

/-- The tuple `𝖠` is proximal (`sec:irreducibility`, tex lines 644 to 646): the semigroup
generated by `𝖠` contains a proximal matrix, that is, some product `A_{i_1} ⋯ A_{i_n}` with
`n ≥ 1` is proximal. For `S : System ι` this is `System.Proximal`. -/
recall BoxLike.TupleProximal {ι : Type u_1} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ w : List ι, w ≠ [] ∧ IsProximalMatrix (w.map A).prod

/-- The description in item (2) of `thm:A_classification`: in some basis, the columns of `P`,
the matrices of `𝖠` are simultaneously diagonal or anti-diagonal, with at least one
anti-diagonal matrix. -/
recall BoxLike.SimultaneouslyBoxLike {ι : Type u_1} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
    (∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, P⁻¹ * A i * P = boxMat c a b) ∧
    ∃ i, ∃ a b : ℝ, P⁻¹ * A i * P = boxMat 1 a b

/-- The description in item (3) of `thm:A_classification`: in some basis, the columns of `P`,
the matrices of `𝖠` are simultaneously upper triangular. -/
recall BoxLike.SimultaneouslyTriangular {ι : Type u_1} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧ ∀ i, (P⁻¹ * A i * P) 1 0 = 0

/-- The tuple `𝖠` is box-like with rotations (`sec:box_like_self_affine`, tex lines 570 to 579):
every `A_i` is `D_i R_i` with `D_i = diag(d_1(i), d_2(i))` invertible, `‖D_i‖ < 1`, and `R_i` a
linear isometry with `R_i([-1,1]²) = [-1,1]²`, and both rotating and non-rotating isometries
occur. The isometry `R_i` is rotating when it moves the coordinate axes, `R_i e_1 ∉ ℝ e_1`, that
is `(R_i)_{21} ≠ 0`. -/
recall BoxLike.IsBoxLikeWithRotations {ι : Type u_1} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ (d₁ d₂ : ι → ℝ) (R : ι → Matrix (Fin 2) (Fin 2) ℝ),
    (∀ i, d₁ i ≠ 0 ∧ d₂ i ≠ 0 ∧ ‖boxMat 0 (d₁ i) (d₂ i)‖ < 1 ∧ IsSquareIsometry (R i) ∧
      A i = boxMat 0 (d₁ i) (d₂ i) * R i) ∧
    (∃ i, R i 1 0 ≠ 0) ∧ ∃ i, R i 1 0 = 0

/-- The distance of `φ_𝐢` and `φ_𝐣` in the affine coefficients: the `ℓ²` operator norm of the
difference `A_𝐢 - A_𝐣` of the linear parts plus the supremum norm of the difference
`φ_𝐢(0) - φ_𝐣(0)` of the translation parts (`sec:intro_setting`, tex lines 388 to 397, and the
norm on affine coefficients of tex line 1460). -/
recall BoxLike.PlanarSystem.affDist {ι : Type u_1} (P : PlanarSystem ι) (w w' : List ι) : ℝ :=
  ‖MatrixTuple.word P.mat w - MatrixTuple.word P.mat w'‖ + ‖P.phiWord w 0 - P.phiWord w' 0‖

/-- The least coefficient distance between distinct words of length `n`; the minimum of the
empty set is `⊤`. -/
recall BoxLike.PlanarSystem.affGap {ι : Type u_1} (P : PlanarSystem ι) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (w : List ι) (w' : List ι) (_ : w.length = n) (_ : w'.length = n) (_ : w ≠ w'),
    ENNReal.ofReal (P.affDist w w')

/-- The exponential separation condition of `sec:intro_setting`, with
the distance in the affine coefficients: there are `c > 0` and a strictly increasing sequence
`(n_k)` with `min_{𝐢 ≠ 𝐣 ∈ Λ^{n_k}} ‖φ_𝐢 - φ_𝐣‖ ≥ c^{n_k}` for every `k`. -/
recall BoxLike.PlanarSystem.ExpSeparation {ι : Type u_1} (P : PlanarSystem ι) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (c ^ n k) ≤ P.affGap (n k)

namespace Solution.Paper

/-! ## 1. Introduction -/

-- PAPER_ENTRY thm:hochman_rapaport
/-! ### Theorem 1.1: Hochman–Rapaport's dimension formula for strongly irreducible planar systems

`thm:hochman_rapaport`. Cited and unproved; the source
hypothesis of no common fixed point is retained. -/

/-- Theorem 1.1 (Hochman–Rapaport), as a proposition only. The source requires no common
fixed point; this hypothesis is retained here. No proof or axiom is asserted. -/
def paper_1_1 : Prop :=
  ∀ {ι : Type u} [Fintype ι] [Nonempty ι] (P : PlanarSystem ι), TupleProximal P.mat →
    TupleStronglyIrreducible P.mat → (¬ ∃ z : ℝ × ℝ, ∀ i, P.phi i z = z) → P.ExpSeparation →
    dimH P.attractor = ENNReal.ofReal (min 2 P.dimaff)

-- PAPER_ENTRY thm:rapaport
/-! ### Theorem 1.2: Rapaport's dimension formula for diagonal systems

`thm:rapaport`. -/

theorem paper_1_2 {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι) (hdiag : ∀ (i : ι), S.o i = 0)
  (hprox : S.Proximal) (hsep₁ : S.AxisExpSeparation 0) (hsep₂ : S.AxisExpSeparation 1) :
  dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  exact Rapaport.rapaportDiagonalDimension_holds S hdiag hprox hsep₁ hsep₂

-- PAPER_ENTRY thm:fraser
/-! ### Theorem 1.3: Fraser's packing and Minkowski dimension formula

`thm:fraser`. -/

/-- Theorem 1.3: the upper bound, equality under the rectangular open set condition,
and equality of modified affinity and affinity dimensions when both projections have dimension one. -/
theorem paper_1_3 {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι) :
    (packingDim S.attractor = upperBoxDim S.attractor ∧
      upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff) ∧
    (S.RectangularOpenSet →
      packingDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimmaff) ∧
    (S.RectangularOpenSet →
      (∀ c, upperBoxDim (System.coord c '' S.attractor) = 1) → S.dimmaff = S.dimaff) := by
  exact ⟨S.fraserBound_holds, S.fraserROSC_holds,
    S.fraserROSC_holds.dimmaff_eq_dimaff⟩

-- PAPER_ENTRY thm:main1
/-! ### Theorem A: Projections of the equilibrium state at the affinity dimension

`thm:main1`. -/

theorem paper_A {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι))
  [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
  (c : ZMod 2) :
  (S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ → IsDoubleDim (S.marginal c μ)) ∧
    (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  exact System.main1_dimaff_all S morrisShmerkinLyapunov_holds equilibriumGibbs fraserJordanJurgaDecomposition_holds
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) hrot hprox hsep μ hinv heq c

-- PAPER_ENTRY thm:main2
/-! ### Theorem B: Hausdorff dimension equals affinity dimension

`thm:main2`. -/

/-- Theorem B, including the furthermore clause. -/
theorem paper_B {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet ∨
      S.ProjExpSeparation) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) ∧
      (S.ProjExpSeparation → S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet →
        IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2) := by
  exact ⟨S.main2_full_of_library hrot hprox hfree μ hinv heq hor,
    fun hsep hor' => S.main2_furthermore_of_library hrot hprox hsep μ hinv heq hor'⟩

-- PAPER_ENTRY q:coincident-projection-dimensions
/-! ### Question 1.4: Question on coincident projection dimensions without exact overlaps

`q:coincident-projection-dimensions`. Open question; no answer is asserted. -/

/-- Question 1.4: does such a system exist? This definition asserts no answer. -/
def paper_1_4 : Prop :=
  ∃ (N : ℕ) (S : System (Fin (N + 1))) (μ : Measure (ℤ → Fin (N + 1)))
    (μ₁ μ₂ : Measure (ℤ → Fin (N + 1) × ZMod 2)) (d : ℝ),
    IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
    S.WithRotations ∧ S.Proximal ∧ S.NoExactOverlaps ∧
    S.IsEquilibriumState S.dimaff μ ∧ S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∧
    S.GibbsDecomposition S.dimaff μ μ₁ μ₂ ∧
    IsExactDim (μ₁.map S.projBar) d ∧ IsExactDim (μ₂.map S.projBar) d ∧
    ∀ c : ZMod 2, IsExactDim (S.marginal c μ) d

/-! ## 2. Box-like systems and the projective coding -/

-- PAPER_ENTRY thm:box_like_sa
/-! ### Lemma 2.1: Box-like matrices are diagonal or anti-diagonal

`thm:box_like_sa`. -/

theorem paper_2_1 {ι : Type u_1} {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ (i : ι), (A i).det ≠ 0)
  (hnorm : ∀ (i : ι), ‖A i‖ < 1) :
  IsBoxLikeWithRotations A ↔
    (∀ (i : ι), ∃ c a b, A i = boxMat c a b) ∧ (∃ i a b, A i = boxMat 0 a b) ∧ ∃ i a b, A i = boxMat 1 a b := by
  exact box_like_sa_of_contracting hdet hnorm

-- PAPER_ENTRY thm:A_classification
/-! ### Lemma 2.2: Classification of irreducibility for planar tuples

`thm:A_classification`. -/

theorem paper_2_2 {ι : Type u_1} {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ (i : ι), (A i).det ≠ 0)
  (hprox : TupleProximal A) :
  (TupleStronglyIrreducible A ∧ ¬SimultaneouslyBoxLike A ∧ ¬SimultaneouslyTriangular A ∨
      ¬TupleStronglyIrreducible A ∧ SimultaneouslyBoxLike A ∧ ¬SimultaneouslyTriangular A ∨
        ¬TupleStronglyIrreducible A ∧ ¬SimultaneouslyBoxLike A ∧ SimultaneouslyTriangular A) ∧
    (SimultaneouslyBoxLike A ↔ TupleIrreducible A ∧ ¬TupleStronglyIrreducible A) ∧
      (SimultaneouslyTriangular A ↔ ¬TupleIrreducible A) := by
  exact tuple_classification hdet hprox

-- PAPER_ENTRY thm:box_like_proximal
/-! ### Lemma 2.3: A proximal box-like tuple has a proximal diagonal generator or passes to second iterates

`thm:box_like_proximal`. -/

theorem paper_2_3 {ι : Type u_1} {S : System ι} (h : S.Proximal) : S.HasProximalDiagonal ∨ S.sq.HasProximalDiagonal := by
  exact System.Proximal.box_like_proximal h

-- PAPER_ENTRY thm:tau_omega_sigma_commutative
/-! ### Lemma 2.4: The codings τ and ω intertwine the shifts

`thm:tau_omega_sigma_commutative`. -/

theorem paper_2_4 {ι : Type u_1} {o : ι → ZMod 2} {x : ℤ → ι} {n : ℤ} (h : eps o x n = 0) :
  tau o (shift n x) = shift n (tau o x) := by
  exact tau_shift_of_eps_eq_zero h

theorem paper_2_4_2 {ι : Type u_1} {o : ι → ZMod 2} {x : ℤ → ι} {n : ℤ} (h : eps o x n = 0) :
  omega o (shift n x) = shift n (omega o x) := by
  exact omega_shift_of_eps_eq_zero h

theorem paper_2_4_3 {ι : Type u_1} {o : ι → ZMod 2} {x : ℤ → ι} {n : ℤ} (h : eps o x n = 1) :
  tau o (shift n x) = shift n (omega o x) := by
  exact tau_shift_of_eps_eq_one h

theorem paper_2_4_4 {ι : Type u_1} {o : ι → ZMod 2} {x : ℤ → ι} {n : ℤ} (h : eps o x n = 1) :
  omega o (shift n x) = shift n (tau o x) := by
  exact omega_shift_of_eps_eq_one h

-- PAPER_ENTRY thm:matrix_products_g_derivatives
/-! ### Lemma 2.5: Matrix products and derivatives of the projective system

`thm:matrix_products_g_derivatives`. -/

theorem paper_2_5 {ι : Type u_1} (S : System ι) (x : ℤ → ι) (n : ℕ) :
  |(S.matWord (pastWord x n)).mulVec ![1, 0] 0| + |(S.matWord (pastWord x n)).mulVec ![1, 0] 1| =
    |S.gDeriv (pastWord (tau S.o x) n)| := by
  exact System.abs_matWord_pastWord_e1 S x n

theorem paper_2_5_2 {ι : Type u_1} (S : System ι) (x : ℤ → ι) (n : ℕ) :
  |(S.matWord (pastWord x n)).mulVec ![0, 1] 0| + |(S.matWord (pastWord x n)).mulVec ![0, 1] 1| =
    |S.gDeriv (pastWord (omega S.o x) n)| := by
  exact System.abs_matWord_pastWord_e2 S x n

-- PAPER_ENTRY lem:proj_gap_dominated
/-! ### Lemma 2.6: The projective gap is dominated by the gap of the diagonal maps

`lem:proj_gap_dominated`. -/

theorem paper_2_6 {ι : Type u_1} (S : System ι) {J : Set ι} {a : ℝ} (hJ : ∀ i ∈ J, S.a i = a) (n : ℕ) :
  S.gap n ≤ S.diagGap J n := by
  exact System.gap_le_diagGap S hJ n

-- PAPER_ENTRY prop:ssc_no_overlap_not_pesc
/-! ### Proposition 2.7: Strong separation without projective exponential separation

`prop:ssc_no_overlap_not_pesc`. -/

theorem paper_2_7 :
  ∃ S : System (Fin 4),
    S.o = ![0, 0, 0, 1] ∧
      S.Proximal ∧
        S.Irreducible ∧
          ¬TupleStronglyIrreducible S.mat ∧
            (∀ (i : Fin 4) (v : Fin 2 → ℝ), v 0 = 0 ∨ v 1 = 0 → (S.mat i).mulVec v 0 = 0 ∨ (S.mat i).mulVec v 1 = 0) ∧
              (∃ i₀, S.o i₀ = 0 ∧ |S.a i₀| ≠ |S.b i₀|) ∧
                S.StrongSeparation ∧ S.FreeProjective ∧ ¬S.ProjExpSeparation ∧ ∑ i, |(S.mat i).det| < 1 := by
  exact NoOverlap.prop_ssc_no_overlap_not_pesc NoOverlap.baranyKaenmakiPair_holds

/-! ## 3. Lyapunov exponents, conditional measures and equilibrium states -/

-- PAPER_ENTRY thm:lyapunov_exponents_via_g_system
/-! ### Lemma 3.1: Lyapunov exponents through the projective system

`thm:lyapunov_exponents_via_g_system`. -/

theorem paper_3_1 {ι : Type u_1} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) (hrot : S.WithRotations) (hprox : S.Proximal) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
  (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
  Nonempty (MatrixTuple.OseledetsSet S.mat μ) ∧
    ∀ (O : MatrixTuple.OseledetsSet S.mat μ),
      ∀ x ∈ O.carrier,
        (x ∈ O.sigmaTau ∨ x ∈ O.sigmaOmega) ∧
          (x ∈ O.sigmaTau → S.HasBackRate (tau S.o x) (S.lyapunov₁ μ) ∧ S.HasBackRate (omega S.o x) (S.lyapunov₂ μ)) ∧
            (x ∈ O.sigmaOmega → S.HasBackRate (omega S.o x) (S.lyapunov₁ μ) ∧ S.HasBackRate (tau S.o x) (S.lyapunov₂ μ)) := by
  exact System.lyapunov_exponents_via_g_system_manuscript S hrot hprox μ hinv herg hlt

-- PAPER_ENTRY thm:conditional_measures_of_a_conditional_measure
/-! ### Lemma 3.2: Conditional measures of a conditional measure

`thm:conditional_measures_of_a_conditional_measure`. -/

theorem paper_3_2 {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] {ξ : Ω → Set Ω} (_hξ : IsMeasurablePartition ξ) {Ξ : Set Ω} (hΞ : MeasurableSet Ξ)
  (_hpos : 0 < μ Ξ) : ∀ᵐ (x : Ω) ∂μ[|Ξ], 0 < (condMeas μ ξ x) Ξ ∧ condMeas μ[|Ξ] ξ x = (condMeas μ ξ x)[|Ξ] := by
  exact condMeas_cond μ _hξ hΞ _hpos

-- PAPER_ENTRY thm:double_conditional
/-! ### Lemma 3.3: Double conditioning

`thm:double_conditional`. -/

theorem paper_3_3 {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] {ξ ξ' : Ω → Set Ω} (_hξ : IsMeasurablePartition ξ) (hξ' : IsMeasurablePartition ξ')
  (hfine : ∀ (x : Ω), ξ' x ⊆ ξ x) :
  (∀ᵐ (j : Ω) ∂μ, ∀ᵐ (i : Ω) ∂condMeas μ ξ j, condMeas (condMeas μ ξ j) ξ' i = condMeas μ ξ' i) ∧
    ∀ (A : Set Ω),
      MeasurableSet A →
        ∫⁻ (j : Ω), ∫⁻ (i : Ω), (condMeas μ ξ' i) A ∂condMeas μ ξ j ∂μ = ∫⁻ (i : Ω), (condMeas μ ξ' i) A ∂μ := by
  exact double_conditional μ _hξ hξ' hfine

-- PAPER_ENTRY thm:finer_partition_dirac_mass
/-! ### Lemma 3.4: Dirac conditional measures of a finer partition

`thm:finer_partition_dirac_mass`. -/

theorem paper_3_4 {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] {ξ ξ' : Ω → Set Ω} (hξ : IsMeasurablePartition ξ) (hξ' : IsMeasurablePartition ξ')
  (hfine : ∀ (x : Ω), ξ' x ⊆ ξ x) (h : ∀ᵐ (x : Ω) ∂μ, condMeas μ ξ x = Measure.dirac x) :
  ∀ᵐ (x : Ω) ∂μ, condMeas μ ξ' x = Measure.dirac x := by
  exact finer_partition_dirac_mass μ hξ hξ' hfine h

-- PAPER_ENTRY thm:feng_entropy_as_limit
/-! ### Lemma 3.5: Feng's entropies as limits

`thm:feng_entropy_as_limit`. -/

theorem paper_3_5 :
  (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      Ergodic (shift 1) μ →
        P.lyapunov₂ μ < P.lyapunov₁ μ →
          ∀ i ≤ 2,
            ∀ᵐ (x : ℤ → ι) ∂μ,
              Tendsto (fun n ↦ -Real.log ((condMeas μ (P.xi μ i) x).real (BoxLike.cylinder (block n x))) / ↑n) atTop
                (𝓝 (P.dimEntropyAt μ i x))) ∧
    ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
      S.WithRotations →
        S.Proximal →
          ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
            MeasurePreserving (shift 1) ν ν →
              ν (subshift S.o)ᶜ = 0 →
                ∀ i ≤ 1,
                  ∀ᵐ (y : ℤ → ι × ZMod 2) ∂ν,
                    Tendsto (fun n ↦ -Real.log ((condMeas ν (S.xiBar i) y).real (BoxLike.cylinder (block n y))) / ↑n)
                      atTop (𝓝 (S.dimEntropyBarAt ν i y)) := by
  exact feng_entropy_as_limit_general

-- PAPER_ENTRY thm:feng_entropy_kolmogorov_sinai
/-! ### Lemma 3.6: Feng's entropy and the Kolmogorov–Sinai entropy

`thm:feng_entropy_kolmogorov_sinai`. -/

theorem paper_3_6 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ)
  (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
  ∀ᵐ (x : ℤ → ι) ∂μ,
    x ∈ P.SigmaPrime μ →
      Tendsto (fun n ↦ -Real.log (μ.real (BoxLike.cylinder (block n x))) / ↑n) atTop (𝓝 (P.dimEntropyAt μ 0 x)) := by
  exact PlanarSystem.feng_entropy_kolmogorov_sinai_general P μ herg hlt

-- PAPER_ENTRY thm:feng_entropy_zero
/-! ### Lemma 3.7: Vanishing of the entropy h_0 on the finest partition

`thm:feng_entropy_zero`. -/

theorem paper_3_7 :
  (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      Ergodic (shift 1) μ →
        P.lyapunov₂ μ < P.lyapunov₁ μ →
          ∀ i ≤ 2, ∀ᵐ (x : ℤ → ι) ∂μ, P.dimEntropyAt μ i x = 0 ↔ condMeas μ (P.xi μ i) x = Measure.dirac x) ∧
    ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
      S.WithRotations →
        S.Proximal →
          ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
            MeasurePreserving (shift 1) ν ν →
              ν (subshift S.o)ᶜ = 0 →
                ∀ i ≤ 1,
                  ∀ᵐ (y : ℤ → ι × ZMod 2) ∂ν, S.dimEntropyBarAt ν i y = 0 ↔ condMeas ν (S.xiBar i) y = Measure.dirac y := by
  exact feng_entropy_zero_general

-- PAPER_ENTRY thm:partitions_xi1
/-! ### Lemma 3.8: The partitions ξ_1 on the orientation sets

`thm:partitions_xi1`. -/

theorem paper_3_8 {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (_hrot : S.WithRotations) (_hprox : S.Proximal)
  (μ : Measure (ℤ → ι)) (_hinv : MeasurePreserving (shift 1) μ μ) (_herg : Ergodic (shift 1) μ)
  (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) :
  (x ∈ S.SigmaTau μ →
      (S.xi μ 1 x = unCode '' S.xiBar 1 (tau S.o x) ∧ S.xi μ 1 x ⊆ S.SigmaTau μ) ∧
        S.xiPerp μ x = unCode '' S.xiBar 1 (omega S.o x) ∧ S.xiPerp μ x ⊆ S.SigmaTau μ) ∧
    (x ∈ S.SigmaOmega μ →
      (S.xi μ 1 x = unCode '' S.xiBar 1 (omega S.o x) ∧ S.xi μ 1 x ⊆ S.SigmaOmega μ) ∧
        S.xiPerp μ x = unCode '' S.xiBar 1 (tau S.o x) ∧ S.xiPerp μ x ⊆ S.SigmaOmega μ) := by
  exact System.partitions_xi1 S _hrot _hprox μ _hinv _herg hlt x

-- PAPER_ENTRY thm:partition_tau_conj
/-! ### Lemma 3.9: Conjugation of the partitions by τ

`thm:partition_tau_conj`. -/

theorem paper_3_9 {ι : Type u_1} [MeasurableSpace ι] (S : System ι) (hrot : S.WithRotations) (hprox : S.Proximal)
  (μ : Measure (ℤ → ι)) (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
  (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) (n : ℕ) :
  (x ∈ S.SigmaTau μ →
      S.xi μ 1 x ∩ BoxLike.cylinder (block n x) =
        unCode '' (S.xiBar 1 (tau S.o x) ∩ BoxLike.cylinder (block n (tau S.o x)))) ∧
    (x ∈ S.SigmaOmega μ →
      S.xi μ 1 x ∩ BoxLike.cylinder (block n x) =
        unCode '' (S.xiBar 1 (omega S.o x) ∩ BoxLike.cylinder (block n (omega S.o x)))) := by
  exact System.partition_tau_conj S hrot hprox μ hinv herg hlt x n

-- PAPER_ENTRY thm:irred_eq_state
/-! ### Proposition 3.10: Equilibrium states of irreducible tuples: existence, uniqueness, ergodicity, Gibbs bounds

`thm:irred_eq_state`. -/

theorem paper_3_10 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ (i : ι), (A i).det ≠ 0) (hirr : TupleIrreducible A) {s : ℝ} (hs0 : 0 < s) :
  ∃ μ,
    IsProbabilityMeasure μ ∧
      MeasurePreserving (shift 1) μ μ ∧
        MatrixTuple.IsEquilibriumState A s μ ∧
          (∀ (ν : Measure (ℤ → ι)),
              IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν → MatrixTuple.IsEquilibriumState A s ν → ν = μ) ∧
            Ergodic (shift 1) μ ∧ MatrixTuple.HasGibbsBounds A s μ := by
  exact MatrixTuple.irred_eq_state_of_fengKaenmaki fengKaenmakiNormEquilibrium_holds A hA hirr hs0

-- PAPER_ENTRY thm:two-block-normalisation
/-! ### Lemma 3.11: Two-block normalisation

`thm:two-block-normalisation`. -/

theorem paper_3_11 {ι : Type u} (S : System ι) [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {s : ℝ} (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s) (μ : Measure (ℤ → ι))
  [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
  S.sq.attractor = S.attractor ∧
    S.sq.WithRotations ∧
      S.sq.HasProximalDiagonal ∧
        (S.StrongSeparation → S.sq.StrongSeparation) ∧
          (S.StrongOpenSet → S.sq.StrongOpenSet) ∧
            (S.ProjExpSeparation → S.sq.ProjExpSeparation) ∧
              (IsProbabilityMeasure (Measure.map group μ) ∧
                  MeasurePreserving (shift 1) (Measure.map group μ) (Measure.map group μ) ∧
                    S.sq.IsEquilibriumState s (Measure.map group μ) ∧
                      (∀ (ν : Measure (ℤ → ι × ι)),
                          IsProbabilityMeasure ν →
                            MeasurePreserving (shift 1) ν ν → S.sq.IsEquilibriumState s ν → ν = Measure.map group μ) ∧
                        Ergodic (shift 1) (Measure.map group μ)) ∧
                (∀ (t : ℝ), 0 ≤ t → S.sq.pressure t = 2 * S.pressure t) ∧
                  entropy (Measure.map group μ) = 2 * entropy μ ∧
                    S.sq.lyapunov₁ (Measure.map group μ) = 2 * S.lyapunov₁ μ ∧
                      S.sq.lyapunov₂ (Measure.map group μ) = 2 * S.lyapunov₂ μ ∧
                        Measure.map S.sq.proj (Measure.map group μ) = Measure.map S.proj μ := by
  exact System.two_block_normalisation S hrot hprox hs0 μ hinv heq

theorem paper_3_11_2 {ι : Type u} (S : System ι) [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Nonempty ι] (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) :
  S.sq.dimaff = S.dimaff ∧
    lyapDim (entropy (Measure.map group μ)) (S.sq.lyapunov₁ (Measure.map group μ))
          (S.sq.lyapunov₂ (Measure.map group μ)) =
        lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ) ∧
      (∀ (c : ZMod 2), S.sq.marginal c (Measure.map group μ) = S.marginal c μ) ∧
        (IsBernoulli μ → IsBernoulli (Measure.map group μ)) := by
  exact System.two_block_normalisation_consequences S μ hinv

-- PAPER_ENTRY thm:bernoulli_equilibrium
/-! ### Lemma 3.12: Equilibrium states for s ≥ 2 are Bernoulli

`thm:bernoulli_equilibrium`. -/

theorem paper_3_12 {ι : Type u_1} [Fintype ι] (S : System ι) {s : ℝ} (hs : 2 ≤ s) :
  S.pressure s = Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) := by
  exact System.pressure_of_two_le S hs

theorem paper_3_12_2 {ι : Type u_1} [Fintype ι] (S : System ι) {s : ℝ} [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [Nonempty ι] (hs : 2 ≤ s) :
  ∃! μ, IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧ S.IsEquilibriumState s μ := by
  exact System.existsUnique_isEquilibriumState_of_two_le S hs

theorem paper_3_12_3 {ι : Type u_1} [Fintype ι] {S : System ι} {s : ℝ} [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (heq : S.IsEquilibriumState s μ)
  (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) : μ = bernoulli (S.detWeightMeasure s) := by
  exact System.IsEquilibriumState.eq_bernoulli heq hinv hs

-- PAPER_ENTRY thm:sigma_tau_omega_positive_eq_measure
/-! ### Lemma 3.13: Positive measure of the orientation sets

`thm:sigma_tau_omega_positive_eq_measure`. -/

theorem paper_3_13 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} (hrot : S.WithRotations) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
  (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) :
  0 < μ (S.SigmaTau μ) ∧ 0 < μ (S.SigmaOmega μ) := by
  exact System.sigma_tau_omega_positive_eq_measure S equilibriumGibbs hrot hs0 hs2 μ hinv herg heq

-- PAPER_ENTRY thm:eq_state_is_sum
/-! ### Proposition 3.14: Decomposition of the equilibrium state into two Gibbs measures

`thm:eq_state_is_sum`. -/

theorem paper_3_14 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    ∃ μ₁ μ₂, S.GibbsDecomposition s μ μ₁ μ₂ := by
  exact fraserJordanJurgaDecomposition_holds S hrot hdiag hs0 hs2 μ hinv
    (equilibriumGibbs S hrot hs0 hs2 μ hinv heq)

theorem paper_3_14_2 {ι : Type u_1} (S : System ι) [Fintype ι] (h0 : ∃ i, S.o i = 0) {s : ℝ} (hs0 : 0 < s)
  (hs2 : s < 2) : S.pressure s = pressureZ S.o (S.potential₁ s) := by
  exact System.pressure_eq_pressureZ₁ S h0 hs0 hs2

theorem paper_3_14_3 {ι : Type u_1} (S : System ι) [Fintype ι] (h0 : ∃ i, S.o i = 0) {s : ℝ} (hs0 : 0 < s)
  (hs2 : s < 2) : S.pressure s = pressureZ S.o (S.potential₂ s) := by
  exact System.pressure_eq_pressureZ₂ S h0 hs0 hs2

theorem paper_3_14_4 {ι : Type u_1} [MeasurableSpace ι] {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)}
  {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (h : S.GibbsDecomposition s μ μ₁ μ₂) :
  S.lyapunov₁ μ = ∫ (y : ℤ → ι × ZMod 2), S.potential₁ 1 (y 0) ∂μ₁ := by
  exact System.GibbsDecomposition.lyapunov₁_eq_integral h

theorem paper_3_14_5 {ι : Type u_1} [MeasurableSpace ι] {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)}
  {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (h : S.GibbsDecomposition s μ μ₁ μ₂) :
  S.lyapunov₂ μ = ∫ (y : ℤ → ι × ZMod 2), S.potential₁ 1 (y 0) ∂μ₂ := by
  exact System.GibbsDecomposition.lyapunov₂_eq_integral h

theorem paper_3_14_6 {ι : Type u_1} [MeasurableSpace ι] {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)}
  {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} [Fintype ι] [MeasurableSingletonClass ι]
  (h : S.GibbsDecomposition s μ μ₁ μ₂) : S.lyapunov₁ μ = ∫ (y : ℤ → ι × ZMod 2), S.potential₂ 1 (y 0) ∂μ₂ := by
  exact System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂ h

theorem paper_3_14_7 {ι : Type u_1} [MeasurableSpace ι] {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)}
  {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} [Fintype ι] [MeasurableSingletonClass ι]
  (h : S.GibbsDecomposition s μ μ₁ μ₂) : S.lyapunov₂ μ = ∫ (y : ℤ → ι × ZMod 2), S.potential₂ 1 (y 0) ∂μ₁ := by
  exact System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂ h

/-! ## 4. Dimensions of the projections and the equilibrium state -/

-- PAPER_ENTRY thm:exact-dimensional-mixture
/-! ### Lemma 4.1: Mixtures of exact-dimensional measures

`thm:exact-dimensional-mixture`. -/

theorem paper_4_1 {X : Type u_1} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X] {ν₁ ν₂ : Measure X} {d₁ d₂ : ℝ}
  [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0)
  (hne₂ : ν₂ ≠ 0) :
  (∀ᵐ (x : X) ∂ν₁, HasLocalDim (ν₁ + ν₂) x d₁) ∧
    (∀ᵐ (x : X) ∂ν₂, HasLocalDim (ν₁ + ν₂) x d₂) ∧
      0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₁} ∧
        0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₂} ∧
          (d₁ ≠ d₂ → IsDoubleDim (ν₁ + ν₂)) ∧ (d₁ = d₂ → IsExactDim (ν₁ + ν₂) d₁) := by
  exact IsExactDim.mixture h₁ h₂ hne₁ hne₂

-- PAPER_ENTRY thm:feng1
/-! ### Theorem 4.2: Feng's Ledrappier–Young formula

`thm:feng1`. -/

theorem paper_4_2 :
  (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ →
        Ergodic (shift 1) μ →
          P.lyapunov₂ μ < P.lyapunov₁ μ →
            IsExactDim (Measure.map P.proj μ)
              ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
                (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)) ∧
    ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
      S.WithRotations →
        S.Proximal →
          ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
            MeasurePreserving (shift 1) ν ν →
              Ergodic (shift 1) ν →
                ν (subshift S.o)ᶜ = 0 →
                  IsExactDim (Measure.map S.projBar ν) ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν) := by
  exact planar_feng1 planarFengLedrappierYoung_holds fengLedrappierYoungBar_holds

-- PAPER_ENTRY thm:entropy_eq_gibbs
/-! ### Proposition 4.3: Entropy of the equilibrium state and of the Gibbs measures

`thm:entropy_eq_gibbs`. -/

theorem paper_4_3 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {S : System ι}
  {s : ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}
  [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
  S.dimEntropy μ 0 = S.dimEntropyBar μ₁ 0 ∧ S.dimEntropy μ 0 = S.dimEntropyBar μ₂ 0 := by
  exact System.GibbsDecomposition.dimEntropy_zero_eq_gibbs hdec

-- PAPER_ENTRY thm:eq_state_proj_dim
/-! ### Theorem 4.4: Dimensions of the projections of the equilibrium state

`thm:eq_state_proj_dim`. -/

theorem paper_4_4 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (μ : Measure (ℤ → ι))
  [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ)
  (c : ZMod 2) :
  HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ)) (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
    upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) ∧
        0 < (S.marginal c μ) {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₁ μ))} ∧
          0 < (S.marginal c μ) {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₂ μ))} := by
  exact System.eq_state_proj_dim_all S morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) hrot hprox
    hsep hs0 μ hinv heq c

-- PAPER_ENTRY ex:projection_double_dimensional
/-! ### Example 4.5: Example with double-dimensional projections

`ex:projection_double_dimensional`. -/

/-- The entropy functions and contractions used in the four-map construction. -/
recall BoxLike.PrescribedExample.H (p : ℝ) : ℝ :=
  -p * Real.log p - (1 - p) * Real.log (1 - p)
recall BoxLike.PrescribedExample.J (p : ℝ) : ℝ :=
  -p * Real.log (1 - p) - (1 - p) * Real.log p
recall BoxLike.PrescribedExample.ratio (p : ℝ) : ℝ :=
  (Real.log 2 + PrescribedExample.H p) / (Real.log 2 + PrescribedExample.J p)
recall BoxLike.PrescribedExample.aOf (s₁ p : ℝ) : ℝ := (p / 2) ^ (1 / s₁)
recall BoxLike.PrescribedExample.bOf (s₁ p : ℝ) : ℝ := ((1 - p) / 2) ^ (1 / s₁)

/-- `paramsOf` bundles these contractions with `0 < b < a < 1/2`. The system `sys P t`
has two diagonal maps `(a x + t_i, b y + t_{i+4})` and two anti-diagonal maps
`(a y + t_i, b x + t_{i+4})`, indexed by `Fin 4`. -/
theorem paper_4_5 {s₁ s₂ : ℝ} (hs₂ : 0 < s₂) (h₂₁ : s₂ < s₁) (hs₁ : s₁ ≤ 1) :
    ∃ (p : ℝ) (hp : 1 / 2 < p ∧ p < 1),
      PrescribedExample.ratio p = s₂ / s₁ ∧
      (∀ q ∈ Ioo (1 / 2) 1, PrescribedExample.ratio q = s₂ / s₁ → q = p) ∧
      ∃ t : Fin 8 → ℝ,
        let S := PrescribedExample.sys
          (PrescribedExample.paramsOf s₁ p (hs₂.trans h₂₁) hs₁ hp.1 hp.2) t
        S.WithRotations ∧ S.Proximal ∧ S.StrongSeparation ∧ S.ProjExpSeparation ∧
        S.dimaff = s₁ ∧
        (∃! μ, IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
          S.IsEquilibriumState s₁ μ) ∧
        ∀ (μ : Measure (ℤ → Fin 4)) [IsProbabilityMeasure μ],
          MeasurePreserving (shift 1) μ μ → S.IsEquilibriumState s₁ μ →
          entropy μ = Real.log 2 + PrescribedExample.H p ∧
          S.lyapunov₁ μ = p * Real.log (PrescribedExample.aOf s₁ p) +
            (1 - p) * Real.log (PrescribedExample.bOf s₁ p) ∧
          S.lyapunov₁ μ = -(Real.log 2 + PrescribedExample.H p) / s₁ ∧
          S.lyapunov₂ μ = p * Real.log (PrescribedExample.bOf s₁ p) +
            (1 - p) * Real.log (PrescribedExample.aOf s₁ p) ∧
          S.lyapunov₂ μ = -(Real.log 2 + PrescribedExample.J p) / s₁ ∧
          -entropy μ / S.lyapunov₁ μ = s₁ ∧ -entropy μ / S.lyapunov₂ μ = s₂ ∧
          ∀ c : ZMod 2,
            IsDoubleDim (S.marginal c μ) ∧ HasLocalDimPair (S.marginal c μ) s₁ s₂ ∧
            upperPackingDim (S.marginal c μ) = s₁ ∧ lowerHausdorffDim (S.marginal c μ) = s₂ ∧
            0 < (S.marginal c μ) {x | HasLocalDim (S.marginal c μ) x s₁} ∧
            0 < (S.marginal c μ) {x | HasLocalDim (S.marginal c μ) x s₂} := by
  exact PrescribedExample.projection_double_dimensional morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) hs₂ h₂₁ hs₁

-- PAPER_ENTRY thm:gibbs_tau_omega_positive
/-! ### Lemma 4.6: Positivity of the Gibbs measures on the orientation sets

`thm:gibbs_tau_omega_positive`. -/

theorem paper_4_6 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s)
  (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
  (μ₁ (tau S.o '' S.SigmaTau μ) + μ₁ (omega S.o '' S.SigmaOmega μ) = 1 ∧
      μ₂ (omega S.o '' S.SigmaTau μ) + μ₂ (tau S.o '' S.SigmaOmega μ) = 1) ∧
    (μ₂ (tau S.o '' S.SigmaTau μ) = 0 ∧
        μ₂ (omega S.o '' S.SigmaOmega μ) = 0 ∧
          μ₁ (omega S.o '' S.SigmaTau μ) = 0 ∧ μ₁ (tau S.o '' S.SigmaOmega μ) = 0) ∧
      0 < μ₁ (tau S.o '' S.SigmaTau μ) ∧
        0 < μ₁ (omega S.o '' S.SigmaOmega μ) ∧ 0 < μ₂ (omega S.o '' S.SigmaTau μ) ∧ 0 < μ₂ (tau S.o '' S.SigmaOmega μ) := by
  exact System.gibbs_tau_omega_positive S morrisShmerkinLyapunov_holds equilibriumGibbs hrot hdiag hs0 hs2 μ hinv herg heq
    hdec

-- PAPER_ENTRY thm:conditional_two_ways
/-! ### Lemma 4.7: Conditional measures computed two ways

`thm:conditional_two_ways`. -/

theorem paper_4_7 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s)
  (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
  [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
  ∀ᵐ (y : ℤ → ι × ZMod 2) ∂avgMeasure μ₁ μ₂,
    (y ∈ tau S.o '' S.SigmaTau μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₁ (S.xiBar 1) y ∧
          condMeas μ₁ (S.xiBar 1) y = Measure.map (tau S.o) (condMeas μ (S.xi μ 1) (unCode y))) ∧
      (y ∈ omega S.o '' S.SigmaTau μ →
          condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₂ (S.xiBar 1) y ∧
            condMeas μ₂ (S.xiBar 1) y = Measure.map (omega S.o) (condMeas μ (S.xiPerp μ) (unCode y))) ∧
        (y ∈ omega S.o '' S.SigmaOmega μ →
            condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₁ (S.xiBar 1) y ∧
              condMeas μ₁ (S.xiBar 1) y = Measure.map (omega S.o) (condMeas μ (S.xi μ 1) (unCode y))) ∧
          (y ∈ tau S.o '' S.SigmaOmega μ →
            condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₂ (S.xiBar 1) y ∧
              condMeas μ₂ (S.xiBar 1) y = Measure.map (tau S.o) (condMeas μ (S.xiPerp μ) (unCode y))) := by
  exact System.conditional_two_ways_normalised S morrisShmerkinLyapunov_holds equilibriumGibbs hrot hdiag hs0 hs2 μ hinv
    herg heq hdec

-- PAPER_ENTRY thm:overline_h1_zero
/-! ### Lemma 4.8: Vanishing of the projective entropy h̄_1 below the threshold

`thm:overline_h1_zero`. -/

theorem paper_4_8 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
  (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
  (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
  (hent : entropy μ ≤ -S.lyapunov₁ μ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
  ∀ᵐ (y : ℤ → ι × ZMod 2) ∂avgMeasure μ₁ μ₂, S.dimEntropyBarAt (avgMeasure μ₁ μ₂) 1 y = 0 := by
  exact System.overline_h1_zero S morrisShmerkinLyapunov_holds equilibriumGibbs
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) fengInfoSumBar_holds
    fengLedrappierYoungBar_holds hrot hdiag hsep hs0 hs2 μ hinv herg heq hent hdec

-- PAPER_ENTRY thm:overline_h1_zero_large
/-! ### Lemma 4.9: Vanishing of h̄_1 and Dirac conditional measures in the large-entropy case

`thm:overline_h1_zero_large`. -/

theorem paper_4_9 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
  (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
  (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
  (hent₂ : entropy μ ≤ -S.lyapunov₂ μ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
  S.dimEntropyBar μ₂ 1 = 0 ∧
    ∀ᵐ (y : ℤ → ι × ZMod 2) ∂avgMeasure μ₁ μ₂,
      y ∈ S.slowPart μ → condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = Measure.dirac y := by
  exact System.overline_h1_zero_large S morrisShmerkinLyapunov_holds equilibriumGibbs
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) fengInfoSumBar_holds
    fengLedrappierYoungBar_holds hrot hdiag hsep hs0 hs2 μ hinv herg heq hent₂ hdec

-- PAPER_ENTRY thm:overline_h1_large
/-! ### Lemma 4.10: The projective entropy h̄_1 of the Gibbs measures equals h_1

`thm:overline_h1_large`. -/

theorem paper_4_10 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s)
  (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
  [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
  S.dimEntropyBar μ₁ 1 = S.dimEntropy μ 1 ∧
    ∀ᵐ (y : ℤ → ι × ZMod 2) ∂avgMeasure μ₁ μ₂,
      y ∈ S.fastPart μ → S.dimEntropyBarAt (avgMeasure μ₁ μ₂) 1 y = S.dimEntropyBar μ₁ 1 := by
  exact System.overline_h1_large S morrisShmerkinLyapunov_holds equilibriumGibbs fengInfoSum_holds
    fengInfoSumBar_holds hrot hdiag hs0 hs2 μ hinv herg heq hdec

-- PAPER_ENTRY thm:eq_state_h1_zero
/-! ### Proposition 4.11: h_1(μ) = 0 below the threshold

`thm:eq_state_h1_zero`. -/

theorem paper_4_11 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
  (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) (hent : entropy μ ≤ -S.lyapunov₁ μ) :
  S.dimEntropy μ 1 = 0 ∧ ∀ᵐ (x : ℤ → ι) ∂μ, condMeas μ (S.xi μ 1) x = Measure.dirac x := by
  exact System.eq_state_h1_zero S morrisShmerkinLyapunov_holds equilibriumGibbs fraserJordanJurgaDecomposition_holds
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) fengInfoSum_holds fengInfoSumBar_holds
    fengLedrappierYoungBar_holds hrot hdiag hsep hs0 hs2 μ hinv herg heq hent

-- PAPER_ENTRY thm:eq_state_h1_large
/-! ### Proposition 4.12: h_1(μ) = h_0(μ) + λ_1 above the threshold

`thm:eq_state_h1_large`. -/

theorem paper_4_12 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
  (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) (hent : -S.lyapunov₁ μ ≤ entropy μ) :
  S.dimEntropy μ 1 = entropy μ + S.lyapunov₁ μ := by
  exact System.eq_state_h1_large S morrisShmerkinLyapunov_holds equilibriumGibbs fraserJordanJurgaDecomposition_holds
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) fengInfoSum_holds fengInfoSumBar_holds
    fengLedrappierYoungBar_holds hrot hdiag hsep hs0 hs2 μ hinv herg heq hent

-- PAPER_ENTRY thm:eq_state_h2_zero
/-! ### Proposition 4.13: h_2(μ) = 0 below the threshold

`thm:eq_state_h2_zero`. -/

theorem paper_4_13 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
  (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) (hent : entropy μ ≤ -S.lyapunov₁ μ) :
  S.dimEntropy μ 2 = 0 := by
  exact System.eq_state_h2_zero S morrisShmerkinLyapunov_holds equilibriumGibbs fraserJordanJurgaDecomposition_holds
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) fengInfoSum_holds fengInfoSumBar_holds
    fengLedrappierYoungBar_holds hrot hdiag hsep hs0 hs2 μ hinv herg heq hent

-- PAPER_ENTRY thm:orto_partition_dirac
/-! ### Proposition 4.14: Dirac conditional measures on the orthogonal partition

`thm:orto_partition_dirac`. -/

theorem paper_4_14 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
  (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) (hent₂ : entropy μ ≤ -S.lyapunov₂ μ) :
  S.dimEntropy μ 2 = 0 := by
  exact System.orto_partition_dirac S morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds)
    fengInfoSum_holds fengInfoSumBar_holds fengLedrappierYoungBar_holds hrot hdiag hsep hs0 hs2 μ hinv herg heq
    hent₂

-- PAPER_ENTRY thm:SOSC_h2_zero
/-! ### Proposition 4.15: h_2(μ) = 0 under the strong open set condition

`thm:SOSC_h2_zero`. -/

theorem paper_4_15 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s : ℝ} (hrot : S.WithRotations) (hprox : S.Proximal) (hsosc : S.StrongOpenSet) (hs0 : 0 < s) (hs2 : s < 2)
  (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) : S.dimEntropy μ 2 = 0 := by
  exact System.SOSC_h2_zero S morrisShmerkinLyapunov_holds equilibriumGibbs fengInfoSum_holds hrot hprox hsosc hs0 hs2
    μ hinv herg heq

-- PAPER_ENTRY thm:main_extended
/-! ### Theorem 4.16: Dimension of the projected equilibrium state

`thm:main_extended`. -/

/-- Theorem 4.16, at the zero of the pressure, for every invariant equilibrium state. -/
theorem paper_4_16 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.dimaff < 2 → S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2 := by
  have := S.nontrivial_of_withRotations hrot
  exact S.main_extended morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds)
    fengInfoSum_holds fengInfoSumBar_holds fengLedrappierYoung_holds
    fengLedrappierYoungBar_holds hrot hprox hsep S.dimaff_pos S.pressure_dimaff μ hinv heq hor

/-- The case `s ≥ 2` under the strong open set condition. -/
theorem paper_4_16_ge_two {ι : Type u} (S : System ι) {s : ℝ} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] (hsosc : S.StrongOpenSet) (hs : 2 ≤ s) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
  [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
  IsExactDim (Measure.map S.proj μ) 2 := by
  exact System.main_extended_ge_two S hsosc hs hP μ hinv heq

-- PAPER_ENTRY rem:threshold_bound
/-! ### Remark 4.17: Lower bound min{dimaff(X), 2 - λ₁/λ₂} without the strong open set condition or projective exponential separation

`rem:threshold_bound`. -/

theorem paper_4_17 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps) (h9 : S.dimaff < 2)
  (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
  (heq : S.IsEquilibriumState S.dimaff μ) :
  ENNReal.ofReal (min S.dimaff (2 - S.lyapunov₁ μ / S.lyapunov₂ μ)) ≤ dimH S.attractor := by
  exact System.threshold_bound S shannonMcMillanBreiman morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds fengLedrappierYoung_holds kittleKoglerDimension_holds hrot hprox hfree
    h9 μ hinv heq

/-! ## Two unnumbered dimension consequences -/

theorem paper_rossi {ι : Type u_1} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ) :
  ∀ᵐ (y : ℝ × ℝ) ∂Measure.map S.proj μ,
    lowerLocalDim (Measure.map S.proj μ) y ≤ min 2 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ)) := by
  exact System.ae_lowerLocalDim_map_proj_le S herg

theorem modified_affinity_eq_of_hausdorff_eq {ι : Type u} [Fintype ι] [Nonempty ι] (S : BoxLike.System ι)
    (hH : dimH S.attractor = ENNReal.ofReal S.dimaff) : S.dimmaff = S.dimaff :=
  S.dimmaff_eq_dimaff S.fraserBound_holds hH

end Solution.Paper

end Manuscript

/-! ## Proofs in the independent challenge vocabulary

The statements below use the definitions of `Challenge.lean`, repeated in
`Solution/Definitions.lean`. `Solution.Transport` identifies that vocabulary with the
library vocabulary displayed above. The comparator checks Theorems A, B and 4.16 here.
-/

namespace Challenge

universe u

open MeasureTheory Solution.Transport

/-! ## Dimension of the projections of the equilibrium state -/

/-- Theorem A (`thm:main1`), for every `s`-equilibrium state with `s = dimaff(X)`. -/
theorem audit_main1 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ) (c : ZMod 2) :
    (S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ → IsDoubleDim (S.marginal c μ)) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep hinv heq
  simp only [isDoubleDim_iff, isExactDim_iff, marginal_eq, dimaff_eq, lyapunov₁_eq, lyapunov₂_eq]
  exact Solution.Paper.paper_A (toLib S) hrot hprox hsep μ hinv heq c

/-- Theorem 4.4 (`thm:eq_state_proj_dim`), for every `s`-equilibrium state, `s > 0`: the
pointwise dimension of each coordinate projection exists almost everywhere and takes at most the
two values `min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`, the upper packing and the
lower Hausdorff dimension, each on a set of positive measure. -/
theorem audit_eq_state_proj_dim {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) {s : ℝ}
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    BoxLike.HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) ∧
      0 < S.marginal c μ
        {x | BoxLike.HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₁ μ))} ∧
      0 < S.marginal c μ
        {x | BoxLike.HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₂ μ))} := by
  have hjr : BoxLike.JordanRapaportDimension.{u} :=
    BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, shift_eq,
    isEquilibriumState_iff] at hrot hprox hsep hinv heq
  simp only [upperPackingDim_eq, lowerHausdorffDim_eq, marginal_eq, entropy_eq,
    lyapunov₁_eq, lyapunov₂_eq]
  exact (toLib S).eq_state_proj_dim_all BoxLike.morrisShmerkinLyapunov_holds
    BoxLike.equilibriumGibbs BoxLike.fraserJordanJurgaDecomposition_holds
    hjr hrot hprox hsep hs0 μ hinv heq c

/-! ## Dimension of the equilibrium state and of the self-affine set -/

/-- Theorem B (`thm:main2`), for every `s`-equilibrium state with `s = dimaff(X)`: the dimension
formula under any of the three conditions, and the furthermore clause. -/
theorem audit_main2 {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet ∨
      S.ProjExpSeparation) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) ∧
      (S.ProjExpSeparation → S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet →
        IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2) := by
  simp only [withRotations_iff, proximal_iff, noExactOverlaps_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, lyapunov₁_eq, lyapunov₂_eq, strongOpenSet_iff, projExpSeparation_iff]
    at hrot hprox hfree hinv heq hor
  rw [attractor_eq, dimaff_eq]
  simp only [projExpSeparation_iff, strongOpenSet_iff, isExactDim_iff, proj_eq,
    lyapunov₁_eq, lyapunov₂_eq]
  exact Solution.Paper.paper_B (toLib S) hrot hprox hfree μ hinv heq hor

/-- Theorem 4.16 (`thm:main_extended`), for every `s`-equilibrium state with `s = dimaff(X)`. -/
theorem audit_main_extended {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι)
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.dimaff < 2 → S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2 := by
  simp only [withRotations_iff, proximal_iff, projExpSeparation_iff, dimaff_eq, shift_eq,
    isEquilibriumState_iff, entropy_eq, lyapunov₂_eq, strongOpenSet_iff]
    at hrot hprox hsep hinv heq hor
  rw [isExactDim_iff, proj_eq, dimaff_eq]
  exact Solution.Paper.paper_4_16 (toLib S) hrot hprox hsep μ hinv heq hor

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
