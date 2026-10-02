# Hausdorff dimension of planar box-like self-affine sets with rotations

This repository contains the Lean 4 formalisation of *Hausdorff dimension of planar box-like
self-affine sets with rotations* by Demi Allen, Antti Käenmäki, R. Dániel Prokaj, Károly Simon
and Sascha Troscheit. It develops the symbolic coding of planar box-like self-affine sets with
rotations, the thermodynamic formalism of the singular value function, the entropies and
conditional measures of Feng's Ledrappier–Young theory, and the dimension theory of the
equilibrium state and of the attractor.

- **Paper:** arXiv:XXXX.XXXXX (placeholder). Theorem numbers below refer to the current
  manuscript.
- **Palomar:** PALOMAR-XXXX-XX-XX-XXXXXX (placeholder).

<!-- TODO(authors): insert the arXiv link and its version, and the Palomar entry, once they
exist; then add the sentence on the archived snapshot, as in the JA-ST formalisation. -->

## Formalised results

Let `X` be a proximal box-like self-affine set with rotations that satisfies the projective
exponential separation condition, and let `μ` be an `s`-equilibrium state, with entropy `h_0(μ)`
and Lyapunov exponents `λ_1`, `λ_2`.

- **Projections of the equilibrium state (Theorem 1.2):** for `s = dimaff(X) < 2` the
  coordinate projections of `μ` are double-dimensional. They fail to be exact-dimensional
  precisely when `s < 2 - λ_1/λ_2`, and at and above this threshold they are exact-dimensional
  of dimension one.
- **Dimensions of the projections (Theorem 4.4):** for `0 < s < 2` the upper packing and lower
  Hausdorff dimensions of both projections are `min{1, -h_0(μ)/λ_1}` and `min{1, -h_0(μ)/λ_2}`.
- **Hausdorff dimension (Theorem 1.3):** if `dimaff(X) < 2`, and either
  `dimaff(X) ≤ 2 - λ_1/λ_2` or `X` satisfies the strong open set condition, then
  `dim_H X = dimaff(X)`.
- **Dimension of the projected equilibrium state (Theorem 4.16):** for `s = dimaff(X)`, if
  `h_0(μ) ≤ -λ_2` or `X` satisfies the strong open set condition, then `π_*μ` is
  exact-dimensional of dimension `min{2, dimaff(X)}`. The case `s ≥ 2`, which needs only the
  strong open set condition, is a separate statement.
- **Dimension formula (Section 4.1):** under the hypotheses of Theorem 4.16,
  `dim_H X = min{2, dimaff(X)}`. Under the strong open set condition alone, `dimaff(X) ≥ 2`
  gives `dim_H X = 2`.

The library also proves every other labelled lemma and proposition of the paper, some of them
from the cited theorems listed below, with three exceptions: Propositions 3.10 and 3.13, which
the paper cites and whose content enters as hypotheses, and Lemma 3.6, which the paper uses
only for the identity `h_0(μ) = h(μ)`, proved directly in the library. It also proves
Falconer's upper bound, the existence of equilibrium states for every `s ≥ 0`, Example 4.5
apart from its explicit Lyapunov exponents and numerical values, and the chain
`dim_H X = dim_P X = dim_M X = dimaff(X)` of the introduction.

## Statements and proofs

[Challenge.lean](Challenge.lean) states the seven headline results using Mathlib alone, with
the definitions needed to read them independently of the library. Each theorem has an
intentional `sorry` placeholder. [Solution.lean](Solution.lean) proves these statements from the
library; the solution and the library contain no `sorry`.

The headline results are proved conditionally on eight theorems that the paper cites without
proof. Each is a `Prop`-valued definition, stated in `Challenge.lean` with its citation, and the
audited theorems take it as a hypothesis:

- `MorrisShmerkinLyapunov`: Morris–Shmerkin, Trans. Amer. Math. Soc. 371 (2019), Theorem 3.1;
  the Lyapunov exponents of the equilibrium state are distinct.
- `FengKaenmakiGibbs`: Feng–Käenmäki, Discrete Contin. Dyn. Syst. 30 (2011), Proposition 1.2;
  the Gibbs bounds of Proposition 3.10.
- `FraserJordanJurgaDecomposition`: Fraser–Jordan–Jurga, J. Fractal Geom. 7 (2020), Lemma 1.3
  and Corollaries 1.5 and 1.6; the decomposition of Proposition 3.13.
- `JordanRapaportDimension`: Jordan–Rapaport, Proc. Lond. Math. Soc. 122 (2021), Theorem 1.1;
  the dimension of projected ergodic measures under exponential separation.
- `FengInfoSum`, `FengInfoSumBar`: Feng, Duke Math. J. 172 (2023), Lemma 4.6, the first identity
  of (4.16), for the planar and the projective partitions.
- `FengLedrappierYoung`, `FengLedrappierYoungBar`: Feng, Duke Math. J. 172 (2023), Theorems 1.2
  and 1.3; the Ledrappier–Young formula of Theorem 4.2, for the plane and for the projective
  system.

Theorems 1.2 and 4.4 take the first four. Theorems 1.3 and 4.16 and the dimension formula take
all eight. The cases `s ≥ 2` and `dimaff(X) ≥ 2` take none. Off the main line, Theorem 1.1,
Proposition 2.7, the uniqueness part of Proposition 3.10 and the double-dimensionality of the
projections without separation rest on further cited theorems, also taken as hypotheses
(Fraser; Bárány–Käenmäki; Feng–Käenmäki; Feng–Hu); no audited theorem uses them. Falconer's
upper bound, which the paper also cites, is proved.

The Comparator check verifies that the solution proves the same statements with the same
definitions, using only `propext`, `Classical.choice` and `Quot.sound`. The library declares no
axiom. [comparator.json](comparator.json) specifies the seven declarations and permitted axioms;
the [verification workflow](.github/workflows/build.yml) builds the library and runs the
comparator audit, [comparator-audit.sh](comparator-audit.sh).

[paper-correspondence.yaml](paper-correspondence.yaml) gives the correspondence between the
paper and Lean: one entry per labelled theorem, proposition, lemma and example, entries for
results stated in running text, and the literature hypotheses that each result takes. The
[correspondence checker](scripts/check_paper_correspondence.py) checks it against the manuscript
`diagonal-antidiagonal.tex` in the parent directory, the Lean sources,
[comparator.json](comparator.json) and [formalization.yaml](formalization.yaml).
[PLAN.md](PLAN.md) records the state of every labelled result, the findings about the manuscript
and the comparison of the literature hypotheses with their sources.

## Library

The development is one library, [BoxLike](BoxLike.lean), built on Mathlib alone; its root module
lists every file. Its main parts are:

- symbolic coding and box-like systems: the two-sided shift, the sub-shift `Σ_Z`, the codings
  `τ` and `ω`, the projective system, the canonical projections and the separation conditions;
- thermodynamic formalism: the singular value function, the pressure and the affinity dimension,
  equilibrium states and their existence, Lyapunov exponents, and Gibbs measures on `Σ_Z`;
- dimension theory: Minkowski and packing dimensions of sets, pointwise dimensions of measures,
  exact- and double-dimensional measures, Falconer's bound and the mass distribution principle;
- ergodic theory and entropy: Birkhoff's ergodic theorem, conditional measures along measurable
  partitions, and the entropies `h_i` of the Ledrappier–Young formula;
- the main results, in `General`, `AffinityMain`, `MainTwo`, `MainExtended` and
  `DimensionFormula`, and the cited theorems, in `Literature`, `LiteratureFeng` and
  `LiteratureRemarks`.

`lake build` builds the library, and `lake build Solution` the proofs of the headline results.

## Attribution and licence

The Lean development was carried out by Sascha Troscheit, one of the authors of the paper. AI
tools were used extensively in the Lean development.

The Lean development is distributed under the [Apache License 2.0](LICENSE).
