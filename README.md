# Hausdorff dimension of planar box-like self-affine sets with rotations

Lean 4 formalisation of *Hausdorff dimension of planar box-like self-affine sets with rotations*
by Antti Käenmäki, R. Dániel Prokaj, Károly Simon and Sascha Troscheit (2026).

## Scope

The library proves dimension formulas for proximal planar self-affine systems with diagonal
and anti-diagonal linear parts, with both types present. Let `X` be the attractor, `μ` its
symbolic equilibrium state at the affinity dimension `s = dimaff(X)`, and `λ₂ ≤ λ₁ < 0` its
Lyapunov exponents.

- **Coordinate projections (Theorem A):** under projective exponential separation, the
  coordinate projections of `π_*μ` are double-dimensional when `s < 2 - λ₁/λ₂`: their pointwise
  dimension exists almost everywhere and takes two distinct values, each on a set of positive
  measure. At and above the threshold, both projections are exact-dimensional of dimension one.
- **Hausdorff dimension (Theorem B):** if the projected maps have no exact overlaps, then
  `dim_H X = min{2, s}` whenever `s ≤ 2 - λ₁/λ₂`, the strong open set condition holds, or
  projective exponential separation holds. Under projective exponential separation together
  with either of the first two conditions, `π_*μ` is exact-dimensional of dimension `s ≤ 2`.
- **Equilibrium measure (Theorem 4.16):** if the entropy satisfies `h(μ) ≤ -λ₂` or the strong
  open set condition holds, then `π_*μ` is exact-dimensional of dimension `s ≤ 2`, assuming
  projective exponential separation when `s < 2`.

Supporting results include the Gibbs decomposition of the equilibrium state, the two projection
dimensions (Theorem 4.4), the lower bound of Remark 4.17, and the separation counterexample of
Proposition 2.7.

## Statements and proofs

[Challenge.lean](Challenge.lean) states the three headline results using Mathlib alone, with
the definitions needed to read them independently of the proof library. Each theorem has an
intentional `sorry` placeholder:

| Result | Endpoint |
| --- | --- |
| A Coordinate projections | `Challenge.audit_main1` |
| B Hausdorff dimension | `Challenge.audit_main2` |
| 4.16 Equilibrium measure | `Challenge.audit_main_extended` |

[Solution.lean](Solution.lean) proves these statements from [BoxLike](BoxLike.lean), for the
full parameter range and every invariant equilibrium state. It displays the definitions,
then states the numbered results explicitly in manuscript order, with proofs applying the
library. Its `recall` blocks check the displayed definitions against the library; recursive
definitions are displayed through their defining equations. The final section retains the
independent challenge statements for the comparator. The library and Solution contain
no `sorry`. No literature result is assumed as an axiom or left as a hypothesis of the headline
theorems. [comparator-config.json](comparator-config.json) selects the three declarations and
permits only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

**Coverage:** 42 of the 44 numbered statements are formalised, including Rapaport's theorem
(Theorem 1.2), proved in [BoxLike/Rapaport](BoxLike/Rapaport/). Hochman–Rapaport's theorem
(Theorem 1.1) is stated but unproved and is not used by the proofs. Question 1.4 is recorded as
an open question. Solution has an entry for each numbered statement.

[docs/correspondence.md](docs/correspondence.md) gives the detailed correspondence, literature
references and differences in statements and proofs. [paper-correspondence.yaml](paper-correspondence.yaml)
identifies the manuscript revision and maps its numbered statements. The module index in
[BoxLike.lean](BoxLike.lean) describes the library's organisation.

## Literature results

The library contains proofs of the following results in the indicated forms. Theorem numbers
refer to the linked sources; proof differences are recorded in [docs/correspondence.md](docs/correspondence.md).

| Source | Result formalised | Lean proof |
| --- | --- | --- |
| A. Rapaport, [*Dimension of diagonal self-affine sets and measures via non-conformal partitions*](https://arxiv.org/abs/2309.03985v1) (2023) | Theorem 1.3, in the plane | [Rapaport](BoxLike/Rapaport/) |
| J. M. Fraser, [*On the packing dimension of box-like self-affine sets in the plane*](https://arxiv.org/abs/1108.2639v1), Nonlinearity 25 (2012) | Theorem 2.3 and Corollary 2.5 | [Fraser](BoxLike/Fraser/) |
| D.-J. Feng and A. Käenmäki, [*Equilibrium states of the pressure function for products of matrices*](https://arxiv.org/abs/1009.3129v1), DCDS 30 (2011) | Proposition 1.2 | [QuasiMultiplicative](BoxLike/QuasiMultiplicative/) |
| J. M. Fraser, T. Jordan and N. Jurga, [*Dimensions of equilibrium measures on a class of planar self-affine sets*](https://arxiv.org/abs/1706.06833v2), J. Fractal Geom. 7 (2020) | Lemma 1.3 and Corollaries 1.5–1.6, the Gibbs decomposition | [FraserJordanJurga](BoxLike/FraserJordanJurga/) |
| I. D. Morris and P. Shmerkin, [*On equality of Hausdorff and affinity dimensions, via self-affine measures on positive subsystems*](https://arxiv.org/abs/1602.08789v3), Trans. Amer. Math. Soc. 371 (2019) | Theorem 3.1, distinct Lyapunov exponents | [MorrisShmerkin](BoxLike/MorrisShmerkin.lean) |
| D.-J. Feng, [*Dimension of invariant measures for affine iterated function systems*](https://arxiv.org/abs/1901.01691v2), Duke Math. J. 172 (2023) | Theorems 1.2(ii) and 1.3, the planar Ledrappier–Young formula; Lemma 4.6 | [FengLedrappierYoung](BoxLike/FengLedrappierYoung.lean), [FengIdentity](BoxLike/FengIdentity.lean), [FengIdentityBar](BoxLike/FengIdentityBar.lean) |
| D.-J. Feng and H. Hu, [*Dimension theory of iterated function systems*](https://arxiv.org/abs/1002.2036v1), Comm. Pure Appl. Math. 62 (2009) | Theorem 2.8, exact dimensionality for the self-similar projections used here | [FengHu](BoxLike/FengHu.lean) |
| T. Jordan and A. Rapaport, [*Dimension of ergodic measures projected onto self-similar sets with overlaps*](https://arxiv.org/abs/1908.00271v2), Proc. Lond. Math. Soc. 122 (2021) | Theorem 1.1 | [JordanRapaport](BoxLike/JordanRapaport.lean) |
| P. Shmerkin, [*On Furstenberg's intersection conjecture, self-similar measures, and the L^q norms of convolutions*](https://arxiv.org/abs/1609.07802v3), Ann. of Math. 189 (2019) | Theorem 6.6, the `L^q`-dimension lower bound; Theorem 3.1 (Bourgain) with a weaker positive doubling exponent | [Shmerkin](BoxLike/Shmerkin/) |
| B. Bárány and A. Käenmäki, [*Super-exponential condensation without exact overlaps*](https://arxiv.org/abs/1910.04623v4), Adv. Math. 379 (2021) | Theorem 2.1 in the corrected form for `n ≥ 5`, and the bound `Δ_n ≤ C₀ exp(-n²)` used here | [BaranyKaenmaki](BoxLike/BaranyKaenmaki.lean) |
| E. Rossi, [*Local dimensions of measures on infinitely generated self-affine sets*](https://doi.org/10.1016/j.jmaa.2013.12.030), J. Math. Anal. Appl. 413 (2014) | The upper Hausdorff dimension bound from Theorem 2.2, for box-like systems | [Rossi](BoxLike/Rossi.lean), [RossiBound](BoxLike/RossiBound.lean) |
| K. J. Falconer, [*The Hausdorff dimension of self-affine fractals*](https://doi.org/10.1017/S0305004100064926), Math. Proc. Cambridge Philos. Soc. 103 (1988) | The affinity-dimension upper bound for Hausdorff and upper Minkowski dimensions, in the plane | [FalconerBound](BoxLike/FalconerBound.lean), [Planar/FalconerBound](BoxLike/Planar/FalconerBound.lean) |
| R. Bowen, [*Equilibrium states and the ergodic theory of Anosov diffeomorphisms*](https://doi.org/10.1007/BFb0081279), LNM 470 (1975), Chapter 1 | Existence and uniqueness of the ergodic Gibbs measure for Hölder potentials on the mixing subshift used here | [Bowen](BoxLike/Bowen/Main.lean) |
| S. Kittle and C. Kogler, [*The exact overlaps conjecture for self-similar measures on the real line*](https://arxiv.org/abs/2610.10511) (2026) | Theorem 1.1, derived from the authors' Lean library [ExactOverlaps](vendor/README.md), vendored verbatim | [KittleKogler](BoxLike/KittleKogler.lean) |

The library also proves [Birkhoff's pointwise](BoxLike/Birkhoff.lean) and
[Kingman's subadditive](BoxLike/Kingman.lean) ergodic theorems,
[Oseledets' theorem for invertible planar cocycles](BoxLike/Planar/OseledetsTheorem.lean),
[Shannon–McMillan–Breiman for the finite-alphabet shift](BoxLike/ShannonMcMillanBreiman.lean),
and the [Kolmogorov–Sinai generator theorem for that shift](BoxLike/KolmogorovSinai.lean).

## Build and verification

Lean and Mathlib are pinned to `v4.35.0-rc2`. On a fresh independent checkout, obtain the
dependencies with `lake exe cache get`, then run:

```bash
lake build BoxLike Challenge Solution
lake env lean tools/AuditAxioms.lean
python3 -B scripts/check_module_headers.py
python3 -B scripts/check_challenge_vocabulary.py
python3 -B scripts/check_solution_entries.py --require-complete
python3 -B scripts/check_paper_correspondence.py
```

The three Challenge warnings are intentional. The correspondence check needs
`../diagonal-antidiagonal.tex`; it checks source drift and declaration consistency, not
mathematical equivalence. This workstation shares `.lake/packages` with other projects, so
do not run `lake update` or replace those dependencies there.

On Linux, `./comparator-audit.sh` runs the sandboxed Comparator with the Lean kernel, NanoDa
and con-ron. On macOS, `./comparator-audit.sh --local-unsandboxed` provides a local development
check without Linux sandbox isolation. The [build workflow](.github/workflows/build.yml)
builds the library and runs the Comparator audit. The
[Palomar preflight](.github/workflows/palomar-preflight.yml) runs the registry verifier on
demand; local checks do not establish Palomar acceptance.

## Licence

The Lean sources use the [Apache License 2.0](LICENSE), with the vendored library's licences
recorded in [vendor/README.md](vendor/README.md). Citation details are in
[CITATION.cff](CITATION.cff); [formalization.yaml](formalization.yaml) records authorship,
sources, AI assistance and review.
