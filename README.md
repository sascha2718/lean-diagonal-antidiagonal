# Hausdorff dimension of planar box-like self-affine sets with rotations

Lean 4 formalisation of the paper

> Antti Käenmäki, R. Dániel Prokaj, Károly Simon and Sascha Troscheit,
> *Hausdorff dimension of planar box-like self-affine sets with rotations*, arXiv:XXXX.XXXXX
> (placeholder identifier until the paper is posted).

## The paper

A planar box-like self-affine set with rotations is the attractor of finitely many contracting
affine maps of the plane whose linear parts are diagonal or anti-diagonal, with both types
present. Up to a linear change of coordinates these are the proximal planar systems that are
irreducible but not strongly irreducible, the case between the strongly irreducible systems of
Hochman–Rapaport (Theorem 1.1) and the diagonal systems of Rapaport (Theorem 1.2). Let `μ` be
the unique equilibrium state at the affinity dimension `s = dimaff(X)`, with Lyapunov exponents
`λ₂ ≤ λ₁ < 0`. Under a projective exponential separation condition, the paper shows that the
coordinate projections of `π_*μ` are double-dimensional if `s < 2 - λ₁/λ₂`, their pointwise
dimension existing almost everywhere and taking exactly two values, each on a set of positive
measure, and exact-dimensional of dimension one otherwise (Theorem A); the two values are
identified in Theorem 4.4. Assuming only that the projected maps have no exact overlaps, the
Hausdorff dimension of `X` equals `min{2, dimaff(X)}` whenever (i) `dimaff(X) ≤ 2 - λ₁/λ₂`,
or (ii) the strong open set condition holds, or (iii) the projective exponential separation
condition holds; if (iii) holds together with (i) or (ii), then `π_*μ` is exact-dimensional of
dimension `dimaff(X) ≤ 2` (Theorem B, whose last clause is Theorem 4.16). For `dimaff(X) < 2`
and without (ii) and (iii), the proof still gives `dim_H X ≥ min{dimaff(X), 2 - λ₁/λ₂}`
(Remark 4.17). The paper also shows that the projective exponential separation condition is not
implied by the strong separation condition, even when the projected maps generate a free
semigroup (Proposition 2.7), and poses Question 1.4: can the coordinate projections of the
equilibrium state be exact-dimensional, with their two Gibbs components of equal dimension,
below the threshold `2 - λ₁/λ₂` when the projective system has no exact overlaps?

## The formalisation

[Challenge.lean](Challenge.lean) states Theorems A, B and 4.16 over Mathlib alone, with the
42 definitions their statements need, and [Solution.lean](Solution.lean) proves them for the full
parameter range of the paper and for every invariant equilibrium state. The library `BoxLike/`
covers all 44 numbered statements of the paper, with one entry per statement in
`Solution.lean`: 42 are formalised, among them Theorem 1.2, Rapaport's theorem, proved in
`BoxLike/Rapaport/`; Theorem 1.1, the theorem of Hochman–Rapaport that the paper cites, is
recorded as the `Prop`-valued statement `HochmanRapaportDimension` and is not proved; Question
1.4 is recorded as the proposition `CoincidentProjectionDimensionsQuestion`, with no answer
claimed. The library has no `sorry` and no axiom beyond `propext`, `Classical.choice` and
`Quot.sound`. No headline statement takes a literature hypothesis. Every result the paper cites
is proved in the library, except Hochman–Rapaport's theorem, which nothing uses.

- M. Hochman and A. Rapaport, *Hausdorff dimension of planar self-affine sets and measures with
  overlaps*, J. Eur. Math. Soc. 24 (2022): Theorem 1.1 (Theorem 1.1 of the paper), stated as
  `HochmanRapaportDimension`, not proved; nothing uses it,
  `BoxLike/LiteratureHochmanRapaport.lean`.
- A. Rapaport, *Dimension of diagonal self-affine sets and measures via non-conformal
  partitions*, arXiv:2309.03985: Theorem 1.3 in the plane (Theorem 1.2 of the paper), stated as
  `RapaportDiagonalDimension` in `BoxLike/LiteratureRapaport.lean` and proved as
  `Rapaport.rapaportDiagonalDimension_holds` in `BoxLike/Rapaport/`, along his Sections 2 to 7
  (the declaration index of [docs/correspondence.md](docs/correspondence.md) maps his statements
  to the modules). Case (iii) of Theorem B applies it to homogeneous diagonal subsystems.
- J. M. Fraser, *On the packing dimension of box-like self-affine sets in the plane*,
  Nonlinearity 25 (2012): Theorem 2.3 and Corollary 2.5 (Theorem 1.3 of the paper),
  `BoxLike/Fraser/`.
- D.-J. Feng and A. Käenmäki, *Equilibrium states of the pressure function for products of
  matrices*, Discrete Contin. Dyn. Syst. 30 (2011): Proposition 1.2 (Proposition 3.10),
  `BoxLike/QuasiMultiplicative/`.
- J. M. Fraser, T. Jordan and N. Jurga, *Dimensions of equilibrium measures on a class of planar
  self-affine sets*, J. Fractal Geom. 7 (2020): Lemma 1.3 and Corollaries 1.5 and 1.6
  (Proposition 3.14), `BoxLike/FraserJordanJurga/`.
- I. D. Morris and P. Shmerkin, *On equality of Hausdorff and affinity dimensions, via
  self-affine measures on positive subsystems*, Trans. Amer. Math. Soc. 371 (2019): Theorem 3.1,
  the distinct Lyapunov exponents of the equilibrium state, `BoxLike/MorrisShmerkin.lean`.
- D.-J. Feng, *Dimension of invariant measures for affine iterated function systems*, Duke
  Math. J. 172 (2023): Theorems 1.2 and 1.3, the Ledrappier–Young formula (Theorem 4.2), proved
  in the plane, and Lemma 4.6, `BoxLike/FengLedrappierYoung.lean`, `BoxLike/FengIdentity.lean`.
- D.-J. Feng and H. Hu, *Dimension theory of iterated function systems*, Comm. Pure Appl.
  Math. 62 (2009): Theorem 2.8, `BoxLike/FengHu.lean`.
- T. Jordan and A. Rapaport, *Dimension of ergodic measures projected onto self-similar sets
  with overlaps*, Proc. Lond. Math. Soc. (3) 122 (2021): Theorem 1.1,
  `BoxLike/JordanRapaport.lean`.
- P. Shmerkin, *On Furstenberg's intersection conjecture, self-similar measures, and the `L^q`
  norms of convolutions*, Ann. of Math. (2) 189 (2019): Theorem 6.6, the input of
  Jordan–Rapaport's proof, `BoxLike/Shmerkin/`. Bourgain's structure theorem (Shmerkin's
  Theorem 3.1) is proved in a weak form, with some positive doubling exponent in place of
  `2^{-2T-1}`, which suffices.
- S. Kittle and C. Kogler, *The exact overlaps conjecture for self-similar measures on the real
  line*, arXiv:2610.10511: Theorem 1.1, derived from the authors' Lean formalisation, carried
  verbatim in [vendor/](vendor/README.md), `BoxLike/KittleKogler.lean`.
- B. Bárány and A. Käenmäki, *Super-exponential condensation without exact overlaps*, Adv.
  Math. 379 (2021): the condensation theorem (Theorem 2.1) in the form the proof of
  Proposition 2.7 uses, `BoxLike/BaranyKaenmaki.lean`.
- E. Rossi, *Local dimensions of measures on infinitely generated self-affine sets*, J. Math.
  Anal. Appl. 413 (2014): Theorem 2.2, `BoxLike/Rossi.lean`.
- K. J. Falconer, *The Hausdorff dimension of self-affine fractals*, Math. Proc. Cambridge
  Philos. Soc. 103 (1988): the upper bound `min{2, dimaff(X)}`, `BoxLike/FalconerBound.lean`.

The library also proves the ergodic theorems the paper uses: Birkhoff, Kingman, Oseledets for
invertible planar cocycles, Shannon–McMillan–Breiman, the Kolmogorov–Sinai generator theorem,
and Bowen's theorem on Gibbs measures of Hölder potentials on the mixing sub-shift.

[docs/correspondence.md](docs/correspondence.md) records the correspondence with the paper
statement by statement, with the proof deviations, and
[paper-correspondence.yaml](paper-correspondence.yaml) fingerprints every numbered statement.

## Build and checks

Lean and Mathlib are pinned to `v4.35.0-rc2`. On this machine `.lake/packages` is shared with
other projects: do not run `lake update`. On a fresh checkout run `lake exe cache get` first.

```bash
lake build BoxLike Challenge Solution
lake env lean tools/AuditAxioms.lean
python3 -B scripts/check_module_headers.py
python3 -B scripts/check_challenge_vocabulary.py
python3 -B scripts/check_solution_entries.py --require-complete
python3 -B scripts/check_paper_correspondence.py
./comparator-audit.sh --local-unsandboxed
```

All pass on the current tree; the only build warnings are the three `sorry` of `Challenge.lean`.
The comparator run is local and unsandboxed, not a Palomar verdict; on Linux omit
`--local-unsandboxed`.

## Licence

Apache License 2.0 ([LICENSE](LICENSE)); see [CITATION.cff](CITATION.cff). Provenance is in
[formalization.yaml](formalization.yaml).
