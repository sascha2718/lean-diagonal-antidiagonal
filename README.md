# Hausdorff dimension of planar box-like self-affine sets with rotations

Lean 4 formalisation accompanying the manuscript by Demi Allen, Antti Käenmäki,
R. Dániel Prokaj, Károly Simon and Sascha Troscheit.

## Coverage

All 41 numbered statements have an entry in [Solution.lean](Solution.lean), with explicit
literature dependencies, scope gaps and deviations from the prose proof. The assessment is
39 formalised, 1 cited (Theorem 4.2 of Feng) and 1 open question (Question 1.4).
[paper-correspondence.yaml](paper-correspondence.yaml) fingerprints the 41 numbered statements
and 45 prose spans; over all 86 items its manifest reads 83 formalised, 2 cited and
1 intentionally unformalised, with 3 literature hypotheses. A valid fingerprint or an entry in
Solution is not by itself evidence of mathematical equivalence.

**Every numbered statement is formalised or cited, except Question 1.4, which is open.** No result
rests on an unauthorised premise. Theorem 1.1 (Fraser, Theorem 2.3 and Corollary 2.5) is proved
along Fraser's proof with no literature premise (`System.fraserBound_holds`,
`System.fraserROSC_holds`). Proposition 3.10 is proved with no literature premise for every
irreducible tuple in `GL_2(ℝ)^N`, from `FengKaenmakiNormEquilibrium` (Feng–Käenmäki, Proposition
1.2, in the form of the source), which the library proves (`fengKaenmakiNormEquilibrium_holds`), and
for every box-like tuple with rotations, irreducible or not. Theorem 4.2 is stated for every planar
self-affine set from the authorised premise `PlanarFengLedrappierYoung` (Feng, Theorems 1.2 and
1.3), which no headline takes; its second part, the scalar formula `FengLedrappierYoungBar`, follows
from the first (`fengLedrappierYoungBar_of_fengLedrappierYoung`). Proposition 3.14
(Fraser–Jordan–Jurga), the distinct Lyapunov exponents `eq:simple_lyapunov` (Morris–Shmerkin) and
Rossi's bound `eq:hausdorff_ergodic_lyapunov` are proved with no literature premise.
Kittle–Kogler's dimension formula for self-similar measures on the line without exact overlaps,
which the proof of Theorem 1.3 uses, is derived from its authors' Lean formalisation of
arXiv:2610.10511, the library `ExactOverlaps` in `vendor/` (`kittleKoglerDimension_holds`).
Shmerkin's theorem on the `L^q` dimension of self-similar measures, the input of Jordan–Rapaport's
argument, is proved along the source (`shmerkinLqDimension_holds`, `BoxLike/Shmerkin.lean`).
Feng–Hu's exact-dimensionality theorem for the projections of ergodic measures, behind the remark
that the coordinate marginals are double-dimensional without separation, is proved along Feng–Hu's
density argument (`fengHuExactDim_holds`). Bárány–Käenmäki's condensation theorem, behind
Proposition 2.7, is proved in the form the paper uses, a free pair with `Δ_n ≤ C_0 exp(-n²)` for
all `n ≥ 1` (`NoOverlap.baranyKaenmakiPair_holds`); Theorem 2.1 of the source as stated is false
(`NoOverlap.not_baranyKaenmakiTheorem`), see "Remaining work" in
[docs/correspondence.md](docs/correspondence.md).

[docs/correspondence.md](docs/correspondence.md) records the coverage assessment, literature
inputs and proof deviations.

## Headline results

[Challenge.lean](Challenge.lean) states the three headline theorems over Mathlib alone, with
the 42 definitions their statements need; no headline takes a literature hypothesis. Solution
proves all three for the full parameter range of the manuscript.

| Endpoint | Manuscript | Solution | Literature inputs |
|---|---|---|---|
| `Challenge.audit_main1` | Theorem 1.2 | proved | None |
| `Challenge.audit_main2` | Theorem 1.3 | proved | None |
| `Challenge.audit_main_extended` | Theorem 4.16 | proved | None |

Feng's information-sum identity, `FengInfoSum` and `FengInfoSumBar`, is a theorem of the library
(`fengInfoSum_holds`, `fengInfoSumBar_holds`) and is not a hypothesis of any headline result.
The decomposition of Proposition 3.14, `FraserJordanJurgaDecomposition`, is likewise a theorem
of the library (`fraserJordanJurgaDecomposition_holds` in
[BoxLike/FraserJordanJurga/Main.lean](BoxLike/FraserJordanJurga/Main.lean)) and is not a
hypothesis of any headline result. Bowen's theorem gives the ergodic Gibbs measure `μ_1` of
`f_{1,s}` on `Σ_Z`, and `μ_2` is its image under the exchange of the axes; the image of `μ_1`
under forgetting the axis has the Gibbs bounds of `φ^s`, and every invariant measure with these
bounds equals it; the four decompositions follow from `Σ_Z = τ(Σ) ⊔ ω(Σ)`, and the Lyapunov
identities from Birkhoff's theorem along the two lifts and a relative-entropy comparison.

Feng's planar Ledrappier–Young formula, `PlanarFengLedrappierYoung` for every planar self-affine
system and its box-like form `FengLedrappierYoung`, is proved (`planarFengLedrappierYoung_holds`
and `fengLedrappierYoung_holds` in
[BoxLike/FengLedrappierYoung.lean](BoxLike/FengLedrappierYoung.lean)) along Feng's Sections 4 to
6 in the plane: the claims (C1) to (C3) by general theorems about nested measurable partitions,
Proposition 5.1 from the planar form of Lemma 5.4, and Proposition 5.5 by Besicovitch
differentiation on the atoms and the weak maximal inequality. The library statements take
`FengLedrappierYoung` as a hypothesis and Solution discharges it; no headline takes it.

Feng's scalar Ledrappier–Young formula `FengLedrappierYoungBar`, which the proof of Theorem 4.16
uses, follows from the planar formula `FengLedrappierYoung`
(`fengLedrappierYoungBar_of_fengLedrappierYoung` in
[BoxLike/ProjectiveLineSystem.lean](BoxLike/ProjectiveLineSystem.lean)): the planar system
`z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` of the projective system has its attractor on the
horizontal axis, its partitions `ξ_2` and `ξ_1` agree and its entropies are the projective ones,
so that the planar formula reduces to the scalar one for every box-like system, with neither
rotations nor proximality (`System.isExactDim_map_projBar_of_fengLedrappierYoung`). It is not a
hypothesis of any headline result.

The inputs the manuscript takes from Feng–Käenmäki and Morris–Shmerkin are theorems of the
library too, and no headline takes them. `EquilibriumGibbsStatement`, the Gibbs bounds of every
invariant `s`-equilibrium state of a box-like tuple with rotations for `0 < s < 2`, is
`equilibriumGibbs` ([BoxLike/EquilibriumGibbs.lean](BoxLike/EquilibriumGibbs.lean)): every such
state equals the image of `μ_1` under forgetting the axis, since the equilibrium equation and the
lower Gibbs bound bound the relative entropy of the cylinder partitions, which gives absolute
continuity, and the image is ergodic. The same argument gives Proposition 3.10 for every
box-like tuple with rotations and every `s > 0` (`System.irred_eq_state_of_withRotations`).
`MorrisShmerkinLyapunov`, the statement of `eq:simple_lyapunov`, is `morrisShmerkinLyapunov_holds`
([BoxLike/MorrisShmerkin.lean](BoxLike/MorrisShmerkin.lean)), along Morris–Shmerkin's Lemmas 3.4
and 3.5. The library statements take both as hypotheses and Solution discharges them.

Kittle–Kogler's Theorem 1.1, `KittleKoglerDimension`, the dimension `min{1, H(p)/|χ|}` of a
self-similar measure on the line whose similarities generate a free semigroup, is
`kittleKoglerDimension_holds` ([BoxLike/KittleKogler.lean](BoxLike/KittleKogler.lean)). It is
derived from the Lean formalisation of the source by its authors,
[ckkogler/exact-overlaps-one-dim-lean](https://github.com/ckkogler/exact-overlaps-one-dim-lean),
whose library `ExactOverlaps` this repository carries verbatim in [vendor/](vendor/README.md), at
a commit on the same Mathlib commit: its `theorem_1_1` gives the lower Hausdorff dimension with
the random walk entropy rate, its `hasExactDimension_lowerHausdorffDimension` the
exact-dimensionality with closed balls, and its `randomWalkEntropyRate_eq_of_noExactOverlaps` the
Shannon entropy of the weights without exact overlaps. The library statements take
`KittleKoglerDimension` as a hypothesis and Solution discharges it; `Challenge.lean` does not
import it.

Jordan–Rapaport's Theorem 1.1, `JordanRapaportDimension`, the dimension `min{1, h/|χ|}` of the
projection of an ergodic measure under the projective exponential separation condition, is
`jordanRapaportDimension_of_shmerkin` ([BoxLike/JordanRapaport.lean](BoxLike/JordanRapaport.lean)),
proved along Section 2 of the source from Shmerkin's theorem on the `L^q` dimension of self-similar
measures with exponential separation (Ann. of Math. (2) 189 (2019), Theorem 6.6), the statement
`ShmerkinLqDimension` of [BoxLike/Literature.lean](BoxLike/Literature.lean), taken as its lower
bound. The library statements take `JordanRapaportDimension` as a hypothesis, and Solution
discharges it from `ShmerkinLqDimension`.

Shmerkin's theorem itself is `shmerkinLqDimension_holds` ([BoxLike/Shmerkin.lean](BoxLike/Shmerkin.lean)),
proved along the source in [BoxLike/Shmerkin/](BoxLike/Shmerkin/): the `L^q` spectrum and the
reduction of Section 6.4, Theorem 5.1 from the inverse theorem for `L^q` norms of convolutions
(Theorem 2.1), and Theorem 2.1 along Section 3 from the asymmetric Balog–Szemerédi–Gowers theorem
(`Shmerkin.theorem32`, after B. Green's notes, from Plünnecke–Ruzsa) and Bourgain's structure
theorem in the weak form `Shmerkin.Bourgain.theorem31Weak`, with some positive doubling exponent in
place of the source's `2^{-2T-1}`, proved from Hochman's saturation theorem of the vendored
`ExactOverlaps` along Shmerkin, arXiv:2308.09846, Theorem 1.5. The weak form suffices, because the
exponent of Theorem 3.2 is chosen after the block length. `Challenge.lean` states no cited theorem.

The library also proves the Shannon–McMillan–Breiman theorem, the Kolmogorov–Sinai generator
theorem, Kingman's subadditive ergodic theorem, the Furstenberg–Kesten limits, Oseledets' theorem
for invertible planar cocycles, Bowen's theorem that every Hölder potential on the mixing
sub-shift `Σ_Z` has exactly one ergodic Gibbs measure, and Proposition 3.10 for box-like tuples
with rotations, which the manuscript cites. Off the main line it proves Fraser's Theorem 2.3
along his Section 5 ([BoxLike/Fraser/](BoxLike/Fraser/)), with one deviation in his Lemma 5.1 (2)
recorded in [docs/correspondence.md](docs/correspondence.md); Feng–Käenmäki's Proposition 1.2
for irreducible planar tuples, through the quasi-multiplicativity of the norm, Bowen's
construction of an ergodic Gibbs measure of `‖·‖^q` and a relative-entropy argument for
uniqueness ([BoxLike/QuasiMultiplicative/](BoxLike/QuasiMultiplicative/)); and Rossi's bound by a
covering argument ([BoxLike/Rossi.lean](BoxLike/Rossi.lean),
[BoxLike/RossiBound.lean](BoxLike/RossiBound.lean)). These statements keep their `Prop`-valued
definitions; the results that use them take them as hypotheses, and Solution passes the proofs.

No literature axiom is declared. Each cited result is a named `Prop` definition taken as an
explicit hypothesis by every result that uses it. The library and Solution are `sorry`-free,
and the comparator permits only `propext`, `Classical.choice` and `Quot.sound`.

## Remaining work

- **Question 1.4** (`q:coincident-projection-dimensions`) is open. It is recorded as the
  proposition `BoxLike.CoincidentProjectionDimensionsQuestion` in
  [BoxLike/OpenQuestion.lean](BoxLike/OpenQuestion.lean); no answer is claimed.
- **The citation of Bárány–Käenmäki in Proposition 2.7.** The paper cites Theorem 2.1 of the
  source as stated, which is false; its proof gives what the paper uses, and the library proves
  it. The citation in the tex file should refer to the proof or to the corrected statement.
- **Bourgain's structure theorem.** Shmerkin's Theorem 3.1 is proved only in the weak form
  `Shmerkin.Bourgain.theorem31Weak`; the form stated by the source has no proof and nothing
  depends on it.

## Build and checks

Lean and Mathlib are pinned to `v4.35.0-rc2`, and Mathlib is the only Lake dependency. The
Kittle–Kogler library `ExactOverlaps` is a verbatim copy, under its own licence, of commit
`99c43ad` of its repository, which pins the same Mathlib commit;
[vendor/README.md](vendor/README.md) records its origin, and `lakefile.toml` builds it with the
Lean options of its own lakefile. This workstation shares `.lake/packages` with other projects: do
not run `lake update` or change that shared dependency tree. On an independent fresh checkout,
obtain the pinned Mathlib with `lake exe cache get`; the modules of `ExactOverlaps` that the
library imports build from source in a few minutes, and `lake build ExactOverlaps` builds all 592
of them.

```bash
lake build BoxLike Challenge Solution
python3 -B scripts/check_module_headers.py
python3 -B scripts/check_challenge_vocabulary.py
lake env lean tools/AuditAxioms.lean
python3 -B scripts/check_solution_entries.py
python3 -B scripts/check_paper_correspondence.py --allow-incomplete
./comparator-audit.sh --local-unsandboxed
```

Results on the current tree:

- The build passes. Its only warnings are the three intentional `sorry` holes of
  `Challenge.lean`.
- The module headers (235 sources and 593 vendored sources), the Challenge vocabulary (42
  definitions, all occurring in the types of the headline statements), the Solution entries and the
  correspondence metadata pass; `git diff --check` is clean. The manifest records the reviewed
  manuscript commit `2e45bb0`, and the fingerprints of all numbered statements and prose spans
  match.
- The axiom audit passes for 6,381 completed constants and 3,463 constants of the vendored
  library, which depend on `propext`, `Classical.choice` and `Quot.sound` only.
- The comparator accepts all three headlines `Challenge.audit_main1`, `Challenge.audit_main2`
  and `Challenge.audit_main_extended`: con-ron checks 68,058 declarations, and nanoda and the
  Lean kernel accept. This is a local macOS run without the Linux sandbox, not a Palomar
  verdict; on Linux omit `--local-unsandboxed` to use the sandboxed external-kernel audit.

The strict completeness checks

```bash
python3 -B scripts/check_solution_entries.py --require-complete
python3 -B scripts/check_paper_correspondence.py
```

pass, since no entry is partially formalised. No LaTeX compilation is performed by these checks.

## Further documentation

[formalization.yaml](formalization.yaml) records provenance and the status of the three
headlines.

## Attribution and licence

Developed by Sascha Troscheit with AI assistance recorded in
[formalization.yaml](formalization.yaml). Sources use [Apache License 2.0](LICENSE);
see [CITATION.cff](CITATION.cff).
