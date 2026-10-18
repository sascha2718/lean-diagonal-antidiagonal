# Hausdorff dimension of planar box-like self-affine sets with rotations

Lean 4 formalisation accompanying the manuscript by Demi Allen, Antti Käenmäki,
R. Dániel Prokaj, Károly Simon and Sascha Troscheit.

## Coverage

All 41 numbered statements have an entry in [Solution.lean](Solution.lean), with explicit
literature dependencies, scope gaps and deviations from the prose proof. The assessment is
38 formalised, 2 cited (Theorem 1.1 of Fraser and Theorem 4.2 of Feng) and 1 open question
(Question 1.4).
[paper-correspondence.yaml](paper-correspondence.yaml) fingerprints the 41 numbered statements
and 45 prose spans; over all 86 items its manifest reads 81 formalised, 4 cited and
1 intentionally unformalised, with 14 literature hypotheses. A valid fingerprint or an entry in
Solution is not by itself evidence of mathematical equivalence.

**Every numbered statement is formalised or cited, except Question 1.4, which is open.** No
result rests on an unauthorised premise. Proposition 3.10 is proved for every irreducible tuple
in `GL_2(ℝ)^N` from the authorised premise `FengKaenmakiNormEquilibrium` (Feng–Käenmäki,
Proposition 1.2), and Theorem 4.2 is stated for every planar self-affine set from the authorised
premise `PlanarFengLedrappierYoung` (Feng, Theorems 1.2 and 1.3); no headline takes either.
Proposition 3.14 (Fraser–Jordan–Jurga) is proved with no literature premise beyond
`FengKaenmakiGibbs`, which passes from the equilibrium state of the manuscript to its Gibbs
bounds.

[docs/correspondence.md](docs/correspondence.md) is the human-readable review;
[docs/review.json](docs/review.json) contains every entry with its exact source hypotheses.

## Headline results

[Challenge.lean](Challenge.lean) states the three headline theorems over Mathlib alone, with
their cited hypotheses and the 72 definitions their statements need. Solution proves all three
for the full parameter range of the manuscript.

| Endpoint | Manuscript | Solution | Literature inputs |
|---|---|---|---|
| `Challenge.audit_main1` | Theorem 1.2 | proved | `MorrisShmerkinLyapunov`, `FengKaenmakiGibbs`, `JordanRapaportDimension` |
| `Challenge.audit_main2` | Theorem 1.3 | proved | `MorrisShmerkinLyapunov`, `FengKaenmakiGibbs`, `FengLedrappierYoung`, `KittleKoglerDimension` |
| `Challenge.audit_main_extended` | Theorem 4.16 | proved | `MorrisShmerkinLyapunov`, `FengKaenmakiGibbs`, `JordanRapaportDimension`, `FengLedrappierYoung`, `FengLedrappierYoungBar` |

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

The library also proves the Shannon–McMillan–Breiman theorem, the Kolmogorov–Sinai generator
theorem, Kingman's subadditive ergodic theorem, the Furstenberg–Kesten limits, Oseledets' theorem
for invertible planar cocycles and Bowen's theorem that every Hölder potential on the mixing
sub-shift `Σ_Z` has exactly one ergodic Gibbs measure, which the manuscript cites.

No literature axiom is declared. Each cited result is a named `Prop` definition taken as an
explicit hypothesis by every result that uses it. The library and Solution are `sorry`-free,
and the comparator permits only `propext`, `Classical.choice` and `Quot.sound`.

## Remaining work

- **Question 1.4** (`q:coincident-projection-dimensions`) is open. It is recorded as the
  proposition `BoxLike.CoincidentProjectionDimensionsQuestion` in
  [BoxLike/OpenQuestion.lean](BoxLike/OpenQuestion.lean); no answer is claimed.

One proposal remains in `BoxLike/Proposals/`: `FengLedrappierYoungBarScalar`
([BoxLike/Proposals/GScalarFeng.lean](BoxLike/Proposals/GScalarFeng.lean)), Feng's scalar
Ledrappier–Young formula for the projective system of an arbitrary box-like system. No result
uses it: the proof of Theorem 1.3 derives the scalar formula for its diagonal subsystems from
`FengLedrappierYoung`. Nothing outside `BoxLike/Proposals/` imports it.

## Build and checks

Lean and Mathlib are pinned to `v4.35.0-rc2`. This workstation shares `.lake/packages` with
other projects: do not run `lake update` or change that shared dependency tree. On an independent
fresh checkout, obtain the pinned dependencies with `lake exe cache get`.

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
- The module headers (182 sources), the Challenge vocabulary (72 definitions, all occurring in
  the types of the headline statements or their hypotheses), the Solution entries and the
  correspondence metadata pass; `git diff --check` is clean. The manifest records the reviewed
  manuscript commit `2e45bb0`, and the fingerprints of all numbered statements and prose spans
  match.
- The axiom audit passes for 5,078 completed constants, which depend on `propext`,
  `Classical.choice` and `Quot.sound` only.
- The comparator accepts all three headlines `Challenge.audit_main1`, `Challenge.audit_main2`
  and `Challenge.audit_main_extended`: con-ron checks 54,963 declarations, and nanoda and the
  Lean kernel accept. This is a local macOS run without the Linux sandbox, not a Palomar
  verdict; on Linux omit `--local-unsandboxed` to use the sandboxed external-kernel audit.

The strict completeness checks

```bash
python3 -B scripts/check_solution_entries.py --require-complete
python3 -B scripts/check_paper_correspondence.py
```

pass, since no entry is partially formalised. No LaTeX compilation is performed by these checks.

## Further documentation

[docs/findings.md](docs/findings.md) records the findings about the manuscript;
[docs/mathlib-gaps.md](docs/mathlib-gaps.md) and [docs/layer-e.md](docs/layer-e.md) describe the
representation and the infrastructure the library builds because Mathlib lacks it.
[formalization.yaml](formalization.yaml) records provenance and the status of the three
headlines. The detailed review is split across [Sections 1–2](docs/review-sections-1-2.json),
[Section 3](docs/review-section-3.json) and [Section 4](docs/review-section-4.json).

## Attribution and licence

Developed by Sascha Troscheit with AI assistance recorded in
[formalization.yaml](formalization.yaml). Sources use [Apache License 2.0](LICENSE);
see [CITATION.cff](CITATION.cff).
