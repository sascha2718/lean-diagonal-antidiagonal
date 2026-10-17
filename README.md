# Hausdorff dimension of planar box-like self-affine sets with rotations

Lean 4 formalisation accompanying the manuscript by Demi Allen, Antti Käenmäki,
R. Dániel Prokaj, Károly Simon and Sascha Troscheit.

## Coverage

All 41 numbered statements have an entry in [Solution.lean](Solution.lean), with explicit
literature dependencies, scope gaps and deviations from the prose proof. The assessment is
36 formalised, 2 cited (Theorem 1.1 of Fraser and Proposition 3.14 of Fraser–Jordan–Jurga),
2 partially formalised (Proposition 3.10 and Theorem 4.2) and 1 open question (Question 1.4).
[paper-correspondence.yaml](paper-correspondence.yaml) fingerprints the 41 numbered statements
and 45 prose spans; over all 86 items its manifest reads 78 formalised, 4 cited, 3 partially
formalised and 1 intentionally unformalised, with 13 literature hypotheses. A valid fingerprint
or an entry in Solution is not by itself evidence of mathematical equivalence.

**The complete manuscript is not formalised.** Two numbered results and one prose span rest on
premises that await the project owner's authorisation, and Question 1.4 is open.

[docs/correspondence.md](docs/correspondence.md) is the human-readable review;
[docs/review.json](docs/review.json) contains every entry with its exact source hypotheses.

## Headline results

[Challenge.lean](Challenge.lean) states the three headline theorems over Mathlib alone, with
their cited hypotheses and the 78 definitions their statements need. Solution proves all three
for the full parameter range of the manuscript.

| Endpoint | Manuscript | Solution | Literature inputs |
|---|---|---|---|
| `Challenge.audit_main1` | Theorem 1.2 | proved | `MorrisShmerkinLyapunov`, `FengKaenmakiGibbs`, `FraserJordanJurgaDecomposition`, `JordanRapaportDimension` |
| `Challenge.audit_main2` | Theorem 1.3 | proved | `MorrisShmerkinLyapunov`, `FengKaenmakiGibbs`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`, `KittleKoglerDimension` |
| `Challenge.audit_main_extended` | Theorem 4.16 | proved | `MorrisShmerkinLyapunov`, `FengKaenmakiGibbs`, `FraserJordanJurgaDecomposition`, `JordanRapaportDimension`, `FengLedrappierYoung`, `FengLedrappierYoungBar` |

Feng's information-sum identity, `FengInfoSum` and `FengInfoSumBar`, is a theorem of the library
(`fengInfoSum_holds`, `fengInfoSumBar_holds`) and is not a hypothesis of any headline result.
The library also proves the Shannon–McMillan–Breiman theorem, the Kolmogorov–Sinai generator
theorem, Kingman's subadditive ergodic theorem, the Furstenberg–Kesten limits and Oseledets'
theorem for invertible planar cocycles, which the manuscript cites.

No literature axiom is declared. Each cited result is a named `Prop` definition taken as an
explicit hypothesis by every result that uses it. The library and Solution are `sorry`-free,
and the comparator permits only `propext`, `Classical.choice` and `Quot.sound`.

## Remaining work

- **Proposition 3.10** (`thm:irred_eq_state`) is proved for irreducible box-like systems. For
  arbitrary irreducible tuples in `GL_2(ℝ)^N` it needs the proposed premise
  `FengKaenmakiNormEquilibrium`, a transcription of Feng–Käenmäki, Proposition 1.2, in
  [BoxLike/Proposals/EFengKaenmakiTuple.lean](BoxLike/Proposals/EFengKaenmakiTuple.lean).
- **Theorem 4.2** (`thm:feng1`): the scalar clause is the authorised `FengLedrappierYoungBar` and
  the planar clause the authorised box-like `FengLedrappierYoung`. The planar clause for every
  planar self-affine set needs the proposed premise `PlanarFengLedrappierYoung` in
  [BoxLike/Proposals/CPlanarFeng.lean](BoxLike/Proposals/CPlanarFeng.lean).
- **The prose span "Existence and uniqueness of ergodic Gibbs measures on the mixing
  sub-shift"**: uniqueness is proved; existence for a general Hölder potential needs the
  proposed premise `BowenGibbsExistence` in
  [BoxLike/Proposals/IBowenGibbs.lean](BoxLike/Proposals/IBowenGibbs.lean). Its Bowen theorem
  number is quoted from memory and must be checked against the book before authorisation.
- **Question 1.4** (`q:coincident-projection-dimensions`) is open. It is recorded as the
  proposition `BoxLike.CoincidentProjectionDimensionsQuestion` in
  [BoxLike/OpenQuestion.lean](BoxLike/OpenQuestion.lean); no answer is claimed.

Three further proposals are not needed. The conclusion of `PlanarOseledets` is a theorem
(`MatrixTuple.measure_regularSet_compl_of_ergodic`), `PlanarFengInfoSum` follows from proved
results (`PlanarSystem.infoSum_xi` and the planar Oseledets theorem), and
`FengLedrappierYoungBarScalar` is unused by the certified proof of Theorem 1.3. Nothing outside
`BoxLike/Proposals/` imports a proposal.

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
- The module headers, the Challenge vocabulary (78 definitions, all occurring in the types of
  the headline statements or their hypotheses), the Solution entries and the correspondence
  metadata pass; `git diff --check` is clean.
- The axiom audit passes for 4,973 completed constants, which depend on `propext`,
  `Classical.choice` and `Quot.sound` only.
- The comparator accepts all three headlines `Challenge.audit_main1`, `Challenge.audit_main2`
  and `Challenge.audit_main_extended`: con-ron checks 53,880 declarations, and nanoda and the
  Lean kernel accept. This is a local macOS run without the Linux sandbox, not a Palomar
  verdict; on Linux omit `--local-unsandboxed` to use the sandboxed external-kernel audit.

The strict completeness checks

```bash
python3 -B scripts/check_solution_entries.py --require-complete
python3 -B scripts/check_paper_correspondence.py
```

fail on exactly the two partially formalised entries 3.10 and 4.2, as they must while the
premises above are unauthorised. No LaTeX compilation is performed by these checks.

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
