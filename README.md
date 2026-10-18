# Hausdorff dimension of planar box-like self-affine sets with rotations

Lean 4 formalisation accompanying the manuscript by Demi Allen, Antti Käenmäki,
R. Dániel Prokaj, Károly Simon and Sascha Troscheit.

## Coverage

All 41 numbered statements have an entry in [Solution.lean](Solution.lean), with explicit
literature dependencies, scope gaps and deviations from the prose proof. The assessment is
39 formalised, 1 cited (Theorem 4.2 of Feng) and 1 open question (Question 1.4).
[paper-correspondence.yaml](paper-correspondence.yaml) fingerprints the 41 numbered statements
and 45 prose spans; over all 86 items its manifest reads 83 formalised, 2 cited and
1 intentionally unformalised, with 6 literature hypotheses. A valid fingerprint or an entry in
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

[docs/correspondence.md](docs/correspondence.md) records the coverage assessment, literature
inputs and proof deviations.

## Headline results

[Challenge.lean](Challenge.lean) states the three headline theorems over Mathlib alone, with
their cited hypotheses and the 62 definitions their statements need. Solution proves all three
for the full parameter range of the manuscript.

| Endpoint | Manuscript | Solution | Literature inputs |
|---|---|---|---|
| `Challenge.audit_main1` | Theorem 1.2 | proved | `JordanRapaportDimension` |
| `Challenge.audit_main2` | Theorem 1.3 | proved | `FengLedrappierYoung`, `KittleKoglerDimension` |
| `Challenge.audit_main_extended` | Theorem 4.16 | proved | `JordanRapaportDimension`, `FengLedrappierYoung` |

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

Feng's scalar Ledrappier–Young formula `FengLedrappierYoungBar`, which the proof of Theorem 4.16
uses, follows from the cited planar formula `FengLedrappierYoung`
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
- The module headers (202 sources), the Challenge vocabulary (62 definitions, all occurring in
  the types of the headline statements or their hypotheses), the Solution entries and the
  correspondence metadata pass; `git diff --check` is clean. The manifest records the reviewed
  manuscript commit `2e45bb0`, and the fingerprints of all numbered statements and prose spans
  match.
- The axiom audit passes for 5,351 completed constants, which depend on `propext`,
  `Classical.choice` and `Quot.sound` only.
- The comparator accepts all three headlines `Challenge.audit_main1`, `Challenge.audit_main2`
  and `Challenge.audit_main_extended`: con-ron checks 55,136 declarations, and nanoda and the
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
