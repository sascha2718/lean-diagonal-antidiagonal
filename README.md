# Hausdorff dimension of planar box-like self-affine sets with rotations

Lean 4 formalisation of the manuscript by Demi Allen, Antti Käenmäki, R. Dániel Prokaj,
Károly Simon and Sascha Troscheit.

## Layout

- [Challenge.lean](Challenge.lean): Theorems 1.2, 1.3 and 4.16 over Mathlib alone, with the 42
  definitions their statements need and a `sorry` for each proof.
- [Solution.lean](Solution.lean), `Solution/`: the proofs, and one entry per numbered statement
  of the manuscript.
- `BoxLike/`: the library. Theorems the manuscript cites are `Prop`-valued definitions in
  `BoxLike/Literature*.lean`; the library proves every one of them.
- `vendor/`: the Kittle–Kogler library `ExactOverlaps`, verbatim; see
  [vendor/README.md](vendor/README.md).
- [paper-correspondence.yaml](paper-correspondence.yaml), [docs/correspondence.md](docs/correspondence.md):
  the correspondence with the manuscript, statement by statement.

## Status

Every numbered statement is formalised except Question 1.4, which is open. The three headline
theorems are proved for the full parameter range and take no literature hypothesis. The library
has no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

Cited results the library proves: Fraser (Theorem 1.1), Feng–Käenmäki (Proposition 3.10),
Fraser–Jordan–Jurga (Proposition 3.14), Feng's Ledrappier–Young formula (Theorem 4.2),
Morris–Shmerkin, Rossi, Feng–Hu, Jordan–Rapaport, Shmerkin's `L^q` dimension theorem
(`BoxLike/Shmerkin/`) and Kittle–Kogler (from the vendored library).

Remaining work:

- Question 1.4 is open (`BoxLike/OpenQuestion.lean`).
- The manuscript cites Theorem 2.1 of Bárány–Käenmäki as stated, which is false
  (`NoOverlap.not_baranyKaenmakiTheorem`); the library proves the form the proof of
  Proposition 2.7 uses. The citation needs a fix.
- Bourgain's structure theorem (Shmerkin's Theorem 3.1) is proved only in a weak form, which
  suffices.

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
