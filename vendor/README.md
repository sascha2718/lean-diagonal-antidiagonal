# The library ExactOverlaps

A verbatim copy of the Lean library `ExactOverlaps`, the formalisation of S. Kittle and C. Kogler,
*The exact overlaps conjecture for self-similar measures on the real line* (arXiv:2610.10511), by
its authors.

- Source: https://github.com/ckkogler/exact-overlaps-one-dim-lean
- Commit: `99c43adec5c5127ff9a65663641fe51f57c8f7d3` (10 October 2026)
- Copied without change: `ExactOverlaps.lean` and `ExactOverlaps/` (592 modules), `LICENSE` (the
  BSD Zero Clause License of Constantin Kogler) and `LpSelfSimilar-LICENSE`, the notice of the
  adapted LpSelfSimilar code that the source retains in its `provenance/` directory.
- Not copied: the source's `Challenge.lean`, `Solution.lean` and `Verification.lean`, its
  documentation, metadata and scripts. Its libraries `Solution` and `Challenge` share their names
  with the comparator modules of this project.
- Toolchain: the source pins `leanprover/lean4:v4.35.0-rc2` and Mathlib commit
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, the pins of this project.

`lakefile.toml` builds the copy as the Lake library `ExactOverlaps` with `srcDir = "vendor"` and
the Lean options of the source's lakefile (`relaxedAutoImplicit = false`,
`maxSynthPendingDepth = 3`). `BoxLike/KittleKogler.lean` imports three of its modules and derives
`BoxLike.KittleKoglerDimension` from `ExactOverlaps.SelfSimilar.System.theorem_1_1`,
`hasExactDimension_lowerHausdorffDimension` and `randomWalkEntropyRate_eq_of_noExactOverlaps`.
The axiom audit `tools/AuditAxioms.lean` covers every constant of the library in the environment
of `Solution`.

Edit nothing in this directory. To compare the copy with the source, or to move it to another
commit, check out the source and diff:

```sh
git clone https://github.com/ckkogler/exact-overlaps-one-dim-lean /tmp/exact-overlaps
git -C /tmp/exact-overlaps checkout --detach 99c43adec5c5127ff9a65663641fe51f57c8f7d3
diff -r /tmp/exact-overlaps/ExactOverlaps vendor/ExactOverlaps
diff /tmp/exact-overlaps/ExactOverlaps.lean vendor/ExactOverlaps.lean
```

The files begin with the copyright notice of the source before `module`, which the Palomar
source policy permits (a plain block comment may precede `module`); `scripts/check_module_headers.py`
accepts that notice for the files of this directory and applies its other checks to them unchanged.
The copy is tracked in git, so a Palomar upload of this repository carries it.
