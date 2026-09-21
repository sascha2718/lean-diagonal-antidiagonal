# Rules for worker agents

The project is the Lean 4 formalisation of the article `../diagonal-antidiagonal.tex`
("Hausdorff dimension of planar box-like self-affine sets with rotations"). Lean `v4.32.2`,
Mathlib `v4.32.2`. Work in `/Users/sascha/Documents/ActiveResearch/DA-AK-ST/lean`.

Read first: `PLAN.md` sections 0, 1, 6 and 8, `README.md`, and one existing module for the house
style (for example `BoxLike/AffinityDim.lean`). Read the modules you build on before you state
anything about their objects.

## Hard rules

* Never run `lake update`. Never edit `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` or
  anything under `.lake`.
* No `native_decide`. No `sorry` in a finished library file. No `axiom` declarations: if a cited
  theorem of the literature is needed, make it an explicit hypothesis of your theorems (a `Prop`
  or a `def … : Prop`), and report the exact statement and its source. The project owner decides
  about axioms.
* Create only the files named in your task. Do not edit existing modules, `BoxLike.lean`,
  `BoxLike/AxCheck.lean`, `PLAN.md` or `README.md`. If an existing lemma is missing, prove it in
  your file and report it.
* Other agents work in this directory at the same time. Do not build, edit or delete their files.
* Check your file with `lake env lean BoxLike/<File>.lean`; it writes nothing. When the file is
  finished and free of errors and warnings, run `lake build BoxLike.<File>` for your own module
  only, so that later modules can import it. Never run a bare `lake build`. Never rebuild
  modules that are not yours.
* Never overwrite or move files with `cp` or `mv`: the shell aliases them to interactive mode and
  the command hangs. Use the Write and Edit tools. Put experiments in the directory
  `tools/scratch/` under a file name that starts with your module name; `lake env lean` accepts
  any path.
* Commit nothing. Do not run `git` commands that change state.

## House style

* Every module opens with a non-doc comment block `/- … -/` that names the section of the article
  and lists the key declarations with one line each.
* Every declaration has a docstring. It cites the labels of the article in backticks, such as
  `thm:main1`, or the line range of the tex file for unlabelled claims.
* Imports are specific Mathlib modules and project modules, never `import Mathlib`.
* Lines have at most 100 characters.
* Namespace `BoxLike`, and `BoxLike.System` for statements about a system `S : System ι`.
* The file compiles with zero warnings: no unused variables, no deprecated lemmas, no unused simp
  arguments; use `omit [...] in` for section instances that a declaration does not need.
* Prose in comments and docstrings: British spelling, plain declarative sentences, no em dashes,
  and no description of the text relative to an earlier draft.

## Faithfulness

* State the results as the article states them, about the defined objects of the library. If the
  article's statement is false, imprecise or needs an extra hypothesis, formalise the corrected
  statement and report the difference.
* A statement may not be weakened silently. Report every deviation from the interface you were
  given.

## Final report

* The verbatim final statements of the main declarations.
* Deviations from the requested interface, with reasons.
* Findings about the article: gaps, unused or missing hypotheses, errors, with tex line numbers.
* The output of `#print axioms` for the main theorems. It may contain only `propext`,
  `Classical.choice`, `Quot.sound` and the literature axioms of `BoxLike/Literature.lean` and
  `BoxLike/LiteratureFeng.lean`.
