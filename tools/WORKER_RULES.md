# Common rules for the formalisation workers

You are one of about ten concurrent worker agents completing the Lean 4 formalisation `BoxLike`
of the manuscript `/Users/sascha/Documents/ActiveResearch/DA-AK-ST/diagonal-antidiagonal.tex`.
A coordinator integrates your work. Work in `/Users/sascha/Documents/ActiveResearch/DA-AK-ST/lean`.

## Read first

1. `docs/formalisation-tasks.md`: the whole file, and your task section in detail. It is the
   specification. Its acceptance criteria apply to you.
2. `tools/AGENT_RULES.md`, `README.md`, `NOTES.local.md` (build set-up, technique notes).
3. `docs/correspondence.md` (fidelity boundary, deviation register, your entries),
   `docs/mathlib-gaps.md`, `docs/layer-e.md` when you touch entropy, and the section review
   JSON for your labels (`docs/review-sections-1-2.json`, `docs/review-section-3.json`,
   `docs/review-section-4.json`, `docs/review.json`).
4. The manuscript statements and proofs of your labels; find them by `\label{...}` in the tex
   file. Never edit, compile or regenerate the LaTeX.
5. The modules you build on, before you state anything about their objects. Reuse existing
   lemmas; search with `grep -rn` over `BoxLike/` and the Mathlib sources under
   `.lake/packages/mathlib/Mathlib/`.

## Shared interfaces fixed by the coordinator (built; do not edit)

* `BoxLike/MatrixTuple.lean`: general tuples `A : ι → Matrix (Fin 2) (Fin 2) ℝ` (invertible
  means `∀ i, (A i).det ≠ 0`, as in `BoxLike/Classification.lean`) with `MatrixTuple.word`,
  `svfSum`, `pressure`, `lyapunov₁`, `lyapunov₂`, `energyLim`, `IsEquilibriumState`,
  `HasGibbsBounds`, and the definitional specialisations `System.pressure_eq_tuple` and so on
  for `A = S.mat`.
* `BoxLike/SMBStatement.lean`: `ShannonMcMillanBreimanStatement.{u} : Prop`, the
  Shannon–McMillan–Breiman theorem for ergodic measures on `ℤ → α`, `α` finite. Worker D
  proves it; other workers may take it as a hypothesis of development lemmas only.
* `BoxLike/PrescribedExample/Defs.lean`: `H`, `J`, `ratio`, `aOf`, `bOf`, `Params`, `paramsOf`,
  `orient`, `sys` for Example 4.5.

If an interface is wrong or insufficient, do not edit it: add what you need in your own file
and report the proposed change.

## Concurrency

* Create and edit only the files your brief assigns to you. Do not edit any existing module,
  `BoxLike.lean`, `Challenge.lean`, `Solution.lean`, `Solution/`, `docs/`,
  `paper-correspondence.yaml`, `README.md`, `formalization.yaml`, `comparator-config.json`,
  `comparator-audit.sh` or `scripts/`. If an existing lemma must change, prove the variant in
  your own file and report the proposed change.
* Import only existing modules, the three interface modules, and the modules of other workers
  that your brief names.
* Check a file with `lake env lean <file>`; it writes nothing. Once a module compiles without
  errors, build it with `lake build BoxLike.<Its.Name>` so that your later modules can import
  it. Build only your own modules. Never run a bare `lake build`, `lake build BoxLike`,
  `lake update`, `lake clean` or `lake exe cache`. Never touch `.lake`, `lean-toolchain`,
  `lakefile.toml` or `lake-manifest.json`.
* Run at most one Lean process at a time: ten workers share 24 GB of memory.
* Write files with the Write and Edit tools; never `cp` or `mv` over files (they are aliased to
  interactive mode). Put experiments in `tools/scratch/<your prefix>_*.lean`.
* Run no git command that changes state. Commit nothing. Do not spawn further agents.

## Library rules

* No `sorry`, `admit`, `native_decide` or `axiom` in a finished file. Only `propext`,
  `Classical.choice` and `Quot.sound` may appear in `#print axioms`.
* Literature boundary. The existing cited results are `Prop` definitions in
  `BoxLike/Literature*.lean`, taken as explicit hypotheses. Do not add a new one, and do not
  broaden an existing one, in a result you present as complete. If a task genuinely needs a new
  or broadened external premise, prepare it for the project owner's review: put its exact
  `def … : Prop` in `BoxLike/Proposals/<YourPrefix><Name>.lean`, with the publication, version,
  theorem number, every source hypothesis, the specialisation and its degenerate-instance test
  in the docstring. Results that use it may live in the same proposals file, clearly marked as
  conditional on an unauthorised premise. Nothing outside `BoxLike/Proposals/` may import it.
  Results of the paper itself never become hypotheses.
* Internal results proved by another worker may be taken as hypotheses only through the
  interfaces above; report every such conditional result as conditional.
* House style: `module`, `public import`, `@[expose] public section`; a `/- … -/` header naming
  the section of the article and listing the key declarations; a docstring on every
  declaration citing its tex label; specific imports, never `import Mathlib`; lines of at most
  100 characters; zero warnings; namespace `BoxLike` (and `BoxLike.System` for statements about
  `S : System ι`); British spelling, plain declarative prose, no em dashes, no description of
  the text relative to an earlier draft.
* Faithfulness. State the manuscript's result with all quantifiers, parameter ranges and
  conclusions, about the defined objects of the library. Do not weaken a statement, assume a
  missing conclusion, or replace the prose proof by a different route when the task requires
  the prose route. If the manuscript is wrong or incomplete, formalise the corrected statement
  and report the precise obstruction as a finding with tex line numbers.

## Working style

This is a long task. Work persistently until your task is complete or you are genuinely
blocked. Checked partial progress is valuable; a fully proved sub-result is worth more than
several sketches. Keep each finished module compiling and built. If you run low on context,
finish and build the current module before continuing.

## Final report (your last message)

1. Your exact model identifier.
2. Files created, each with its final `lake env lean` and `lake build` result.
3. The verbatim types of the main theorems, and `#print axioms` for each (run it in a scratch
   file).
4. Literature dependencies, by predicate name.
5. A map from each step of the prose proof to the Lean declaration that carries it.
6. Proposed changes to coordinator-owned files, such as the exact `Solution.lean` entry or proof
   text, and any proposed interface change.
7. Proposals for new or broadened literature premises, if any, with their files.
8. Findings about the manuscript, with tex line numbers.
9. Every remaining gap, stated plainly. Do not report completion from a successful compilation
   alone.
