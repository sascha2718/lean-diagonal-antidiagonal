# Instructions for completing the article's Lean formalisation

## Objective and scope

Fully formalise the current [manuscript](../../diagonal-antidiagonal.tex), apart from explicitly
permitted results from the literature, and make the formal proofs follow the manuscript's prose
proofs. Give every numbered statement and example an entry in [Solution.lean](../Solution.lean).
Complete the supporting definitions and unnumbered claims needed to certify the article's stated
scope. Preserve Question 1.4 as an open question: record its actual formulation, without claiming
to answer it.

**Do not edit the LaTeX. Do not compile or regenerate it.** If the prose contains an incorrect
claim, missing assumption or invalid proof step, record the precise obstruction in
[findings.md](findings.md). Do not silently weaken its Lean counterpart, assume the missing
conclusion, or rewrite the manuscript to fit the available proof.

This document is a handoff for future implementation, not a claim that the listed work is done.
The requested workers are **Claude Opus 5.5**, using the exact model identifier
`claude-opus-5-5`. Access was verified through the authenticated local Claude Code CLI. The
built-in Codex agent selector does not offer Anthropic models; use the CLI when orchestrating
these workers, verify the returned model identity, and do not silently substitute another model.
Authentication is available outside the Codex filesystem sandbox; a sandboxed login check may
incorrectly appear unauthenticated. Respect the host's execution approvals and file permissions.

## Read first and preserve the current work

Read [CLAUDE.md](../../CLAUDE.md), the user-supplied AGENTS.md agreements,
[README.md](../README.md), [correspondence.md](correspondence.md),
[review.json](review.json), [mathlib-gaps.md](mathlib-gaps.md), and
[layer-e.md](layer-e.md). Consult the section reviews for the assigned statement:
[Sections 1–2](review-sections-1-2.json), [Section 3](review-section-3.json),
and [Section 4](review-section-4.json). Follow source labels rather than old line numbers.

The `lean/` directory is a separate Git repository, ignored by the manuscript repository.
It already contains substantial modified and untracked work. Inspect and preserve that state;
never reset, clean, overwrite or omit it when preparing a worker checkout. If workers use
isolated checkouts, their starting snapshot must include the current uncommitted Lean sources.

Lean and Mathlib are pinned. `.lake/packages` is shared with other projects. Do not run
`lake update`, alter the toolchain or lake configuration, or modify the shared dependency sources.
Each new Lean module must use `module`, `public import`, and `@[expose] public section`, following
the existing modules. Document its manuscript labels and the mathematical purpose of its lemmas.

Before starting, rerun the metadata checks against the current manuscript. The review snapshot
has raw manuscript SHA-256
`7e3b4a3ffd64a77a4a6db6e4032c7224d4e9319a1a567ad4e560b3cbb1ba9bab`.
The manifest's parser-normalised fingerprints have a different purpose; do not confuse them
with this raw file hash. If the source has changed, review the affected statements before coding.

## Baseline and completion standard

The reviewed snapshot has 41 numbered entries: 28 covered by proofs under their recorded
hypotheses, 2 represented as cited results, 8 partially covered, 2 unproved results, and 1 open
question. The manifest also records 40 unnumbered spans. Existing “formalized” entries sometimes
collect component lemmas; review their assembly as well as the ten incomplete non-question
entries below.

The full Theorems 1.3 and 4.16 already compile and passed local Lean, nanoda and con-ron checks.
The full Theorem 1.2 has no Solution proof: `audit_main1_below_two` proves only its restricted
case. The strict completeness checks and the full three-endpoint comparator currently fail
intentionally. Do not remove an endpoint, weaken a statement or relax a checker to obtain a pass.

Completion requires all of the following:

- Every non-question numbered result has its complete manuscript statement represented, with
  all quantifiers, parameter ranges and conclusions. A cited result is clearly distinguished
  from a theorem proved internally.
- Every result with a prose proof has an actual assembled proof following its substantive
  steps. A list of aliases, component lemmas, or a theorem assuming the missing step is
  insufficient. Foundational helpers may use different internal implementations when the
  article's argument is still the argument used by the exported proof.
- The supporting unnumbered mathematical claims and representation changes are accounted for,
  including the broader general-planar scope where the manuscript states it.
- Literature hypotheses are exact, individually named and cited, and every use is visible.
  Ordinary assumptions and internal facts derived from the literature remain separate.
- No unproved assertion is introduced into the library or Solution. `sorry`, `admit`,
  `native_decide`, opaque assumptions disguising missing results, and additional kernel axioms
  are prohibited. Only the three intentional Challenge holes may remain.
- The complete build, strict correspondence checks, vocabulary check and the comparator for
  all three headlines pass. A semantic and proof-fidelity review is still required: these
  mechanical checks cannot establish correspondence with the manuscript by themselves.

## Literature hypotheses and Challenge boundaries

“Apart from hypotheses” means the permitted external literature results may remain explicit
`Prop` hypotheses. It does not permit assuming a result of this article or any missing internal
construction. Use [review.json](review.json) for the current exact declarations and source
citations, and read the actual cited theorem before changing its transcription.

For each source boundary record the publication/version and theorem number, every source
hypothesis, the exact Lean predicate, its specialisation, and any reduction proved in Lean.
Check product order, one-sided versus two-sided shifts, signs, normalisations, measure support,
probability, ergodicity, parameter endpoints and degenerate cases. A false `Prop` premise can
make all its consequences vacuous while still passing the kernel checker.

[CLAUDE.md](../../CLAUDE.md) and the fidelity rules in [correspondence.md](correspondence.md)
require explicit authorisation for new literature statements. If a task genuinely needs an
additional external premise, first prepare its exact declaration, source statement, scope and
downstream uses for review. Do not use a new premise before it is authorised. Continue work
that does not depend on that decision. Generalising an existing literature predicate also
requires checking whether the broader source statement is already within the authorised scope.

Keep the current explicit-hypothesis design; do not introduce Lean `axiom` declarations.
If an actual literature axiom is separately authorised, the AGENTS.md rules require it to be
conspicuously named and cited, identically declared in Challenge and Solution, and individually
whitelisted. Blanket axiom permission is never acceptable.

[Challenge.lean](../Challenge.lean) must contain exactly these three headline declarations:

| Manuscript | Challenge endpoint |
|---|---|
| Theorem 1.2, `thm:main1` | `Challenge.audit_main1` |
| Theorem 1.3, `thm:main2` | `Challenge.audit_main2` |
| Theorem 4.16, `thm:main_extended` | `Challenge.audit_main_extended` |

Their declarations retain holes. Apart from those declarations, include only the vocabulary
and precise literature hypotheses needed to state them. Import Mathlib alone. Do not import
Solution or the audited library, or insert helper proofs, conditional variants, reductions,
coverage records or audit endpoints. Keep the shared definition block identical to
[Solution/Definitions.lean](../Solution/Definitions.lean), including its active variable and
instance context. Put additional solution vocabulary in Solution or the library. Recheck that
every retained Challenge definition is needed whenever the statement vocabulary changes.

## Work allocation and integration

Use independent workers for the mathematical tasks below, with one coordinator responsible for
integration, proof review and the correspondence records. The table is a suggested allocation,
not a requirement to run all workers at once.

| Workstream | Tasks | Dependencies and coordination |
|---|---|---|
| Projection and probability | A; later relevant parts of F and H | Agree reusable finite-state Markov interfaces with the example worker |
| Oseledets and general planar systems | B, C | Agree the general system, filtration and partition interfaces before dependent work |
| Entropy and equilibrium | D, E | Coordinate general-planar types with C and the SMB interface with G |
| Prescribed-dimension example | F | Parameter and translation work is independent; reuse A's probability infrastructure where applicable |
| Proof alignment | G, H | G depends on the needed SMB/mixing results; H can start independently |
| Coordinator | I, integration and final verification | Own shared files and verify all workers' claims |

Give each worker explicit file ownership. Prefer new modules for independent tasks. The
coordinator owns `BoxLike.lean`, `Challenge.lean`, `Solution.lean`, `Solution/Definitions.lean`,
`Solution/Transport.lean`, literature-boundary changes, the comparator configuration, and shared
review/manifest files. Workers propose changes to these files rather than editing them
concurrently. Reserve any existing library module before changing it.

Each worker must return the exact completed theorem types, changed files, build commands and
results, literature dependencies, a prose-step-to-Lean-declaration map, and every remaining gap.
Do not report completion from a successful local compilation alone. The coordinator reads the
statements and proof route, builds the integrated result, then updates coverage. Keep a working
proof until its replacement has passed these checks.

## A. Complete projections for s ≥ 2 — Theorems 1.2 and 4.4

Labels: `thm:main1`, `thm:eq_state_proj_dim`.
Start with `BernoulliEquilibrium`, `EntropyFactor`, `Lyapunov`, `SigmaMeasure`, `Projection`,
`Main`, `AffinityMain`, and the existing Solution proof `audit_main1_below_two`.

Follow the new branch in the prose proof of Theorem 4.4:

1. Use Lemma 3.12 to obtain the Bernoulli equilibrium state with weights proportional to
   `|det A_i|^(s/2)`.
2. Construct the orientation lift `(τ_*μ + ω_*μ)/2`. Prove that it is a stationary mixing
   Markov measure when both matrix types have positive probability. In particular, prove
   ergodicity; invariance of this average alone is insufficient.
3. Prove that each planar word has exactly two lifts and that the lift's entropy equals
   the base entropy.
4. Use Birkhoff and the matrix/projective derivative identities to show that both planar
   Lyapunov exponents equal the scalar exponent, namely
   `(1/2) ∑ i, p_i log |det A_i|`.
5. Apply the permitted Jordan–Rapaport result and identify both coordinate marginals.
   Obtain the full projection theorem for every `s > 0`, including equality at `s = 2`.
6. Combine with the existing below-two argument to prove the unchanged full
   `Challenge.audit_main1`, including both directions of the non-exact-dimensionality
   criterion and dimension one at and above the threshold.

Do not add a Bernoulli-lift or equal-exponent hypothesis to the headline. These are internal
results to prove. Preserve the all-equilibrium-state quantification. Acceptance closes both
numbered entries and allows the full three-headline comparator to reach kernel checking.

## B. Bridge the Oseledets representation — Lemma 3.1

Label: `thm:lyapunov_exponents_via_g_system`.
Start with `SlowAxis`, `SigmaMeasure`, `DimPartitions`, `PartitionIdentities`, and `Lyapunov`.

Lean currently defines the orientation sets through growth rates and makes the displayed
four-rate lemma essentially definitional. The manuscript instead defines them through the
Oseledets filtration and uses its all-vector property (V3).

Prove the all-vector characterisation, identify the slow subspace with the appropriate axis,
and prove agreement with the manuscript's filtration and orientation sets on the required
full-measure set. Then derive the four rates by substituting the matrix/projective derivative
identity into that characterisation, as in the prose. Supply measurability, invariance and
almost-everywhere bridges wherever downstream partition definitions use them.

Distinguish Feng's admissible full-measure set, which has forward-time properties, from the
box-like past-saturated set. Prove agreement of the relevant partitions modulo null sets;
do not identify these sets pointwise without justification. Simply renaming the rate-defined
slow axis “Oseledets” does not close this task.

## C. Represent the full general-planar scope

Labels: `thm:feng_entropy_as_limit` (3.5), `thm:feng_entropy_zero` (3.7),
`thm:feng1` (4.2), and the general objects used in 3.6 and 3.10.
Start with `System`, `General`, `Classification`, `SingularValue`, `Conditional`,
`DimPartitions`, `FengEntropy`, `LiteratureFeng`, and the general-planar prose spans.

Introduce or extend a representation of the actual arbitrary planar systems in the manuscript.
Do not retain a diagonal/anti-diagonal restriction under a general-sounding name. Define the
needed projections, products, exponents, filtrations, partitions and entropies in that setting,
and prove that the existing box-like implementation is a specialisation. Use the assumptions
of each source statement: do not impose contractivity on a matrix-only theorem that allows
arbitrary invertible tuples.

For 3.5 and 4.2, transcribe the genuinely cited Feng statements at their full stated scope,
subject to the literature-boundary rules above, and prove the representation reductions.
For 3.7, prove the article's stronger pointwise equivalence, not just the source's global
vanishing criterion. Follow its proof: the invariant zero set of conditional expected
information, vanishing information along every forward iterate, the finite information-sum
identity, mass one on all future cylinders, fixed past, and intersection to a Dirac measure.
Prove the converse through the pointwise entropy limit. Preserve the scalar clause without
adding ergodicity, and the stated planar hypotheses and index ranges.

Acceptance requires both planar and scalar clauses in complete endpoints, with explicit
specialisation theorems back to the objects used by the headlines.

## D. Unconditional cylinder entropy — Lemma 3.6

Label: `thm:feng_entropy_kolmogorov_sinai`.
Start with `Entropy`, `PastEntropy`, `Birkhoff`, `FengEntropy`, and `Conditional`.

Formalise the almost-everywhere limit of **unconditional** cylinder masses and its equality
with the pointwise `h₀`. The current integrated identity `h₀(μ) = h(μ)` and the conditional
cylinder limit do not prove this statement. Preserve the general-planar scope and all
almost-everywhere qualifiers.

The manuscript explicitly invokes Shannon–McMillan–Breiman and Feng's Lemma 4.6; the review
identifies Feng (4.17) as the relevant unconditional assertion. Reuse a suitable checked theorem
if available. Otherwise prove the required finite-alphabet SMB result, or prepare the exact
cited source boundary for authorisation under the literature rules. Never disguise Lemma 3.6
itself as a new unsupported premise. If a permitted source theorem is transcribed rather than
proved, label that dependency and coverage honestly as cited.

Also prove the bridge from the library's finite-block entropy rate to the manuscript's
Kolmogorov–Sinai entropy, defined as a supremum over finite Borel partitions. Supply the actual
generator argument or an explicitly permitted exact source result. Provide an SMB interface
usable by the typical-word proof in task G.

## E. Irreducible equilibria and two-block normalisation — 3.10 and 3.11

Labels: `thm:irred_eq_state`, `thm:two-block-normalisation`.
Start with `UniqueEquilibrium`, `EquilibriumExistence`, `BernoulliEquilibrium`, `Proximal`,
`SecondIterate`, `Grouping`, `SeparationConditions`, and the literature modules.

For Proposition 3.10, assemble existence, uniqueness, ergodicity and Gibbs bounds for arbitrary
irreducible planar invertible tuples and every `s > 0`. The normalised box-like result obtained
using Fraser–Jordan–Jurga does not cover this scope. Follow the stated Feng–Käenmäki route:
the norm potential for `s ≤ 1`; the rescaled tuple
`A'_i = |det A_i|^((s-1)/(2-s)) A_i` with exponent `2-s` for `1 < s < 2`; and the determinant
Bernoulli calculation for `s ≥ 2`. Prove the rescaling and two-sided-shift reductions. Any
expansion of the cited source predicate must pass the literature review before use.

For Lemma 3.11, assemble every conclusion in one theorem or a clearly complete family with
a final wrapper: attractor equality; both matrix types; a proximal diagonal generator;
preservation of strong separation, strong open set and projective exponential separation;
the unique ergodic equilibrium state; the pressure, entropy and both Lyapunov scalings; and
equality of projected measures.

Close the elementary proximal-diagonal step: if the original tuple has such a generator, its
square supplies one in the second iterate; combine this with `hasProximalDiagonal_or_sq`.
Use Proposition 3.10 for uniqueness and ergodicity as the prose does, rather than the later
Gibbs decomposition. Retain the existing floor/subsequence argument for projective separation.
Formalise that grouping a Bernoulli measure into pairs is Bernoulli, and account for the
following affinity-dimension, Lyapunov-dimension and coordinate-projection consequences.

## F. The actual four-map example — Example 4.5

Label: `ex:projection_double_dimensional`.
The old rational two-map example is not this result. Prove the construction for **every**
`0 < s₂ < s₁ ≤ 1`, using four maps and the precise parameter family in the manuscript.
This task can be split into three workers after agreeing the common definitions.

**Parameters and pressure.** Define `H(p)` and `J(p)` as in the source. Prove continuity,
strict monotonicity and endpoint limits of `(log 2 + H(p))/(log 2 + J(p))`, hence existence
and uniqueness of the required `p ∈ (1/2,1)`. Define `a = (p/2)^(1/s₁)` and
`b = ((1-p)/2)^(1/s₁)`, prove `0 < b < a < 1/2`, construct the tuple, and verify its geometry.
Use the displayed rank-one matrix `M(u)` and the two-sided partition-sum estimate to prove
`P(A,u) = log(2a^u + 2b^u)` for `0 ≤ u ≤ 1`, then `dimaff = s₁`.

**Translations and separation.** Use the eight-dimensional translation cube with
`R = 2/(1-2a)`. Prove the invariant rectangle and gaps of at least one for all translations
in the cube. For two distinct words, use their first differing symbol to prove the lower
bound `κ b^(n-1)` on a translation coefficient, where `κ = (1-2a)/(1-a)`. Apply the
one-dimensional interval estimate and integration over the other seven coordinates. With
`C = κ/8` and `c = b/128`, prove the displayed union bound
`volume(E_n) ≤ (b/4) 2^(-n)` and select a translation outside every bad event. Derive the
all-length exponential gap and then the library's projective separation predicate, absorbing
the prefactor correctly. Do not replace this argument by an unproved generic-parameter claim.

**Markov measure and dimensions.** Construct and identify the stated Gibbs/Markov measure,
derive `Q_ij = M(s)_ij v_j/v_i` and its rows `(p,1-p)`, verify stationarity and the two
equiprobable labelled choices per transition, and compute entropy and both Lyapunov exponents.
Use Proposition 4.3 and the decomposition as in the prose. Apply Theorem 4.4 to obtain both
dimension values in both coordinate projections, each on a positive-measure set, together with
the stated upper packing and lower Hausdorff dimensions. Do not assume the entropy or exponent
formulas as inputs to the final example.

## G. Make Theorem 1.3 use its prose proof

Label: `thm:main2`.
Start with `TypicalWords`, `Subsystem`, `HomogeneousSubsystem`, `SubsystemEntropy`,
`MainTwoFree`, and `MainTwoEndpoint`. Preserve the already completed all-range endpoint while
developing its replacement proof.

- Construct the typical families using the manuscript's SMB, mixing and horizontal-orientation
  return argument. The current Gibbs/Birkhoff counting construction followed by appending an
  anti-diagonal symbol is a substantive alternative and must not remain the certified route.
- Formalise the pigeonhole loss and all length, cardinality and Lyapunov limits explicitly.
- Work with the genuinely diagonal subsystem in the prose. Remove its dependence on an added
  zero-weight anti-diagonal symbol by providing a justified scalar Feng interface for the
  actual subsystem. Do not merely weaken the existing literature predicate without source
  review and approval of any expanded external premise.
- Under the entropy threshold, derive `0 ≤ q ≤ q_y = 0` from conditional-entropy monotonicity,
  as in the manuscript. The existing Dirac-conditionals proof may remain a helper but is not
  the replacement for this step.
- In the open-set branch prove the asserted strong separation of the selected finite subsystem,
  then unique coding, rather than stopping at unique coding alone.
- Preserve the Kittle–Kogler source hypothesis, the dimension limit, the ambient upper bound,
  and the already proved `s ≥ 2` strong-open-set/determinant endpoint.

Acceptance includes a step-by-step comparison of the assembled proof with the current prose,
not just a new theorem with the same type.

## H. Align the other proofs and audit all existing entries

Use the complete deviation register in [correspondence.md](correspondence.md), including
entries currently marked proved. At minimum address these substantive differences:

| Statement | Required prose route |
|---|---|
| 2.3, `thm:box_like_proximal` | Remove conformal diagonal factors and pair anti-diagonal factors of a proximal word; replace the weighted-cocycle argument on the certified route |
| 2.7, `prop:ssc_no_overlap_not_pesc` | Select parameters by excluding the stated countable algebraic exceptional sets, then prove the multiplicative-independence, symbol-count and coefficient steps used in the prose |
| 3.13, `thm:sigma_tau_omega_positive_eq_measure` | Sum the counting inequality and apply Birkhoff as written, rather than using only its integrated one-step version |
| 4.7, `thm:conditional_two_ways` | Normalise on the positive pieces, transport the conditional measures, then remove restrictions using 3.2 |
| Unnumbered measure-dimension identities | Compare the set-based infimum/supremum argument in the text with the current differentiation/essential-bound proof and supply the required bridges or prose-route proof |

Retain useful alternative proofs as internal lemmas if desired, but make the numbered endpoint
use the aligned argument. A helper name or comment saying “as in the prose” is not evidence of
alignment; inspect its dependency tree and mathematical steps.

Distinguish substantive alternatives from extra foundational detail. The prose omits proofs
for some facts and cites sources for others; direct internal proofs of those facts need not be
deleted. Algebraic factoring, zero-based indexing and proved equivalent representations are
acceptable when explained. If the prose invokes a theorem redundantly, record that fact rather
than adding an unnecessary external premise merely to match the citation list. Preserve the
existing repairs to 4.3, 4.9 and 4.14 and the source-faithful prime Bárány–Käenmäki endpoint.

## I. Supporting claims, Solution entries and final integration

Review all 40 unnumbered spans in [paper-correspondence.yaml](../paper-correspondence.yaml).
The known gaps include:

- General-planar upper dimension bounds, Lyapunov exponents, pressure, energy, variational
  statements and equilibrium existence; also the asserted pressure convexity.
- The one-sided canonical projection and equality of its push-forward with that of the
  natural extension, at the manuscript's stated scope.
- Topological mixing of `Σ_Z`, not just positivity of a two-step transition matrix.
- Metric doubling of Gibbs measures, not just a cylinder comparison.
- Pressure, existence and uniqueness of Gibbs measures for the stated Hölder potentials,
  rather than only the two one-symbol potentials used by the main proofs.
- The stated countable-partition/conditioning-sigma-algebra generality of information and
  entropy, beyond the current canonical finite-partition specialisation.
- The general Oseledets partitions, the Kolmogorov–Sinai generator bridge, SMB, and the
  Bernoulli grouping claim covered by the tasks above.

The existing manifest is the minimum inventory. During the source pass, add any mathematical
claim required for “the full article” that is not covered by those spans. Check the review's
reported issues against the actual source, including the introductory classification wording
and the all-anti-diagonal case. A false prose claim must remain visibly flagged, with a
counterexample or precise obstruction where available.

Maintain exactly one `-- PAPER_ENTRY <label>` in Solution for each numbered item. Each entry
must identify its complete assembled theorem or an explicit complete family, exact literature
inputs and citations, ordinary assumptions, internal prerequisites, parameter ranges and proof
alignment. If a helper takes `GibbsDecomposition`, an Oseledets structure or another internal
object as input, the entry must also show how that object is obtained from the manuscript's
actual hypotheses. An endpoint assuming the desired construction is not a solution.

The coordinator updates `paper-correspondence.yaml`, `docs/correspondence.md`, `docs/review.json`,
the relevant section review, `docs/findings.md`, `README.md` and `formalization.yaml` when work
lands. Keep these as records of current state. Remove stale gaps only after the complete result
has been checked; retain unresolved deviations explicitly. Do not change fingerprints simply
to hide a source mismatch. Record model assistance accurately in the existing provenance scheme.

## Verification and handoff

Run targeted Lean builds while implementing. From `lean/`, run the following for integration:

```bash
lake build BoxLike Challenge Solution
python3 -B scripts/check_module_headers.py
python3 -B scripts/check_solution_entries.py --require-complete
python3 -B scripts/check_paper_correspondence.py
python3 -B scripts/check_challenge_vocabulary.py
lake env lean tools/AuditAxioms.lean
./comparator-audit.sh --local-unsandboxed
git diff --check
```

On a supported Linux environment, omit `--local-unsandboxed` to run the sandboxed comparator.
The macOS command is a local development check, not Palomar acceptance. Keep all three headline
names in the comparator and only `propext`, `Classical.choice`, and `Quot.sound` on its permitted
axiom list. A two-endpoint subset pass is not completion. The internal axiom audit must cover
new non-headline declarations as well as the headlines; ensure its namespace selection includes
any new general-planar namespace.

`--allow-incomplete` is useful for intermediate metadata checks only. It is not a completion
check. Likewise, the strict numbered-entry checker currently does not by itself certify every
unnumbered span or substantive proof alignment; review those separately and extend internal
audit tooling if useful. Do not put that tooling in Challenge.

At handoff, report the three headline endpoints, the status of all numbered items and supporting
spans, all remaining prose deviations or manuscript obstructions, precise literature
dependencies, and the actual verification results. Confirm that the LaTeX hash is unchanged.
If any required proof, scope bridge, source review or prose alignment remains outstanding,
state that the full formalisation is incomplete.
