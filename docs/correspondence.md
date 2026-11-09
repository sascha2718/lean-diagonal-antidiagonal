# Correspondence with the paper

The paper is available as [arXiv:2611.09066v1](https://arxiv.org/abs/2611.09066v1),
submitted on 6 November 2026. The checks below use the local `diagonal-antidiagonal.tex`
at manuscript revision `ea69be97835c7061f7c06adc1545bffebd821aa1`; its full source fingerprint
and all 44 numbered-statement fingerprints match the recorded correspondence.

[Solution.lean](../Solution.lean) records all 44 numbered statements in manuscript order.
It proves 42 of them. Hochman–Rapaport's
theorem (1.1) is stated without proof and is unused; Question 1.4 remains open.
[paper-correspondence.yaml](../paper-correspondence.yaml) gives the statement mapping,
reviewed source revision and fingerprints. The whole-file fingerprint also detects
changes to proofs and unnumbered text.

The three headline results are stated independently over Mathlib in
[Challenge.lean](../Challenge.lean) and proved in Solution for their full parameter ranges:

| Paper | Endpoint |
| --- | --- |
| Theorem A | `Challenge.audit_main1` |
| Theorem B, including its furthermore clause | `Challenge.audit_main2` |
| Theorem 4.16 | `Challenge.audit_main_extended` |

All literature inputs to these proofs are proved in the development. The only axioms are
the standard `propext`, `Classical.choice`
and `Quot.sound`. Build and audit commands are in the [README](../README.md).

## Scope and formulation

Lean represents the alphabet by a finite type, orientations by `ZMod 2`, and the plane
by `ℝ × ℝ` with the supremum norm and closed balls. The headline results apply to every
invariant equilibrium state. Theorem A includes positivity of both pointwise-dimension
level sets; Theorem 4.16 requires projective exponential separation only below affinity
dimension two.

The recorded Hochman–Rapaport statement makes the paper's standing assumption of no
common fixed point explicit. It uses affine-coefficient distance, exponential separation
along infinitely many levels, and the proximal, strongly irreducible formulation.

The unnumbered dimension-drop argument in `sec:dimension-drop`, Fraser's numerical
projection dimension `0.891`, and the open-questions discussion are not formalised.
They are not used by the headline proofs.

## Proof differences

| Result | Formal proof |
| --- | --- |
| Theorem B | Ergodic returns give a subsequence of typical words; the scalar Ledrappier–Young formula follows from a planar embedding. |
| Rapaport (1.2) | The planar case uses Kittle–Kogler's quantitative central limit theorem in place of Berry–Esseen; deficient projections use Feng's formula and Kittle–Kogler. |
| Fraser (1.3) | A block sum replaces the stopping set in the super-multiplicative argument. |
| Proposition 2.7 | The version with a constant `C_0` is proved by Baire category. The literal cited statement without that constant has a formal counterexample and is unused. |
| Proposition 3.14 | Gibbs existence and uniqueness use Bowen's theorem in place of Sarig's. |
| Feng (4.2) | The planar theorem is proved directly; the projective formula follows through an auxiliary planar system. |
| Shmerkin, Theorem 6.6 | The required lower bound uses a weaker Bourgain structure theorem, with an unspecified positive doubling exponent. The source's stronger structure theorem is not proved. |

Further proof details are in the module documentation; the [README](../README.md#literature-results)
lists the cited results and their modules. 
