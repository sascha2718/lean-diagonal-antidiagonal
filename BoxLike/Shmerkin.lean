module

/-
`ShmerkinLqDimension` of `BoxLike/Literature.lean`, the lower bound of Theorem 6.6 of P. Shmerkin,
*On Furstenberg's intersection conjecture, self-similar measures, and the `L^q` norms of
convolutions*, Ann. of Math. (2) 189 (2019), arXiv:1609.07802v3, proved along the source. The
development lives in `BoxLike/Shmerkin/`:

* `Basic`, `Section4`, `Prop413`, `Limit`, `TauTilde`, `Prop68`, `Main`: Sections 4 and 6.4. The
  `L^q` spectrum `τ(μ, q)` is a limit (Fekete), concave and non-decreasing, hence differentiable
  on a dense set; the theorem follows from Proposition 6.8 through Proposition 6.7, and
  Proposition 6.8 from the line form of Theorem 5.1 (`Flattening`).
* `Statements`: Theorems 2.1, 3.1, 3.2 and 5.1 of the source as `Prop`-valued definitions, on
  `2^{-m}`-measures of the circle in integer coordinates. `Theorem51`, `Flattening`: Theorem 5.1 on
  the circle from Theorem 2.1 and Proposition 4.13 (Section 5), along the scales `ℓ D`, and its
  line form for finitely supported measures, which reaches every large scale by coarsening.
* `BSG/`, `BSG`: Theorem 3.2, the asymmetric Balog–Szemerédi–Gowers theorem (Tao–Vu,
  *Additive combinatorics*, Theorem 2.35) on `ZMod (2^m)`, after B. Green's notes on the
  theorem, from the Plünnecke–Ruzsa inequalities and Ruzsa's triangle inequality (`theorem32`).
* `Bourgain/`: Theorem 3.1, Bourgain's structure theorem for sets of small exponential doubling,
  in the weak form `Bourgain.theorem31Weak`: the doubling exponent `2^{-2T-1}` of the source is
  some `ε(T) > 0`. It is proved along Shmerkin, arXiv:2308.09846, Theorem 1.5, in dimension one,
  from Hochman's saturation theorem as formalised in the vendored library `ExactOverlaps`
  (`Entropy.exists_repeated_convolution_component_uniformity`), Plünnecke–Ruzsa and a pruning of
  the tree. The source's form `Theorem31` is not proved; it implies the weak form
  (`Bourgain.theorem31Weak_of_theorem31`).
* `Inverse/`: Theorem 2.1 from Theorems 3.1 and 3.2 along Section 3 (Lemmas 3.3 to 3.9 and
  Corollary 3.10). The weak form of Theorem 3.1 suffices, because the exponent `κ` of Theorem 3.2
  is chosen after `D` (`inverseTheorem_of_theorem32`); `inverseTheorem_of_theorem31_theorem32`
  is the deduction from the source's form.
* `InverseTheorem`: `inverseTheorem` (Theorem 2.1) and `proposition68`.

Deviations from the source, each inside a proof or in a weaker intermediate statement: the
middle-half condition of Theorem 2.1 is the closed middle half; Lemma 3.6 loses `(2(D+1))^{-ℓ}`;
sumsets pass from `ZMod (2^m)` to `ℤ` at the cost of a factor `2`; Corollary 3.10 rescales to the
resolution `(⌊ℓ/D⌋ + 1) D²` when `ℓ D` is not a multiple of `D²`; conclusion (vi) of Theorem 2.1
holds with the same `δ` as the threshold, by collapsing a few levels (Lemma 3.7); Theorem 5.1 on
the circle is proved for measures carried by `[3/8, 5/8]`, which the normalisation supplies.

* `shmerkinLqDimension_holds`: the statement `ShmerkinLqDimension`. No literature premise is
  used.
-/
public import BoxLike.Shmerkin.Main

@[expose] public section

namespace BoxLike

universe u

/-- `ShmerkinLqDimension`, the lower bound of Shmerkin's Theorem 6.6, proved along the source
with Theorem 3.1 in the weak form `Shmerkin.Bourgain.theorem31Weak`. -/
theorem shmerkinLqDimension_holds : ShmerkinLqDimension.{u} :=
  shmerkinLqDimension_of_proposition68 fun _ _ _ _ h => Shmerkin.proposition68 h

end BoxLike
