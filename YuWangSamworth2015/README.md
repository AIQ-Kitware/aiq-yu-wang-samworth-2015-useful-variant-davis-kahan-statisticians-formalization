# YuWangSamworth2015

A paper-facing formalization package for:

> Yi Yu, Tengyao Wang, and Richard J. Samworth, *A useful variant of the
> Davis--Kahan theorem for statisticians*, Biometrika 102 (2015), 315--323,
> arXiv:1405.0680.

## Theorem coverage

Numbering is the **published** Biometrika numbering (checked against the article
on 2026-08-13): Theorem 1, Theorem 2, Corollary 1, Theorem 3, Lemma A1.  The
2014 preprint shares one counter and calls the last three Corollary 3, Theorem 4
and Lemma 5, which is what several Lean declaration names here still spell; the
census carries the translation table.

The package represents every numbered result in the paper.  They are not all at
the same distance from the printed page, and the list below says which is which:
Theorem 2 is source-exact; Corollary 1 writes out the unit normalization the
standalone printed display omits, without which that display is false; Theorem 3
is a documented correction of a false printed convention; and Theorem 1 and
Lemma A1 are proved in forms more general than printed.

1. Theorem 1 in general unitarily invariant, Frobenius, and operator norm form —
   more general than printed, and with an intrinsic separation rather than the
   printed `δ`, whose endpoint conventions are inverted (see the census gap
   `theorem1-sample-endpoint-conventions`);
2. Theorem 2 and its aligned-frame conclusion, for **arbitrary** orthonormal
   eigenframes at a common index block — no sample eigengap, which is the whole
   point of the paper — together with the sharper residual-numerator forms its
   proof establishes;
3. Corollary 1, both displays, including the literal real sign-aligned bound,
   with `‖v‖ = ‖v̂‖ = 1` written out — the standalone printed display omits it and
   its second half is false without it, which
   `corollary1_printed_unnormalized_counterexample` refutes;
4. Theorem 3, right and left, including aligned frames, in its corrected form,
   and in the paper's own singular-value notation;
5. Lemma A1 in a basis-free compression API;
6. all three Section 2 sharpness examples, including the published middle-block
   construction.

It additionally exposes direct right and left rank-one singular-vector
corollaries, the Section 1 numerical illustration that Theorem 1's separation
can vanish, and the deterministic core of the Section 3 diagnosis of the
statistical literature.

The canonical source-facing Theorem 2 declarations are
`YuWangSamworth2015.theorem2_sinTheta` and
`YuWangSamworth2015.theorem2_alignedFrame`.  They are intentionally optimized for
semantic review: real operators on `Real^p`, source-style names, the visible
conditions `r ≤ s`, `s < p`, and `d = s - r + 1`, arbitrary supplied population
and sample eigenvector blocks, and the source's exact population denominator.  The
aligned conclusion exhibits the orthogonal matrix and compares `Vhat O` against
the supplied `V`.  `IsEigenvectorBlock` expands directly to the
orthonormal/eigenvector equations.  `SourcePopulationGap` characterizes `Delta`
as the greatest real satisfying the two population boundary inequalities --
exactly their finite minimum -- with an explicit full-space branch for the
paper's `+infinity` convention.  The audit packet expands both it and the
underlying `PopulationBoundaryGap`, so no weaker gap assumption is hidden.
The headline inequality names `sinThetaNorm` as a theorem parameter and
identifies it by a literal equality hypothesis.  The perturbation term is written
directly as `frobeniusNorm (SigmaHat - Sigma)`, where `frobeniusNorm` is a
reducible application-level abbreviation for the existing Frobenius seminorm.
Thus the text after the theorem colon mirrors the printed bound without hiding
the perturbation norm behind an extra scalar parameter.

The more general `RCLike` block wrappers remain available underneath that paper
surface, and `Symmetric/Corollary1.lean` carries the rank-one case together with
`yuWangSamworth_corollary1_scalarSample`, the witness that the sample eigenvector
is genuinely arbitrary: for `Σ = diag(1, 0)` and `Σ̂ = I/2` every unit vector of
the plane is admissible.

## Two source defects, both machine checked

The paper contains two false printed statements.  Each is refuted here, and each
has a proved repair; neither is silently corrected.

* **Equation (4)** is missing a square on `2 − ‖v̂ − v‖²`.  The corrected
  identity and a counterexample to the printed polynomial are in
  `Symmetric/AngleIdentity.lean`.
* **Theorem 3's convention `σ²_{rank(A)+1} := −∞`** makes the denominator
  infinite when `s = rank(A)`, so the printed bound asserts that the sample and
  population right singular subspaces coincide when they can be orthogonal.
  `Rectangular/RankBoundary.lean` refutes it with two rank-one orthogonal
  projections.  The repair is the ambient-dimension convention the paper's own
  proof uses, and is what the theorems here already carry.

## Architecture

This package is deliberately downstream of `ForTauCeti`.  Reusable angle,
spectral, Hilbert--Schmidt, Gram, and singular-subspace infrastructure stays in
`ForTauCeti` under the `TauCeti` namespace.  YWS-specific population-gap
bookkeeping and perturbation arguments live in `YuWangSamworth2015.Core`, while
`Symmetric`, `Rectangular`, and `Appendix` expose paper-facing results.  There is
no reverse dependency from `ForTauCeti` or `DavisKahan` into this package.

One definition extracted during this split is genuinely foundational:
`TauCeti.sinThetaFrobenius`, now in
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean`.  It is used by
non-YWS foundation code, so application-specific statistics machinery no longer
has to be imported merely to name the Frobenius sine distance.

Theorem 3 is factored through one generic Gram transport result, at both index
and frame generality.  The `FrobeniusGram` module owns the shared
finite-dimensional Hilbert--Schmidt foundation and the general two-sided ideal
theorem consumed by Lemma A1. Bundled linear-isometry wrappers expose the paper's
orthonormal-column and orthonormal-row hypotheses directly. Rank-one
singular-vector results reuse the symmetric rank-one theorem on Gram operators.
No perturbation argument is duplicated.

See `ELEGANCE_AUDIT.md` for the in-place API and factoring review.

## Sharpness

All three of the paper's sharpness constructions are formalized against the
*same* hypotheses the theorems carry, so each is a genuine instance rather than a
numerical coincidence.

`Symmetric/OrthogonalSharpness.lean` — orthogonal top-`d` eigenspaces.  Every
aligned orthonormal pair is at distance exactly `√(2d)` and `‖sin Θ‖_F = √d`,
against a bound of `√(2d)(1+ε)`: the aligned-basis constant `2^{3/2}` and the
`√d` dimension dependence are unimprovable.  This is the *preprint's*
construction.

`Symmetric/MiddleBlockSharpness.lean` — the *published* construction, a middle
block over three levels `5 > 3 > 1`, so that the population gap `min(5−3, 3−1)`
is genuinely two-sided, over the full parameter range `0 < ε < 3`.  The model
needs `2 < 2 + ε < 5` so that `2 + ε` is the *second* level of the sorted sample
spectrum; at `ε = 3` it merges with `5` and its multiplicity becomes `p − d`, so
the range is maximal whenever `2d < p` and merely sufficient in the degenerate
case `p = 2d`, where there is no leading level `5` at all.  It proves the same printed conclusion,
and it was the
harder of the two: its block sits in the middle of both spectra, so the
branch-selection hypothesis cannot be produced by any "leading `d` eigenvectors"
argument.  Closing it needed the position of an arbitrary eigenvalue level set
inside Mathlib's sorted eigenbasis — `eigenvalues_level_eq_Ico`,
`card_filter_lt_eigenvalues_basisDiagonal`, and the general
`correspondingEigenblock_eigenvalueLevel`, of which the earlier top-eigenspace
constructor is now the case `m = 0`.

`Symmetric/PlanarSharpness.lean` — two nearby lines.  Stated without
coordinates: `diag(3,1)` is `twoLevelOperator 1 3` on a line, conjugation moves
the line, and `twoLevelOperator_sub` makes the perturbation `2 (P_v̂ − P_v)`.
The sine bound is tight up to *exactly* the factor `2` at every angle, so the
constant is pinned in the small-angle regime too — which the orthogonal-blocks
example cannot do.

Building the first of them required the first-ever *constructor* for
`CorrespondingEigenblock` (`YuWangSamworth2015/Core/TopEigenblock.lean`):
that hypothesis is consumed by every theorem in the package and had no instance
anywhere in the repository, so no concrete pair of covariance operators had ever
been checked against it.

This is a root Lake library with no nested workspace, and a **default** build
target since 2026-08-02.

## Build

```bash
lake build YuWangSamworth2015.Symmetric.Theorem1
lake build YuWangSamworth2015.Symmetric.OrthogonalSharpness
lake build YuWangSamworth2015.Symmetric.MiddleBlockSharpness
lake build YuWangSamworth2015.Symmetric.MixedGap
lake build YuWangSamworth2015.Symmetric.AngleIdentity
lake build YuWangSamworth2015.Symmetric.Corollary1
lake build YuWangSamworth2015.Appendix.Lemma5
lake build YuWangSamworth2015.Rectangular.RankOne
lake build YuWangSamworth2015.Rectangular.RankBoundary
lake build YuWangSamworth2015.Rectangular.SingularBlock
lake build YuWangSamworth2015
```

Warnings are errors for this library.
