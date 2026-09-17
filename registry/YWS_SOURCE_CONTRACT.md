# Yu-Wang-Samworth 2015 - source contract for the merged Palomar entry

This file records the clause-by-clause basis for the single root
`comparator.json`. Published numbering is from Yi Yu, Tengyao Wang and Richard
J. Samworth, *A useful variant of the Davis-Kahan theorem for statisticians*,
Biometrika **102** (2015) 315-323, doi:10.1093/biomet/asv008.

The merged entry selects two related theorem families from the same paper:

| family | selected declarations | disposition |
| --- | --- | --- |
| symmetric eigenspaces | Theorem 2 (both conclusions), Corollary 1 (both displays) | Theorem 2 **source-exact**; Corollary 1 **source-faithful**, with inherited unit normalization explicit |
| general-matrix singular subspaces | Theorem 3 (right/left x sine/aligned), plus two representation equivalences | **source-corrected** because the printed rank-boundary convention is false |

Because one Comparator configuration has one source relationship, the combined
`formalization.yaml` conservatively records `relationship: adapts`. That does not
mean Theorem 2 itself is adapted.

## Common indexing

The paper orders eigenvalues and singular values decreasingly. Lean indices are
zero-based, so the paper block `1 <= r <= s` appears with one subtracted from
`r,s`; `d = s-r+1` is retained literally in the Challenge variables.

## Theorem 2 - sine conclusion

Selected declaration: `YWSPalomar.theorem2_sinTheta`.

| clause | paper | Challenge |
| --- | --- | --- |
| objects | real symmetric `Sigma, SigmaHat in R^(p x p)` | endomorphisms of `EuclideanSpace R (Fin p)`, both `IsSymmetric` |
| block | `1 <= r <= s <= p`, `d=s-r+1` | `r <= s`, `s < p`, `d = s-r+1` |
| population frame | orthonormal eigenvectors of `Sigma` at the block | `IsEigenvectorBlock Sigma ... V` |
| sample frame | arbitrary orthonormal eigenvectors of `SigmaHat` at the same indices | `IsEigenvectorBlock SigmaHat ... Vhat`; no sample-gap hypothesis |
| denominator | `Delta = min(lambda_(r-1)-lambda_r, lambda_s-lambda_(s+1))` | `SourcePopulationGap`, identifying the greatest finite boundary gap; the full-space block is an explicit infinite-boundary branch |
| numerator | `2 min(sqrt(d)||E||_op,||E||_F)` | `2 * perturbation d (SigmaHat-Sigma)` |
| conclusion | Frobenius `sin Theta` distance | `sinThetaDist V Vhat` |

Disposition: **source-exact**.

## Theorem 2 - aligned-frame conclusion

Selected declaration: `YWSPalomar.theorem2_alignedFrame`.

The hypotheses are the same as the sine conclusion. The conclusion is the
paper's `exists O in O(d)` statement comparing the rotated supplied sample frame
against the supplied population frame, with constant `2^(3/2)`. Lean writes
that constant as `2 * sqrt 2` and expands the Frobenius norm of the frame
difference as a finite sum.

Disposition: **source-exact**.

## Corollary 1

Selected declarations:

* `YWSPalomar.corollary1_sinTheta`
* `YWSPalomar.corollary1_alignedVector`

These are the rank-one `d=1` specialization of Theorem 2. The paper introduces
the corollary explicitly as the `s=r`, `d=1` case of Theorem 2, whose frame
columns are orthonormal, but the standalone printed corollary omits
`||v||=||vhat||=1` from its displayed hypotheses.

The Challenge writes those unit conditions explicitly. They are not optional:
without them the printed second display is false. Taking `SigmaHat=Sigma` and
`vhat=2v` preserves the homogeneous eigenvector equations and the printed
orientation condition while making the perturbation zero and `||vhat-v||`
nonzero. The substantive development contains a compiled counterexample.

The first selected conclusion is the sine/orthogonal-projection bound with
constant `2`; the second is the oriented vector-difference bound with constant
`2^(3/2)`.

Disposition: **source-faithful with one inherited hypothesis explicit**, not
verbatim standalone transcription.

## Theorem 3 - right and left singular subspaces

Selected declarations:

* `YWSRectangular.theorem3_rightSinTheta`
* `YWSRectangular.theorem3_rightAlignedFrame`
* `YWSRectangular.theorem3_leftSinTheta`
* `YWSRectangular.theorem3_leftAlignedFrame`

| clause | paper | Challenge |
| --- | --- | --- |
| objects | real `A, Ahat in R^(p x q)` | linear maps `Rn q -> Rn p` |
| block | `1 <= r <= s <= rank(A)` | `r <= s`, `s < finrank(range A)`, `d=s-r+1` |
| frames | right/left singular-vector blocks | `IsRightSingularBlock` / `IsLeftSingularBlock` in Gram form |
| sample gap | none | none |
| exact denominator | `min(sigma_(r-1)^2-sigma_r^2, sigma_s^2-sigma_(s+1)^2)` | `SourceSingularGap` identifies the corrected ambient-index minimum |
| numerator | `(2 sigma_1 + ||D||_op) min(sqrt(d)||D||_op,||D||_F)` | `coefficient d A (Ahat-A)` |
| sine constant | `2` | `2` |
| aligned constant | `2^(3/2)` | `2 * sqrt 2` |

### Corrected rank-boundary convention

The paper prints `sigma^2_0 := +infinity` and
`sigma^2_(rank(A)+1) := -infinity`. The second convention is false for the
claimed bound: when `s=rank(A)` it makes the denominator infinite and therefore
forces a zero upper bound, although population and sample singular subspaces can
be orthogonal. The substantive development contains the rank-one orthogonal-
projection counterexample.

The paper's own proof passes to the Gram operators. The corrected reading is
therefore at the **ambient** dimension: `A^T A` has `q` eigenvalues for right
singular vectors and `A A^T` has `p` for left singular vectors, with singular
values equal to zero past `rank(A)`. Thus a block ending exactly at the rank has
the finite lower boundary `sigma_s^2 - 0`. The Challenge implements exactly this
reading and does **not** drop the paper's independent restriction
`s <= rank(A)`.

Disposition: **source-corrected**; this is why the combined entry is `adapts`.

## Singular-frame representation equivalences

Selected declarations:

* `YWSRectangular.isRightSingularBlock_iff_pairedSingularVectors`
* `YWSRectangular.isLeftSingularBlock_iff_pairedSingularVectors`

The paper states singular blocks through paired equations
`A v_j = sigma_j u_j` and `A^T u_j = sigma_j v_j`. The Challenge theorem-family
statements use the equivalent Gram equations `A^T A v_j = sigma_j^2 v_j` and
`A A^T u_j = sigma_j^2 u_j`. At the indices selected by
`s < rank(A)`, every relevant singular value is positive, and these two compared
supporting declarations prove the equivalence in both directions. They are not
presented as numbered results of the paper.

## Not selected by Comparator

The wider repository also formalizes Theorem 1, Appendix Lemma A1, the Section 1
numerical illustration, Section 2 sharpness constructions, and source-defect
counterexamples. They are not selected by the merged root Comparator.

In particular, Theorem 1's printed endpoint conventions make its mixed
separation zero at any block touching an end of the spectrum. The Lean
formalization uses an intrinsic spectral separation rather than claiming that
printed `delta`, so Theorem 1 is intentionally outside this Palomar selection.

## Mechanical contract

`definition_names` is deliberately absent. The helper definitions in
`Challenge.lean` are fully specified and Comparator should compare them as
ordinary constants rather than treating them as definition holes.

`Challenge.lean` imports Mathlib alone. `Solution.lean` imports the two internal
solution adapters whose Mathlib-only `SolutionPrelude` modules define the same
helper constants before importing the substantive proof development. The local
`check_solution_preludes.py` guard checks those root Challenge declarations
against the preludes.
