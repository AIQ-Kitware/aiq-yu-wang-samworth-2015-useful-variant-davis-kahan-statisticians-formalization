/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.Symmetric
import YuWangSamworth2015.Rectangular
import YuWangSamworth2015.Appendix

/-!
# Citation-priority Yu--Wang--Samworth API

Numbering here is the **published** Biometrika numbering.  The 2014 preprint
shares one counter and calls the last three Corollary 3, Theorem 4 and Lemma 5,
which several declaration names in this library still spell; the census carries
the translation table.

Every numbered result of the paper is represented.  They are not all at the same
distance from the printed page, and this list says which is which:

1. classical Davis--Kahan Theorem 1, in a form more general than printed and with
   an intrinsic separation rather than the printed `delta`;
2. population-gap Theorem 2 and its aligned-frame conclusion, for arbitrary
   ordered eigenframes, source-exact;
3. rank-one Corollary 1, both displays, with the unit normalization the
   standalone printed display omits written out -- without it the second display
   is false, and `corollary1_printed_unnormalized_counterexample` refutes it;
4. right and left singular-subspace Theorem 3, in its corrected form -- the
   printed rank-boundary convention is false;
5. Appendix Lemma A1, in a form more general than printed.

## Finding the source-shaped statement

The general theorems select their block by an index embedding and take the
intrinsic separation as hypothesis.  Statements in the paper's own shape —
a contiguous block `r..s` with the two-sided boundary gap
`min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`, under the printed conventions
`λ_0 = +∞`, `λ_{p+1} = −∞` — are:

* `YuWangSamworth2015.theorem2_sinTheta` and
  `YuWangSamworth2015.theorem2_alignedFrame` are the canonical paper-facing
  Theorem 2 declarations.  They use `Real^p`, source-style names, the literal
  conditions `r ≤ s`, `s < p`, `d = s - r + 1`, arbitrary supplied eigenvector
  blocks, and the exact source population gap `SourcePopulationGap`.  The sine
  quantity is an explicit parameter tied to its concrete Lean realization by an
  equality hypothesis, while the perturbation Frobenius norm is written through
  the reducible application-level abbreviation `frobeniusNorm`.  The aligned
  conclusion exposes its orthogonal matrix directly.  The more general
  `yuWangSamworth_sinTheta_block_le` and `yuWangSamworth_alignedFrame_block_le`
  remain the implementation-oriented `RCLike` forms;
* `YuWangSamworth2015.yuWangSamworth_sinTheta_block_le_residual` and
  `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le_residual` for the sharper
  residual numerators the paper says its proof establishes,
  `‖V̂Λ − ΣV̂‖_F` in place of the perturbation norm;
* `yuWangSamworth_corollary1_sinTheta_le` and
  `yuWangSamworth_corollary1_real_le` for Corollary 1;
* `yuWangSamworth_rightSingularSubspace_block_le` and its three siblings for
  Theorem 3, in singular-value notation with the corrected boundary convention.

The surface also includes direct rank-one singular-vector corollaries, the
rank-one algebraic identity recorded as equation (4), all three Section 2
sharpness constructions, the Section 1 illustration that Theorem 1's separation
can vanish, the deterministic core of the Section 3 diagnosis, and
`yuWangSamworth_corollary1_scalarSample`, the witness that the sample side
genuinely admits an arbitrary unit eigenvector at a repeated sample eigenvalue.
-/
