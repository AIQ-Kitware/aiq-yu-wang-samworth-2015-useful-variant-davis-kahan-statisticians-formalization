# Yu-Wang-Samworth 2015, formalized in Lean 4

A machine-checked formalization of Yi Yu, Tengyao Wang and Richard J. Samworth,
*A useful variant of the Davis-Kahan theorem for statisticians*, Biometrika
**102** (2015) 315-323, <https://doi.org/10.1093/biomet/asv008>.

Published numbering is used in the paper-facing documentation. Some internal
Lean names retain numbering from the 2014 preprint; the correspondence is
Corollary 1 = Corollary 3, Theorem 3 = Theorem 4, Lemma A1 = Lemma 5.

## The population-gap idea

For real symmetric `Sigma, SigmaHat`, the classical Davis-Kahan separation mixes
population eigenvalues in the selected block with sample eigenvalues outside it.
Yu, Wang and Samworth replace that by the population-only gap

`Delta = min(lambda_(r-1) - lambda_r, lambda_s - lambda_(s+1))`.

With `E = SigmaHat - Sigma` and `d = s - r + 1`, Theorem 2 gives

* `||sin Theta(Vhat,V)||_F <= 2 min(sqrt(d)||E||_op,||E||_F)/Delta`, and
* an orthogonal `O` with
  `||Vhat O - V||_F <= 2^(3/2) min(sqrt(d)||E||_op,||E||_F)/Delta`.

No sample eigengap is assumed. The sample frame is arbitrary among admissible
orthonormal eigenframes at the selected indices, including under multiplicity.
Corollary 1 is the rank-one specialization.

Theorem 3 carries the same idea to a general real `p x q` matrix and its right
and left singular subspaces, with the squared population singular gap and the
additional factor `(2 sigma_1 + ||Ahat-A||_op)`.

## Source fidelity

The formalization deliberately distinguishes three source dispositions instead
of describing every selected theorem with one adjective:

| selected result | disposition |
| --- | --- |
| Theorem 2, both conclusions | **source-exact** |
| Corollary 1, both displays | **source-faithful**: the unit normalization inherited from its `d = 1` derivation from Theorem 2 is written out |
| Theorem 3, right/left sine and aligned-frame conclusions | **source-corrected**: the false printed rank-boundary convention is replaced by the ambient Gram-spectrum convention used by the paper's proof |

The standalone printed Corollary 1 does not state `||v|| = ||vhat|| = 1`, even
though the preceding sentence introduces it as the `d = 1` case of Theorem 2,
whose frame columns are orthonormal. Without normalization its second display is
false; the repository contains a machine-checked counterexample.

Theorem 3 prints `sigma^2_(rank(A)+1) := -infinity`. At `s = rank(A)` that makes
the denominator infinite and can force a zero bound although sample and
population singular subspaces are orthogonal. The corrected statements read the
endpoint in the ambient spectrum of `A^T A` (right) or `A A^T` (left), where
singular values are zero past rank. The paper's separate restriction
`1 <= r <= s <= rank(A)` is retained.

Two additional printed defects are formalized but are not part of the Palomar
selection: Equation (4) omits a square, and Theorem 1's printed sample endpoint
conventions invert its exterior rays and make its positive-separation hypothesis
impossible at end blocks. Appendix Lemma A1, sharpness constructions, the
Section 1 numerical illustration and other supporting material are also present
in the wider development.

## Palomar Registry submission

Preparation only. Nothing here claims registration, acceptance, or peer review.

This repository now uses the conventional **single root entry**:

```text
Challenge.lean
Solution.lean
comparator.json
formalization.yaml
lakefile.toml
lake-manifest.json
lean-toolchain
LICENSE
```

The root Comparator selects ten declarations in one review surface:

* Theorem 2: `YWSPalomar.theorem2_sinTheta`,
  `YWSPalomar.theorem2_alignedFrame`;
* Corollary 1: `YWSPalomar.corollary1_sinTheta`,
  `YWSPalomar.corollary1_alignedVector`;
* corrected Theorem 3: right/left sine and aligned-frame conclusions; and
* the right/left equivalences between the Gram form and the paper's paired
  singular-vector equations.

Because the combined entry includes the corrected Theorem 3, its single source
relationship is conservatively `adapts`. `formalization.yaml` then explains the
finer per-result dispositions above rather than pretending Theorem 2 itself was
changed.

`Challenge.lean` imports Mathlib alone. `Solution.lean` composes the two
previously verified implementation adapters under `Palomar/`; those adapters
remain implementation modules only, not separate Palomar entries. Their
Mathlib-only `SolutionPrelude` modules ensure Comparator-visible helper constants
are elaborated before the larger proof development is imported.

The clause-by-clause basis for the merged selection is
`registry/YWS_SOURCE_CONTRACT.md`.

## Building and verification

```bash
lake exe cache get
lake build
python3 scripts/check_solution_preludes.py
python3 scripts/check_palomar_readiness.py
scripts/verify_palomar.sh
```

The local verifier builds the root Challenge and Solution named by
`comparator.json`, runs the static preflight, then runs Comparator with NanoDa and
Lean kernel replay. It uses verification tools already on `PATH`; otherwise it
can discover `~/.cache/palomar-tools-latest/bin` or the newest dated
`~/.cache/palomar-tools-YYYYMMDD/bin` bundle.

That is local preparation only. Palomar's own verifier and editorial review are
the authority for a submission.

## Repository lineage

This repository is an extraction containing the substantive proof sources
`ForTauCeti`, `DavisKahan`, and `YuWangSamworth2015` in full.
`AIQ-Kitware/aiq-dkps-formalization` remains the authoritative development
repository: mathematics is developed and audited there, while this repository is
the Palomar-facing snapshot. A mathematical fix made here should also be carried
upstream before the next extraction.
