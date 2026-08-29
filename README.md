# Yu–Wang–Samworth 2015, formalized in Lean 4

A machine-checked formalization of Yi Yu, Tengyao Wang and Richard J. Samworth,
*A useful variant of the Davis–Kahan theorem for statisticians*, Biometrika
**102** (2015) 315–323, <https://doi.org/10.1093/biomet/asv008>.

Published numbering throughout. The 2014 arXiv preprint shares one counter across
environments and numbers the same results differently; many Lean declaration names
still carry the preprint numbering, and the correspondence is
Corollary 1 = Corollary 3, Theorem 3 = Theorem 4, Lemma A1 = Lemma 5.

## What the paper says, and why it is cited

Let `Σ` be a real symmetric `p × p` matrix — a population covariance — and `Σ̂` a
symmetric estimate of it. Fix a block `r, …, s` of eigenvalue indices in
nonincreasing order and let `V`, `V̂` hold orthonormal eigenvectors of `Σ` and `Σ̂`
at those indices. How far is the sample eigenspace from the population one?

The classical Davis–Kahan answer divides the perturbation by a separation between
the population eigenvalues *inside* the block and the sample eigenvalues *outside*
it. That quantity mixes the two spectra, so it is random, unobserved, and is
typically what the statistician is trying to estimate in the first place. It can
vanish while the population spectrum is perfectly well separated: for
`Σ = diag(50, 40, 30, 20, 10)` and `Σ̂ = diag(54, 37, 32, 23, 21)` at the block
`r = s = 4` it is zero, while the population gap there is `10`.

**Yu, Wang and Samworth's contribution is that the separation may be taken
entirely inside the population spectrum.** With
`Δ = min(λ_{r−1} − λ_r, λ_s − λ_{s+1})`, `E = Σ̂ − Σ` and `d = s − r + 1`,

* `‖sin Θ(V̂, V)‖_F ≤ 2 min(√d ‖E‖_op, ‖E‖_F) / Δ`, and
* some `Ô ∈ O(d)` has `‖V̂Ô − V‖_F ≤ 2^{3/2} min(√d ‖E‖_op, ‖E‖_F) / Δ`.

Every hypothesis constrains `Σ` alone; `Σ̂` enters only through `E`. That is what
makes the bound usable, and it is why the paper is cited across spectral methods —
principal component analysis, spectral clustering, covariance estimation, and
network models where an adjacency or Laplacian matrix concentrates around a
population version.

**No sample eigengap is assumed, and that is not a technicality.** `Σ̂` may have a
repeated eigenvalue at the block, in which case `V̂` is not determined, and the
theorem quantifies over *every* admissible orthonormal sample eigenframe. A
formulation pinning `V̂` to one chosen eigenbasis would be a different and weaker
statement. `yuWangSamworth_corollary1_scalarSample` is the extreme witness: for
`Σ = diag(1, 0)` and `Σ̂ = I/2` every unit vector of the plane is an admissible
sample eigenvector, and Corollary 1 bounds the angle for each of them.

**The aligned-frame conclusion** is the second display above. `‖sin Θ‖_F` measures
the angle between two *subspaces*; the statistician usually wants to compare the
frames themselves, and the two differ by an orthogonal rotation of the block. The
theorem produces that rotation explicitly and compares `V̂Ô` against the supplied
`V`, not against some other frame of the same span.

**Theorem 3** carries all of this to rectangular `A, Â ∈ ℝ^{p×q}` and their
singular subspaces, with the squared population singular gap
`Δ_sv = min(σ²_{r−1} − σ²_r, σ²_s − σ²_{s+1})` and an extra factor
`(2σ₁ + ‖D‖_op)`. The paper presents it as a population-gap counterpart of Wedin's
generalized `sin θ` theorem, and it holds for right and left singular blocks
alike.

## What is formalized here

Every numbered result of the paper, at the printed generality:

| result | Lean |
| --- | --- |
| Theorem 1, the classical baseline | `yuWangSamworth_theorem1_uiNorm_le`, with Frobenius and operator-norm specializations |
| Theorem 2, first conclusion | `YuWangSamworth2015.theorem2_sinTheta` |
| Theorem 2, aligned frame | `YuWangSamworth2015.theorem2_alignedFrame` |
| Corollary 1, both displays | `YuWangSamworth2015.corollary1_sinTheta`, `YuWangSamworth2015.corollary1_alignedVector` |
| Theorem 3, right and left sine | `yuWangSamworth_rightSingularSubspace_block_le`, `yuWangSamworth_leftSingularSubspace_block_le` |
| Theorem 3, right and left aligned frame | `yuWangSamworth_rightSingularAlignedFrame_block_le`, `yuWangSamworth_leftSingularAlignedFrame_block_le` |
| Appendix Lemma A1, both halves | `yuWangSamworth_lemma5_orthonormalColumns`, `yuWangSamworth_lemma5_orthonormalRows` |

The `yuWangSamworth_*` names live in `YuWangSamworth2015.DavisKahanTheory`. Also
formalized: the Section 1 numerical illustration that Theorem 1's separation can
vanish, both Section 2 sharpness constructions, the deterministic content of the
Section 3 audit of statistical practice, and rank-one singular-vector corollaries
beyond the printed paper.

## Two source defects, neither concealed

**Printed Equation (4) is false as printed.** The paper rewrites `sin²(2θ)` in
terms of `‖v̂ − v‖²` and the printed right-hand side omits a square on the factor
`(2 − ‖v̂ − v‖²)`. Both directions are machine-checked:
`yuWangSamworth_equation4` proves the corrected identity and
`yuWangSamworth_equation4_printed_counterexample` refutes the printed polynomial
at inner product `3/5`.

**Theorem 3's printed rank-boundary convention is false.** The paper sets
`σ²_{rank(A)+1} := −∞`, which makes the denominator infinite when `s = rank(A)`,
so the printed bound asserts that the sample and population singular subspaces
coincide. They need not: take `A` and `Â` to be the orthogonal projections of `ℝ²`
onto the two coordinate axes — both have rank one, so `r = s = 1 = rank(A)` is
admissible and the printed hypothesis holds, yet the two right singular subspaces
are orthogonal and `‖sin Θ‖_F = 1`. Refuted by
`yuWangSamworth_theorem3_printed_rankBoundary_refutation`. The correction is the
paper's own proof's convention — pass to `AᵀA` with eigenvalues `σ²₁ ≥ ⋯ ≥ σ²_q`
and apply Theorem 2, whose convention is at the *ambient* index `q`, not at
`rank(A)`, with `σ_j = 0` past the rank. **The Theorem 3 statements here are the
corrected ones.**

## Palomar Registry entries

Preparation only. Nothing here claims registration, acceptance, or peer review.

| config | compares | status |
| --- | --- | --- |
| `palomar/yws-symmetric/comparator.json` | Theorem 2, both conclusions; Corollary 1, both displays | exact |
| `palomar/yws-rectangular/comparator.json` | Theorem 3, right and left, sine and aligned | source-corrected, as above |
| `palomar/yws-2015/comparator.json` | one general-index-set form of Theorem 2's first conclusion | prototype, kept as a regression |

The root `comparator.json` is a copy of the symmetric entry, which is the
preferred one. Each Challenge states its theorems against Mathlib alone, with
deliberate statement-side holes, and each Solution supplies the same declarations
from the libraries here. The clause-by-clause basis for what is selected, what is
not, and why, is [`palomar/YWS_SOURCE_CONTRACT.md`](palomar/YWS_SOURCE_CONTRACT.md).

Theorem 1 is deliberately not selected. It is formalized, but writing its printed
mixed separation exactly turns on the paper's endpoint conventions for the sample
spectrum, which as transcribed make the theorem vacuous at any block touching
either end of the spectrum. That question is recorded in the source contract and
is for the maintainer, not for a packaging decision.

## Where this comes from

This repository is an **extraction**.
[`AIQ-Kitware/aiq-dkps-formalization`](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
is authoritative: mathematics is developed, reviewed and audited there, and this
is a snapshot of the `ForTauCeti`, `DavisKahan` and `YuWangSamworth2015` packages
taken from it. `DavisKahan` is here because the Yu–Wang–Samworth package uses its
Hilbert–Schmidt/Frobenius ideal theory; it is a dependency, not the subject.

**Send changes upstream.** A fix made only here is lost at the next extraction.

The source census and the audit and gate scripts are deliberately not extracted;
they are maintenance machinery for the authoritative repository. Accordingly this
repository makes no coverage claim beyond the table above.

## Building

```bash
lake exe cache get              # Mathlib oleans
lake build                      # the mathematics
lake build Palomar              # the entries; their Challenge modules carry holes
```

## Verifying an entry

Comparator, `lean4export` and the independent NanoDa kernel are external tools.
`lean4export` reads this repository's oleans, so it must be built at the Lean in
`lean-toolchain` -- including the nested `lean4export` package inside a comparator
checkout, whose own pin is not the one you set on the checkout. With the tools on
PATH:

```bash
lake env comparator palomar/yws-symmetric/comparator.json
lake env comparator palomar/yws-rectangular/comparator.json
```

`lake env` is required: the exporter needs the Lake search path to find the
compiled modules. All three configs pass Comparator, NanoDa and Lean's own kernel,
with axiom closure exactly `propext`, `Quot.sound`, `Classical.choice`.

That is local verification only. It is not Palomar verification, not acceptance,
and not registration.
