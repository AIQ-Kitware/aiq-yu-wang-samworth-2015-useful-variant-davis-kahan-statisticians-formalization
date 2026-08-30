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
vanish while the population spectrum is perfectly well separated. The paper's own
§1 illustration is `Σ = diag(50, 40, 30, 20, 10)` and `Σ̂ = diag(54, 37, 32, 23,
21)` at the eigenvectors for the second, third and fourth largest eigenvalues —
`r = 2`, `s = 4` in the paper's one-based indexing, the zero-based Lean block
`1, 2, 3`. There `λ₄ = 20` lies in the exterior ray `(−∞, λ̂₅] = (−∞, 21]`, so the
classical separation is `0`, while the population gap
`min(λ₁ − λ₂, λ₄ − λ₅) = 10`.

**Yu, Wang and Samworth's contribution is that the separation may be taken
entirely inside the population spectrum.** With
`Δ = min(λ_{r−1} − λ_r, λ_s − λ_{s+1})`, `E = Σ̂ − Σ` and `d = s − r + 1`,

* `‖sin Θ(V̂, V)‖_F ≤ 2 min(√d ‖E‖_op, ‖E‖_F) / Δ`, and
* some `Ô ∈ O(d)` has `‖V̂Ô − V‖_F ≤ 2^{3/2} min(√d ‖E‖_op, ‖E‖_F) / Δ`.

Every *separation* hypothesis constrains `Σ` alone: `Δ` is built from the
population spectrum only, and `Σ̂` enters the bound solely through `E`. (`Σ̂` is of
course assumed symmetric, and `V̂` is assumed to be one of its eigenframes at the
block; what is absent is any gap or separation condition on its spectrum.) That is
what makes the bound usable, and it is why the paper is cited across spectral
methods — principal component analysis, spectral clustering, covariance
estimation, and network models where an adjacency or Laplacian matrix concentrates
around a population version.

**No sample eigengap is assumed in Theorem 2 or Corollary 1, and that is not a
technicality.** `Σ̂` may have a repeated eigenvalue at the block, in which case `V̂`
is not determined, and the theorem quantifies over *every* admissible orthonormal
sample eigenframe. A formulation pinning `V̂` to one chosen eigenbasis would be a
different and weaker statement. `yuWangSamworth_corollary1_scalarSample` is the
extreme witness: for `Σ = diag(1, 0)` and `Σ̂ = I/2` every unit vector of the plane
is an admissible sample eigenvector, and Corollary 1 bounds the angle for each of
them. Theorem 1 is the classical baseline the paper argues *against*, and its
separation is mixed by design.

**The aligned-frame conclusion** is the second display above. `‖sin Θ‖_F` measures
the angle between two *subspaces*; the statistician usually wants to compare the
frames themselves, and the two differ by an orthogonal rotation of the block. The
theorem produces that rotation explicitly and compares `V̂Ô` against the supplied
`V`, not against some other frame of the same span.

**Theorem 3** carries all of this to rectangular `A, Â ∈ ℝ^{p×q}` and their
singular subspaces, for a block `1 ≤ r ≤ s ≤ rank(A)`, with the squared population
singular gap `Δ_sv = min(σ²_{r−1} − σ²_r, σ²_s − σ²_{s+1})` and an extra factor
`(2σ₁ + ‖D‖_op)`. The paper presents it as a population-gap counterpart of Wedin's
generalized `sin θ` theorem, and it holds for right and left singular blocks
alike. Its printed rank-boundary convention is false; see below.

## What is formalized here

Every numbered result of the paper is represented in the development. They are
*not* all at the same distance from the printed page, and this table says which is
which rather than using one adjective for all of them.

| result | Lean | source disposition |
| --- | --- | --- |
| Theorem 1, the classical baseline | `yuWangSamworth_theorem1_uiNorm_le`, with Frobenius and operator-norm specializations | proved in a **more general** form (any unitarily invariant norm, arbitrary invariant subspaces) with an intrinsic separation; the printed `δ` is not reproduced, because its printed endpoint conventions make it vacuous at end blocks |
| Theorem 2, first conclusion | `YuWangSamworth2015.theorem2_sinTheta` | **source-exact** |
| Theorem 2, aligned frame | `YuWangSamworth2015.theorem2_alignedFrame` | **source-exact** |
| Corollary 1, both displays | `YuWangSamworth2015.corollary1_sinTheta`, `YuWangSamworth2015.corollary1_alignedVector` | **source-exact** |
| Theorem 3, right and left sine | `YuWangSamworth2015.theorem3_rightSinTheta`, `…theorem3_leftSinTheta` | **corrected**: a false printed boundary convention is replaced, the printed block condition `s ≤ rank(A)` is kept |
| Theorem 3, right and left aligned frame | `YuWangSamworth2015.theorem3_rightAlignedFrame`, `…theorem3_leftAlignedFrame` | **corrected**, same reason |
| Appendix Lemma A1, both halves | `yuWangSamworth_lemma5_orthonormalColumns`, `yuWangSamworth_lemma5_orthonormalRows` | proved in a **more general** form |

The `yuWangSamworth_*` names live in `YuWangSamworth2015.DavisKahanTheory`; the
paper-facing wrappers live directly in `YuWangSamworth2015`. The Theorem 3
wrappers are specializations of
`YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularSubspace_block_le`
and its three companions, which are proved without the source's rank restriction —
a valid generalization that is kept, but is not what the paper states.

Also formalized: the §1 numerical illustration above, both §2 sharpness
constructions, the deterministic content of the §3 audit of statistical practice,
and rank-one singular-vector corollaries beyond the printed paper.

## Three source defects, none concealed

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
corrected ones.** Two things that are *not* changed, and are easy to conflate with
this: the paper's own block condition `1 ≤ r ≤ s ≤ rank(A)` is retained, and `Δ`
is the paper's exact denominator rather than an arbitrary positive lower bound.

**Theorem 1's printed sample endpoint conventions are inverted.** Its separation
is an infimum over the two exterior rays `(−∞, λ̂_{s+1}] ∪ [λ̂_{r−1}, ∞)`, and the
article defines `λ̂₀ = −∞` and `λ̂_{p+1} = +∞`. Those values make the corresponding
ray the whole line at `r = 1` or `s = p`, so `δ = 0` and the hypothesis `δ > 0` is
unsatisfiable at any block touching an end of the spectrum — including the top-`d`
block, the common case in statistics. The intended reading is the opposite one,
`λ̂₀ = +∞` and `λ̂_{p+1} = −∞`, which makes the missing ray empty, exactly as
Theorem 2's population conventions do. This is milder than the other two: it
degrades a baseline theorem to vacuity rather than asserting something false. The
Lean statement is unaffected — it phrases the separation as an intrinsic spectral
condition and never used the printed conventions — and no declaration here claims
to be the printed `δ`.

## Palomar Registry entries

Preparation only. Nothing here claims registration, acceptance, or peer review.

| config | metadata | compares | source relationship | status |
| --- | --- | --- | --- | --- |
| `palomar/yws-symmetric/comparator.json` | `palomar/yws-symmetric/formalization.yaml` | Theorem 2, both conclusions; Corollary 1, both displays | `formalizes` | exact |
| `palomar/yws-rectangular/comparator.json` | `palomar/yws-rectangular/formalization.yaml` | Theorem 3, right and left, sine and aligned, plus the two singular-frame equivalences | `adapts` | source-corrected, as above |
| `palomar/yws-2015/comparator.json` | — | one general-index-set form of Theorem 2's first conclusion | — | prototype, kept as a regression; superseded by `yws-symmetric` |

A Palomar entry is one Comparator configuration, and one `formalization.yaml`
records one relationship per source. The two paper-facing entries therefore carry
their own metadata beside their own configuration, because Theorem 2 is formalized
as printed while Theorem 3 is a documented correction. A submission selects both
paths explicitly. The repository-root `formalization.yaml` is the repository-wide
record and the default metadata path; it is not the metadata of either entry.

Each Challenge states its theorems against Mathlib alone, with deliberate
statement-side holes, and each Solution supplies the same declarations from the
libraries here. `definition_names` is empty in both paper-facing configurations,
deliberately: Comparator treats a listed name as a *definition hole* and stops
comparing that definition's value, and every helper definition in these Challenges
is fully specified, so listing them weakened the comparison rather than
strengthening it. The clause-by-clause basis for what is selected, what is not,
and why, is [`palomar/YWS_SOURCE_CONTRACT.md`](palomar/YWS_SOURCE_CONTRACT.md).

Theorem 1 is deliberately not selected, for the reason in the previous section: a
paper-facing statement of its printed `δ` would be a third corrected entry, not an
exact one, and that scope decision has not been taken.

## Where this comes from

This repository is an **extraction**, and it carries the proof: `ForTauCeti`,
`DavisKahan` and `YuWangSamworth2015` are here in full and are built here, so this
is a substantive formalization in Palomar's sense and its metadata carries no
`repository` key. `DavisKahan` is present because the Yu–Wang–Samworth package
uses its Hilbert–Schmidt/Frobenius ideal theory; it is a dependency, not the
subject.

[`AIQ-Kitware/aiq-dkps-formalization`](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
remains **authoritative**: the mathematics is developed, reviewed and audited
there, and this is a snapshot of those three packages taken from it. That is a
statement about where work happens, not about where the proof lives.

**Send changes upstream.** A fix made only here is lost at the next extraction.

The source census and the audit and gate scripts are deliberately not extracted;
they are maintenance machinery for the authoritative repository. Accordingly this
repository makes no coverage claim beyond the tables above.

## Building

```bash
lake exe cache get              # Mathlib oleans
lake build                      # the mathematics
lake build Palomar              # the entries; their Challenge modules carry holes
```

## Verifying an entry

Comparator, `lean4export` and the independent NanoDa kernel are external tools.
`lean4export` reads this repository's oleans, so it must be built at the Lean in
`lean-toolchain` — including the nested `lean4export` package inside a comparator
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
