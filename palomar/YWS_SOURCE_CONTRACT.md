# Yu–Wang–Samworth 2015 — source contract for Palomar selection

Working document for the Palomar preparation pass. It records, clause by clause,
what the published paper states and what the repository currently proves, so that
a selection decision is made against the source rather than against a declaration
name.

**Numbering is the published Biometrika numbering** — Theorem 1, Theorem 2,
Corollary 1, Theorem 3, Lemma A1. Many Lean names still carry the 2014 preprint's
single-counter numbering (Corollary 3, Theorem 4, Lemma 5); the correspondence is
Corollary 1 = Corollary 3, Theorem 3 = Theorem 4, Lemma A1 = Lemma 5.

**Sources used.** `prose/distilled_literature/YuWangSamworth2015_statistical_davis_kahan.tex`,
which records a read of the published article on 2026-08-13 and carries the
published indices, the published middle-block sharpness example and the Section 1
numerical illustration; and
`dev/yu-wang-samworth-2015-full-source-census.json`. The private preprint
transcription is not consulted here and no row is resolved by it. Where a row
below turns on a detail finer than the distilled TeX records, it says so.

**Ordering convention throughout:** eigenvalues and singular values decreasing,
`λ₁ ≥ … ≥ λ_p`, block `1 ≤ r ≤ s ≤ p`, `d = s − r + 1`, `E := Σ̂ − Σ`,
`D := Â − A`.

---

## Row T1 — Theorem 1, the mixed-gap Davis–Kahan baseline

| clause | source | current Lean |
| --- | --- | --- |
| scalar field | real | `RCLike 𝕜` |
| space | `Σ, Σ̂ ∈ ℝ^{p×p}` symmetric | abstract `E`, `[FiniteDimensional 𝕜 E]` |
| block | eigenvector blocks `V = (v_r,…,v_s)`, `V̂` at the same indices | `U V : Submodule 𝕜 E` with `IsInvariant A U`, `IsInvariant B V` |
| separation | `δ := inf{ \|λ̂ − λ\| : λ ∈ [λ_s, λ_r], λ̂ ∈ (−∞, λ̂_{s+1}] ∪ [λ̂_{r−1}, ∞) }`, conventions `λ̂₀ = −∞`, `λ̂_{p+1} = ∞` | `IntervalExteriorGap A B U V a b δ` |
| exact or lower bound | the printed `δ` is an exact infimum | `IntervalExteriorGap` is a separation *hypothesis*, not an identification of `δ` |
| sample separation | present — this is the point of Theorem 1, and why Theorem 2 supersedes it | present |
| numerator | `‖Σ̂ − Σ‖_F`, and the source says both norms may be replaced simultaneously by the operator norm or **any orthogonally invariant norm** | `N.toFun (B − A)` for `N : UnitarilyInvariantSeminorm 𝕜 E` |
| constant | `1` | `1` |
| conclusion | subspace `sin Θ` Frobenius norm | `N.toFun (sinThetaMap U V)` |
| production theorem | — | `yuWangSamworth_theorem1_uiNorm_le`, with `…_frobenius_le` and `…_opNorm_le` as specializations |
| census status | — | `compiled_generalized` |

**Disposition: stronger implementation theorem; no paper-facing wrapper exists.**
The unitarily-invariant-norm form is the right primary statement — the source
advertises that scope explicitly, so proving it is proving Theorem 1 rather than
overreaching. Three mismatches stand between it and a Palomar statement:

1. **Scalar scope.** The paper is real. Presenting the `RCLike` form as "exactly
   Theorem 1" would violate Phase 13.
2. **Block versus invariant subspace.** The paper fixes eigenvector blocks at the
   contiguous indices `r…s`; the Lean takes arbitrary invariant subspaces. That is
   more general, but a reviewer cannot see the paper in it.
3. **`δ` is a hypothesis, not the printed infimum.** Theorem 2 was tightened on
   2026-08-17 so that `SourcePopulationGap` *identifies* `Δ`. Theorem 1 has had no
   equivalent treatment.

**NOT SELECTED, 2026-08-29, and the reason is a source question, not size.**

Writing the printed `δ` exactly requires the paper's endpoint conventions for the
*sample* spectrum, and as the distilled TeX records them they make Theorem 1
vacuous at any block touching either end of the spectrum — including the top-`d`
block, which is the common case in statistics. The TeX prints
`λ̂₀ = −∞` and `λ̂_{p+1} = ∞`, so at `r = 1` the ray `[λ̂_{r−1}, ∞)` becomes all of
`ℝ`, the infimum defining `δ` is `0`, and the hypothesis `δ > 0` is unsatisfiable;
symmetrically at `s = p` for the other ray.

The reading that makes the theorem say what it evidently means is the opposite
one — `λ̂₀ = +∞` and `λ̂_{p+1} = −∞`, which make the missing ray **empty**, exactly
as Theorem 2's `λ₀ = +∞`, `λ_{p+1} = −∞` do for the population gaps. Under that
reading the exterior set is the sample eigenvalues genuinely outside the block,
which is what the classical Davis–Kahan separation is.

Two possibilities, and this repository cannot distinguish them from what is
checked in: the distilled transcription swapped the two conventions, or the
published article prints them as recorded and Theorem 1 is vacuous at end blocks.
The first is more likely. Resolving it needs a fresh read of the Biometrika
article, and it is a maintainer decision, not an agent's.

Note that the Lean development is unaffected either way: it never used the printed
conventions, phrasing the separation as `IntervalExteriorGap`, an intrinsic
spectral condition. What is blocked is only the claim that a Palomar statement
*is* the printed `δ`.

Until that is settled, selecting Theorem 1 would mean either asserting a
convention the source may not have, or comparing a statement that is vacuous
exactly where the theorem is used. Neither is acceptable, so Theorem 1 is left
out and the metadata says the substantive development formalizes it.

The remaining work, once the convention is settled, is small: a paper-facing
`theorem1_uiNorm` on `EuclideanSpace ℝ (Fin p)` at the block `r…s` modelled on
`theorem2_sinTheta`, plus a Challenge-side unitarily-invariant-norm interface
(subadditive, absolutely homogeneous, two-sided unitarily invariant — the three
fields of `UnitarilyInvariantSeminorm`, which carries no positivity requirement)
and an adapter constructing that structure from the interface.

---

## Row T2-1 — Theorem 2, first conclusion (YWS-1)

| clause | source | current Lean |
| --- | --- | --- |
| scalar field | real | `EuclideanSpace ℝ (Fin p)` ✓ |
| block | `1 ≤ r ≤ s ≤ p`, `d = s − r + 1` | `hr : r ≤ s`, `hs : s < p`, `hd : d = s − r + 1` ✓ |
| population frame | orthonormal `V` with `Σ v_j = λ_j v_j` | `IsEigenvectorBlock Sigma hSigma hr hs hd V` ✓ |
| sample frame | orthonormal `V̂` with `Σ̂ v̂_j = λ̂_j v̂_j`, **arbitrary** | `IsEigenvectorBlock SigmaHat …` — arbitrary supplied frame ✓ |
| sample separation | **none** | none ✓ |
| denominator | `Δ = min(λ_{r−1} − λ_r, λ_s − λ_{s+1})`, conventions `λ₀ = +∞`, `λ_{p+1} = −∞` | `SourcePopulationGap Sigma hSigma r s Delta` — identifies `Δ` as the greatest real satisfying the two boundary inequalities, with vacuous quantification for a missing endpoint and an explicit full-space branch for the `+∞` convention ✓ |
| exact or lower bound | exact | **exact** ✓ |
| numerator | `2 min(√d ‖E‖_op, ‖E‖_F)` | `2 * min (√d * ‖(SigmaHat − Sigma)‖_op) (frobeniusNorm (SigmaHat − Sigma))` ✓ |
| conclusion | `‖sin Θ(V̂, V)‖_F` | `sinThetaNorm`, tied by an equality hypothesis to `TauCeti.sinThetaFrobenius (span V) (span V̂)` ✓ |
| production theorem | — | `YuWangSamworth2015.theorem2_sinTheta` |
| census status | — | `compiled_exact` |

**Disposition: exact.** This is the reference standard for the whole pass.

---

## Row T2-2 — Theorem 2, aligned-frame conclusion (YWS-2)

Hypotheses identical to T2-1. Conclusion: `∃ Ô ∈ O(d)` with
`‖V̂Ô − V‖_F ≤ 2^{3/2} min(√d ‖E‖_op, ‖E‖_F) / Δ`.

`theorem2_alignedFrame` returns `O ∈ Matrix.orthogonalGroup (Fin d) ℝ` and bounds
`√(∑ᵢ ‖∑ⱼ O j i • V̂ j − V i‖²)` — the supplied population frame is compared
against, not some other frame spanning the same block, and the alignment is an
honest orthogonal matrix.

**Disposition: exact.**

---

## Row C1-1 — Corollary 1, first display

| clause | source | current Lean |
| --- | --- | --- |
| scalar field | real | `RCLike 𝕜` |
| space | `ℝ^{p×p}` | abstract `E`, `finrank 𝕜 E = n` |
| vectors | unit `v, v̂` with `Σ v = λ_j v`, `Σ̂ v̂ = λ̂_j v̂`; `v̂` **arbitrary** at a repeated sample eigenvalue | `‖u‖ = 1`, `‖v‖ = 1`, `A u = λ_j • u`, `B v = λ̂_j • v` — arbitrary ✓ |
| denominator | `Δ_j = min(λ_{j−1} − λ_j, λ_j − λ_{j+1})`, exact | `OrderedBlockBoundaryGap hA hn j j Δ` — a **lower bound**, not an identification |
| sample separation | none | none ✓ |
| numerator/constant | `2 ‖E‖_op` | `2 * ‖(B − A)‖_op` ✓ |
| production theorem | — | `yuWangSamworth_corollary1_sinTheta_le` |

## Row C1-2 — Corollary 1, second display

Adds `v̂ᵀv ≥ 0` and concludes `‖v̂ − v‖ ≤ 2^{3/2} ‖E‖_op / Δ_j`. Lean:
`yuWangSamworth_corollary1_real_le`, over a real `F`, with `0 ≤ ⟪v, u⟫`. Same
denominator issue.

**Disposition for both: printed hypothesis, but two mismatches.** The gap
hypothesis is the printed one in *shape* — only the two neighbouring population
eigenvalues — which is the hard part and is already right. What is missing is the
`SourcePopulationGap` exactness treatment that Theorem 2 received, and the real
`EuclideanSpace ℝ (Fin p)` presentation. Both are wrapper work, not new
mathematics.

**Sample-degeneracy witness:** `yuWangSamworth_corollary1_scalarSample` — for
`Σ = diag(1,0)` and `Σ̂ = I/2` every unit vector is an admissible `v̂`. This is the
semantic regression test named in Phase 6.

---

## Rows T3-R-1 / T3-L-1 — Theorem 3, right and left sine conclusions

| clause | source | current Lean |
| --- | --- | --- |
| scalar field | real | `RCLike 𝕜` |
| shape | `A, Â ∈ ℝ^{p×q}`, rectangular | `A Â : E →ₗ[𝕜] F`, distinct spaces ✓ |
| block | `1 ≤ r ≤ s ≤ rank(A)`, `d = s − r + 1` | `hsn : s + 1 ≤ n`, `hd : r + d = s + 1`, block `consecutiveEmb` ✓ |
| frames | ordered singular frames, arbitrary | `IsOrderedRightSingularFrame` / `…Left…`, arbitrary ✓ |
| denominator | `Δ_sv = min(σ_{r−1}² − σ_r², σ_s² − σ_{s+1}²)` with conventions `σ₀² = +∞` and **`σ_{rank(A)+1}² = −∞`, which is false** | two lower-bound clauses on `A.singularValues q ^ 2 − A.singularValues p ^ 2` at the ambient indices |
| exact or lower bound | printed as an exact minimum | lower bound |
| sample separation | none | none ✓ |
| numerator | `2 (2σ₁ + ‖D‖_op) min(√d ‖D‖_op, ‖D‖_F)` | same, with `A.singularValues 0` for `σ₁` ✓ |
| production theorem | — | `yuWangSamworth_rightSingularSubspace_block_le`, `yuWangSamworth_leftSingularSubspace_block_le` |
| census status | — | `compiled_corrected` |

**Disposition: corrected source defect.** The printed convention
`σ_{rank(A)+1}² := −∞` makes the denominator infinite when `s = rank(A)`, so the
printed bound asserts that the two singular subspaces coincide when they can be
orthogonal. Refuted by `yuWangSamworth_theorem3_printed_rankBoundary_refutation`
and its Euclidean instance, which also exhibit `‖sin Θ‖_F = 1`. The corrected
convention is the ambient one the paper's own proof uses — pass to `AᵀA` with
eigenvalues `σ₁² ≥ … ≥ σ_q²` and apply Theorem 2, whose convention is
`λ_{q+1} := −∞` at the ambient index `q`, with `σ_j := 0` for `min(p,q) < j ≤ q`;
`σ_{p+1}² := −∞` on the left. Lean has always used that reading.

**This entry must be labelled corrected, never exact, and must disclose the
defect.**

---

## Rows T3-R-2 / T3-L-2 — Theorem 3, aligned-frame conclusions

Source: `∃ Ô ∈ O(d)` with
`‖V̂Ô − V‖_F ≤ 2^{3/2} (2σ₁ + ‖D‖_op) min(√d ‖D‖_op, ‖D‖_F) / Δ_sv`, and the
identical statement on the left.

Current Lean: `yuWangSamworth_rightSingularAlignedBasis_block_le` and its left
twin conclude

```
∃ w ŵ, Orthonormal w ∧ Orthonormal ŵ ∧ span w = span v ∧ span ŵ = span v̂ ∧
       √(∑ᵢ ‖ŵ i − w i‖²) ≤ …
```

**Disposition: CLOSED 2026-08-29 — the printed shape is now stated.**
`yuWangSamworth_rightSingularAlignedFrame_block_le` and its left twin conclude the
printed conclusion: a unitary `Ô` on the block's coordinate space with
`‖V̂ Ô − V‖_F ≤ …` against the supplied `V`. The alignment half was first factored
out as `exists_unitary_sqrt_sum_sq_norm_frameComp_sub_le` and its real matrix form
`exists_orthogonal_sqrt_sum_sq_norm_sub_le`, which need only two orthonormal
frames and any Frobenius sine bound, so the Procrustes step now exists once
instead of twice.

The finding that prompted this, recorded for the archive: this was the
basis-free content of the claim and it did prove the numerical bound, but it did
not say what the paper says — the paper rotates `V̂` by an orthogonal `Ô` and
compares against **the supplied `V`**, whereas the old statement asserted only
that *some* pair of frames spanning the two blocks achieves the bound.

This is exactly the defect that was found and closed for Theorem 2 on 2026-08-13,
when `yuWangSamworth_alignedBasis_*` was superseded by `yuWangSamworth_alignedFrame_*`
and then by `theorem2_alignedFrame`. **The correction was never propagated to
Theorem 3.** There is no `…AlignedFrame…` declaration for singular blocks; a grep
for `Matrix.orthogonalGroup` in the package reaches `Symmetric/Theorem2.lean` and
`Core/Procrustes.lean` only.

It was closed by the route predicted here: `frameComp`,
`frameAlignMatrix_mem_orthogonalGroup` and
`exists_unitary_sum_sq_norm_frameComp_sub_le` in `Core/Procrustes.lean` were
already stated for arbitrary frames, so it was a transport rather than a new
perturbation argument.

---

## Row A1 — Appendix Lemma A1

Orthonormal compression cannot increase the Frobenius norm, with equality for
orthonormal rows. Lean: `yuWangSamworth_lemma5_orthonormalColumns`,
`yuWangSamworth_lemma5_orthonormalRows` (preprint numbering in the names),
`compiled_generalized`. Optional for Palomar by the task's own instruction.

---

## Known source defects, neither of which may be concealed

1. **Equation (4)** — the printed double-angle identity omits a square on
   `(2 − ‖v̂ − v‖²)`. Corrected identity `yuWangSamworth_equation4`; printed form
   refuted at `c = 3/5` by `yuWangSamworth_equation4_printed_counterexample`.
   Not selected in either entry; to be disclosed in metadata.
2. **Theorem 3's rank-boundary convention** — as above. Selected, corrected, and
   disclosed.

---

## Selection consequences

| entry | rows | outcome |
| --- | --- | --- |
| A, `palomar/yws-symmetric` | T2-1, T2-2 | **selected, exact** |
| A, `palomar/yws-symmetric` | C1-1, C1-2 | **selected, exact** — `corollary1_sinTheta` and `corollary1_alignedVector` added |
| — | T1 | **not selected**; source-convention question, see the row |
| B, `palomar/yws-rectangular` | T3-R-1, T3-L-1 | **selected, corrected**, defect disclosed |
| B, `palomar/yws-rectangular` | T3-R-2, T3-L-2 | **selected, corrected** — printed aligned shape proved 2026-08-29 |
| — | A1 | not selected; formalized in the development, recorded in metadata |

Both entries pass the real Comparator, NanoDa and Lean's kernel, with axiom
closure exactly `propext`, `Classical.choice`, `Quot.sound`.

None of the library work this required was a Palomar-specific convenience: every
item is a paper-facing statement the authoritative package should carry anyway,
which is why it landed in `YuWangSamworth2015/` and not in a Palomar directory.
