# Yu–Wang–Samworth 2015 — source contract for the Palomar selections

Clause-by-clause record of what the published paper states and what the two
prepared Palomar entries compare, so that a selection decision is made against
the source rather than against a declaration name.

**Regenerated 2026-08-29 from the final theorem types.** Every row below was
re-read against the Lean signatures in the tree at that date, not carried over
from an earlier state of this file.

**Numbering is the published Biometrika numbering** — Theorem 1, Theorem 2,
Corollary 1, Theorem 3, Lemma A1. Many Lean names still carry the 2014
preprint's single-counter numbering (Corollary 3, Theorem 4, Lemma 5); the
correspondence is Corollary 1 = Corollary 3, Theorem 3 = Theorem 4,
Lemma A1 = Lemma 5.

**Sources used.** The published Biometrika article (doi:10.1093/biomet/asv008),
read directly for this pass on 2026-08-29;
`prose/distilled_literature/YuWangSamworth2015_statistical_davis_kahan.tex`, the
repository's transformative reconstruction; and
`dev/yu-wang-samworth-2015-full-source-census.json`.

**Ordering convention throughout:** eigenvalues and singular values decreasing,
`λ₁ ≥ … ≥ λ_p`, paper block `1 ≤ r ≤ s ≤ p`, `d = s − r + 1`, `E := Σ̂ − Σ`,
`D := Â − A`. Lean indices are zero-based: the paper's `r…s` is the Lean block
`r−1 … s−1`, and every "Challenge zero-based block" entry below is written in
the Lean variables.

---

## The two entries

| entry | comparator config | metadata | compared | source relationship |
| --- | --- | --- | --- | --- |
| symmetric | `registry/yws-symmetric/comparator.json` | `registry/yws-symmetric/formalization.yaml` | Theorem 2 (both conclusions), Corollary 1 (both displays) | `formalizes` — **source-faithful**: Theorem 2 exact, Corollary 1 with one inherited hypothesis written out |
| rectangular | `registry/yws-rectangular/comparator.json` | `registry/yws-rectangular/formalization.yaml` | Theorem 3 (right/left × sine/aligned), plus the two singular-frame equivalences | `adapts` — **source-corrected** |

Not compared by either entry: Theorem 1, Appendix Lemma A1, the two Section 2
sharpness constructions, the Section 1 numerical illustration, the Section 3
audit content, and the three source-defect refutations. All are formalized in the
development; see the rows below for Theorem 1 and Lemma A1.

---

## Row T2-1 — Theorem 2, first conclusion

| clause | source | Challenge |
| --- | --- | --- |
| published result | Theorem 2, display (2) | — |
| scalar field / space | real symmetric `Σ, Σ̂ ∈ ℝ^{p×p}` | `Rp p = EuclideanSpace ℝ (Fin p)`, `Sigma.IsSymmetric` ✓ |
| source one-based block | `1 ≤ r ≤ s ≤ p`, `d = s − r + 1` | — |
| Challenge zero-based block | — | `hr : r ≤ s`, `hs : s < p`, `hd : d = s - r + 1` ✓ |
| source rank restriction | none in Theorem 2 | none ✓ |
| population frame | orthonormal `V` with `Σ v_j = λ_j v_j` | `IsEigenvectorBlock Sigma hSigma hr hs hd V` ✓ |
| sample frame | orthonormal `V̂` with `Σ̂ v̂_j = λ̂_j v̂_j`, **arbitrary** | `IsEigenvectorBlock SigmaHat …` — arbitrary supplied frame ✓ |
| arbitrary-frame status | every admissible orthonormal eigenframe, including under multiplicity | same; nothing pins `V̂` to a chosen eigenbasis ✓ |
| sample-gap status | **none** | none ✓ |
| exact denominator | `Δ = min(λ_{r−1} − λ_r, λ_s − λ_{s+1})` | `SourcePopulationGap Sigma hSigma r s Delta` — **identifies** `Δ` as the greatest real satisfying both boundary inequalities ✓ |
| endpoint convention | `λ₀ = +∞`, `λ_{p+1} = −∞` | vacuous quantification for a missing endpoint; the full block `r = 0`, `s + 1 = p` is an explicit disjunct, sound because the sine distance is then `0` ✓ |
| numerator and constant | `2 min(√d ‖E‖_op, ‖E‖_F)` | `2 * perturbation d (SigmaHat - Sigma)`, `perturbation = min (√d * opNorm) frobeniusNorm` ✓ |
| conclusion | `‖sin Θ(V̂, V)‖_F` | `sinThetaDist V Vhat`, the Frobenius sine distance between the two spans ✓ |
| source disposition | — | **exact** |
| production theorem used by Solution | — | `YuWangSamworth2015.theorem2_sinTheta` |

## Row T2-2 — Theorem 2, aligned-frame conclusion

Hypotheses identical to T2-1.

| clause | source | Challenge |
| --- | --- | --- |
| published result | Theorem 2, display (3) | — |
| aligned conclusion | `∃ Ô ∈ O(d)` with `‖V̂Ô − V‖_F ≤ …`, compared against **the supplied** `V` | `∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ`, bounding `√(∑ᵢ ‖∑ⱼ O j i • V̂ j − V i‖²)` against the supplied `V` ✓ |
| numerator and constant | `2^{3/2} min(√d ‖E‖_op, ‖E‖_F)` | `2 * Real.sqrt 2 * perturbation d (SigmaHat - Sigma)` ✓ |
| source disposition | — | **exact** |
| production theorem used by Solution | — | `YuWangSamworth2015.theorem2_alignedFrame` |

## Row C1-1 — Corollary 1, first display

| clause | source | Challenge |
| --- | --- | --- |
| published result | Corollary 1, first display | — |
| scalar field / space | real symmetric `Σ, Σ̂ ∈ ℝ^{p×p}` | `Rp p`, both `IsSymmetric` ✓ |
| source one-based block | `j ∈ {1, …, p}`, `d = 1` | — |
| Challenge zero-based block | — | `hj : j < p`, single index ✓ |
| source rank restriction | none | none ✓ |
| vectors | `v, v̂` with `Σ v = λ_j v`, `Σ̂ v̂ = λ̂_j v̂`. **The standalone printed display does not say they are unit vectors**; the sentence introducing the corollary does, by presenting it as the `d = 1` case of Theorem 2 | `hv : ‖v‖ = 1`, `hvHat : ‖vHat‖ = 1`, the two eigenvector equations — the inherited hypothesis written out, see the note below |
| arbitrary-frame status | `v̂` **arbitrary** at a repeated sample eigenvalue | arbitrary ✓ |
| sample-gap status | none | none ✓ |
| exact denominator | `Δ_j = min(λ_{j−1} − λ_j, λ_j − λ_{j+1})` | `SourcePopulationGap Sigma hSigma j j Delta` — identified, not bounded below ✓ |
| endpoint convention | `λ₀ = +∞`, `λ_{p+1} = −∞` | as in T2-1; the `p = 1` case is the full-block disjunct ✓ |
| numerator and constant | `2 ‖E‖_op` | `2 * opNorm (SigmaHat - Sigma)` ✓ |
| conclusion | `sin Θ(v̂, v)` | `‖P_{span{v̂}^⊥} v‖`, the length of the component of `v` orthogonal to `v̂` ✓ |
| source disposition | — | **source-faithful, with one inherited hypothesis explicit** |
| production theorem used by Solution | — | `YuWangSamworth2015.corollary1_sinTheta` |

## Row C1-2 — Corollary 1, second display

Hypotheses as C1-1 plus the printed orientation condition.

| clause | source | Challenge |
| --- | --- | --- |
| published result | Corollary 1, second display | — |
| orientation | `v̂ᵀv ≥ 0` | `hsign : 0 ≤ inner ℝ vHat v` ✓ |
| numerator and constant | `2^{3/2} ‖E‖_op` | `2 * Real.sqrt 2 * opNorm (SigmaHat - Sigma)` ✓ |
| conclusion | `‖v̂ − v‖` | `‖vHat - v‖` ✓ |
| source disposition | — | **source-faithful, with one inherited hypothesis explicit**; without it this display is false |
| production theorem used by Solution | — | `YuWangSamworth2015.corollary1_alignedVector` |

### The normalization, and why it cannot simply be dropped

The paper writes, immediately before the corollary: *"Many if not most
applications of this result will need only `s = r`, i.e., `d = 1`. In that case,
the statement simplifies a little; for ease of reference, we state it as a
corollary."* Theorem 2's `V` and `V̂` have orthonormal columns, so unit vectors
are what the corollary inherits and unambiguously means. The standalone display
nevertheless says only "if `v, v̂ ∈ ℝ^p` satisfy `Σ v = λ_j v` and
`Σ̂ v̂ = λ̂_j v̂`".

That omission is not harmless. The eigenvector equations are homogeneous and
`v̂ᵀv ≥ 0` only becomes more true under scaling, so from any instance take
`Σ̂ := Σ` and `v̂ := 2v`: every printed hypothesis holds, the perturbation is zero,
the printed bound is `0`, and `‖v̂ − v‖ = ‖v‖ = 1`. **The printed second display
is therefore false as literally stated**, and
`YuWangSamworth2015.corollary1_printed_unnormalized_counterexample` is the
machine-checked refutation. The printed first display survives scaling, being
about the angle between two spans, but is degenerate at `v̂ = 0`, which the
printed hypotheses also admit.

The two compared declarations write the normalization out. The source
relationship stays `formalizes`: what is made explicit is a hypothesis the source
supplies one sentence earlier, not a change to the result — unlike Theorem 3,
where a printed convention had to be replaced. But no claim of "no added
hypothesis" or "exactly as printed" may be made for Corollary 1, and none is.

**Sample-degeneracy witness, kept as a regression:**
`yuWangSamworth_corollary1_scalarSample` — for `Σ = diag(1,0)` and `Σ̂ = I/2`
every unit vector of the plane is an admissible `v̂`, and the corollary bounds
the angle for each of them. Not compared; it is the evidence that the
arbitrary-frame clause above has content.

---

## Rows T3-R-1 / T3-L-1 — Theorem 3, right and left sine conclusions

| clause | source | Challenge |
| --- | --- | --- |
| published result | Theorem 3, first display (right); the "identical bounds also hold" sentence for `U`, `Û` (left) | — |
| scalar field / shape | real `A, Â ∈ ℝ^{p×q}` | `A Ahat : Rn q →ₗ[ℝ] Rn p` ✓ |
| source one-based block | `1 ≤ r ≤ s ≤ rank(A)`, `d = s − r + 1` | — |
| Challenge zero-based block | — | `hr : r ≤ s`, `hd : d = s - r + 1` ✓ |
| **source rank restriction** | `s ≤ rank(A)` | `hrank : s < finrank ℝ (LinearMap.range A)` — **retained**; `s < q`, `s < p`, `0 < q`, `0 < p` are derived from it inside the proof and are not caller hypotheses ✓ |
| frames | orthonormal `V` (resp. `U`) with `A v_j = σ_j u_j` (resp. `Aᵀ u_j = σ_j v_j`) | `IsRightSingularBlock` / `IsLeftSingularBlock`: orthonormal plus the Gram equations `AᵀA vᵢ = σ²_{r+i} vᵢ`, `A Aᵀ uᵢ = σ²_{r+i} uᵢ`. Equivalent to the printed pair at these indices, and that equivalence is itself compared — see rows T3-EQ below ✓ |
| arbitrary-frame status | arbitrary orthonormal singular frame, no multiplicity assumption | arbitrary ✓ |
| sample-gap status | none | none ✓ |
| exact denominator | `Δ_sv = min(σ²_{r−1} − σ²_r, σ²_s − σ²_{s+1})` | `SourceSingularGap q A r s Delta` on the right, `SourceSingularGap p A r s Delta` on the left — **identifies** `Δ` as the greatest real satisfying both boundary inequalities ✓ |
| **endpoint convention** | printed `σ²₀ = +∞` and `σ²_{rank(A)+1} = −∞`; **the second is false** | corrected to the ambient convention the paper's own proof uses: `σ²₀ = +∞`, `σ²_{q+1} = −∞` on the right and `σ²_{p+1} = −∞` on the left, with `σ_j = 0` past the rank. Where the block ends at the rank the lower gap is the finite `σ²_s − 0`. The full-ambient-block case is an explicit disjunct, sound because the frame then spans everything **corrected** |
| numerator and constant | `2 (2σ₁ + ‖D‖_op) min(√d ‖D‖_op, ‖D‖_F)` | `2 * coefficient d A (Ahat - A)`, `coefficient = (2 * σ₁ + opNorm D) * min (√d * opNorm D) (frobeniusNorm D)`, with `σ₁ = A.singularValues 0` ✓ |
| conclusion | `‖sin Θ(V̂, V)‖_F` (resp. `‖sin Θ(Û, U)‖_F`) | `sinThetaDist V Vhat` / `sinThetaDist U Uhat` ✓ |
| source disposition | — | **source-corrected**, defect disclosed |
| production theorems used by Solution | — | `YuWangSamworth2015.theorem3_rightSinTheta`, `YuWangSamworth2015.theorem3_leftSinTheta` |

**The defect.** The printed convention `σ²_{rank(A)+1} := −∞` makes the
denominator infinite when `s = rank(A)`, so the printed bound asserts that the
two singular subspaces coincide when they can be orthogonal. Refuted by
`yuWangSamworth_theorem3_printed_rankBoundary_refutation` and its Euclidean
instance, which exhibit `‖sin Θ‖_F = 1` for two rank-one orthogonal projections
of the plane. **This entry must be labelled corrected, never exact, and must
disclose the defect.** Its metadata says `relationship: adapts`.

**What is *not* changed.** The paper's own block restriction `s ≤ rank(A)` is a
separate matter and is kept. The lower-level theorems
`yuWangSamworth_rightSingularSubspace_block_le` and its three companions remain
in the development without it, which is a valid generalization; the Palomar
statements deliberately compare at the paper's scope instead.

## Rows T3-R-2 / T3-L-2 — Theorem 3, aligned-frame conclusions

Hypotheses identical to T3-R-1 / T3-L-1.

| clause | source | Challenge |
| --- | --- | --- |
| published result | Theorem 3, second display, and the same for the left blocks | — |
| aligned conclusion | `∃ Ô ∈ O(d)` with `‖V̂Ô − V‖_F ≤ …` against **the supplied** `V` | `∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ` bounding `√(∑ᵢ ‖∑ⱼ O j i • V̂ j − V i‖²)` ✓ |
| numerator and constant | `2^{3/2} (2σ₁ + ‖D‖_op) min(√d ‖D‖_op, ‖D‖_F)` | `2 * Real.sqrt 2 * coefficient d A (Ahat - A)` ✓ |
| source disposition | — | **source-corrected** (the rank-boundary defect, unchanged from the sine rows) |
| production theorems used by Solution | — | `YuWangSamworth2015.theorem3_rightAlignedFrame`, `YuWangSamworth2015.theorem3_leftAlignedFrame` |

The printed *shape* — rotate `V̂` by an orthogonal `Ô` and compare against the
supplied `V` — was closed on 2026-08-29. Before that the only statements
concluded that *some* pair of frames spanning the two blocks achieves the bound,
which is the basis-free content and proves the numerical claim but is not what
the paper says. The alignment step is
`exists_orthogonal_sqrt_sum_sq_norm_sub_le`, which needs only two orthonormal
frames and a Frobenius sine bound, so no perturbation argument is duplicated.

## Rows T3-EQ — the singular-frame representation, machine-checked

The paper writes the printed hypothesis as the paired singular-vector equations
`A v_j = σ_j u_j` and `Aᵀ u_j = σ_j v_j`; its proof immediately passes to the
Gram operators, and the Challenge states the Gram form. These two rows prove the
two readings agree, so the choice is notational rather than a change of
hypothesis.

| clause | content |
| --- | --- |
| compared declarations | `YWSRectangular.isRightSingularBlock_iff_pairedSingularVectors`, `YWSRectangular.isLeftSingularBlock_iff_pairedSingularVectors` |
| statement | at a block with `s < rank(A)`, `IsRightSingularBlock A hr hd V` holds iff `V` is orthonormal and there is an orthonormal `U` with `A v_i = σ_{r+i} u_i` and `Aᵀ u_i = σ_{r+i} v_i`; and the mirror image on the left |
| why the rank condition is needed | it is exactly what makes every selected `σ_{r+i}` strictly positive, so `u_i := σ_{r+i}⁻¹ A v_i` is defined and orthonormal |
| source disposition | supporting equivalence; it is *not* one of the paper's numbered results and is not counted as one |
| production theorems used by Solution | `YuWangSamworth2015.isRightSingularBlock_iff_pairedSingularVectors`, `YuWangSamworth2015.isLeftSingularBlock_iff_pairedSingularVectors` |

---

## Row T1 — Theorem 1, the mixed-gap Davis–Kahan baseline

**NOT SELECTED.** Formalized in the development; not compared by either entry.

| clause | source | current Lean |
| --- | --- | --- |
| published result | Theorem 1, display (1) | — |
| scalar field | real | `RCLike 𝕜` |
| space | `Σ, Σ̂ ∈ ℝ^{p×p}` symmetric | abstract `E`, `[FiniteDimensional 𝕜 E]` |
| block | eigenvector blocks `V = (v_r,…,v_s)`, `V̂` at the same indices | `U V : Submodule 𝕜 E` with `IsInvariant A U`, `IsInvariant B V` |
| separation | `δ := inf{ \|λ̂ − λ\| : λ ∈ [λ_s, λ_r], λ̂ ∈ (−∞, λ̂_{s+1}] ∪ [λ̂_{r−1}, ∞) }`, conventions `λ̂₀ = −∞`, `λ̂_{p+1} = +∞` | `IntervalExteriorGap A B U V a b δ` |
| exact or lower bound | the printed `δ` is an exact infimum | a separation *hypothesis*, not an identification of `δ` |
| sample separation | present — this is the point of Theorem 1, and why Theorem 2 supersedes it | present |
| numerator | `‖Σ̂ − Σ‖_F`, and the source says both norms may be replaced simultaneously by the operator norm or **any orthogonally invariant norm** | `N.toFun (B − A)` for `N : UnitarilyInvariantSeminorm 𝕜 E` |
| constant | `1` | `1` |
| production theorem | — | `yuWangSamworth_theorem1_uiNorm_le`, with `…_frobenius_le` and `…_opNorm_le` as specializations |

**The endpoint question is now resolved, and it resolves against the printed
statement.** This file previously recorded, as an open maintainer question,
whether the published article really prints `λ̂₀ = −∞` and `λ̂_{p+1} = +∞` or
whether the repository's transcription had swapped them. The published Biometrika
article was read directly on 2026-08-29. **It prints them as recorded.** With the
published rays `(−∞, λ̂_{s+1}] ∪ [λ̂_{r−1}, ∞)`, that makes `[λ̂₀, ∞) = ℝ` at
`r = 1` and `(−∞, λ̂_{p+1}] = ℝ` at `s = p`, so the infimum defining `δ` is `0`
and the hypothesis `δ > 0` is unsatisfiable at any block touching either end of
the spectrum — including the top-`d` block, the common case in statistics. The
reading that makes the theorem say what it evidently means is the opposite one,
`λ̂₀ = +∞` and `λ̂_{p+1} = −∞`, which makes the missing ray empty, exactly as
Theorem 2's `λ₀ = +∞`, `λ_{p+1} = −∞` do for the population gaps.

So this is a **third printed defect in the paper**, alongside Equation (4) and
Theorem 3's rank boundary, and it is milder than either: it degrades Theorem 1 to
vacuity at end blocks rather than making a false assertion, and Theorem 1 is the
baseline the paper is arguing *against*, not a contribution of it. Note also that
the paper's own Section 1 illustration is chosen at `r = 2`, `s = 4` in a
five-dimensional example, an interior block, where `δ = 0` for the honest reason
that `λ₄ = 20` lies in the ray `(−∞, λ̂₅] = (−∞, 21]` and not because of the
endpoint convention.

**Selecting Theorem 1 would therefore be a third `adapts` entry**, with its own
disclosed correction, not a `formalizes` one. That is a scope decision for the
maintainer, and it is deliberately not taken here. Two further mismatches would
also have to be closed first: the Lean statement is over `RCLike 𝕜` and over
arbitrary invariant subspaces rather than the paper's real contiguous blocks, and
`δ` is a hypothesis rather than the printed infimum. Neither is hard — a
paper-facing `theorem1_uiNorm` on `EuclideanSpace ℝ (Fin p)` modelled on
`theorem2_sinTheta`, plus a Challenge-side unitarily-invariant-norm interface —
but neither is done.

**HUMAN REVIEW ITEM.** The finding above is recorded here and in the two entry
metadata files' scope fields. It is *not* yet recorded as a gap row in
`dev/yu-wang-samworth-2015-full-source-census.json`, whose
`published_source_audit` currently notes only that the published article fixes
the preprint's wrong *indices* `λ̂_{s−1}`/`λ̂_{r+1}`, without observing that the
*values* it assigns to `λ̂₀` and `λ̂_{p+1}` are inverted. Adding that row is
census maintenance and belongs with a maintainer's review of this pass.

---

## Row A1 — Appendix Lemma A1

**NOT SELECTED.** Orthonormal compression cannot increase the Frobenius norm,
with equality for orthonormal rows. Lean:
`yuWangSamworth_lemma5_orthonormalColumns`,
`yuWangSamworth_lemma5_orthonormalRows` (preprint numbering in the names),
census status `compiled_generalized`. It is a proof tool of the paper rather
than one of its results, and neither entry compares it.

---

## Known source defects, none of which may be concealed

1. **Equation (4)** — the printed double-angle identity omits a square on
   `(2 − ‖v̂ − v‖²)`. Corrected identity `yuWangSamworth_equation4`; printed form
   refuted at `c = 3/5` by `yuWangSamworth_equation4_printed_counterexample`.
   Not selected in either entry; disclosed in both entries' `fidelity`.
2. **Theorem 3's rank-boundary convention** — as in rows T3-R-1 / T3-L-1.
   Selected, corrected, and disclosed; it is why the rectangular entry's source
   relationship is `adapts`.
3. **Theorem 1's sample endpoint conventions** — as in row T1. Not selected;
   disclosed in both entries' `status.scope`.
4. **Corollary 1's missing normalization** — as in rows C1-1 / C1-2. Selected,
   with the inherited hypothesis written out, refuted as printed by
   `corollary1_printed_unnormalized_counterexample`, and disclosed in the
   symmetric entry's Challenge docstring, `sources[].note` and `fidelity`. It
   does not change the source relationship, because the hypothesis is the
   paper's own.

---

## Mechanical status

Both entries pass the real Comparator, the independent NanoDa kernel and Lean's
own kernel, with axiom closure exactly `propext`, `Quot.sound`,
`Classical.choice`, and each Challenge's transitive import closure reaches
nothing in this repository. See `dev/palomar-readiness.md` for how to reproduce
that, and `registry/README.md` for what the status words do and do not mean.

`definition_names` is empty in both configurations, deliberately. Comparator
treats a name listed there as a *definition hole*: it checks only that the name,
type, universe levels and safety level agree, and it stops comparing the
definition's value. Every helper definition in these Challenges is fully
specified, so listing them would have weakened the comparison — with the lists
removed, Comparator requires the Challenge and Solution copies of `sinThetaDist`,
`SourceSingularGap` and the rest to agree as whole constants, bodies included.

---

## Authorship, checked before publishing it

Palomar publishes `project.authors`, so it was verified rather than inherited.
`Jon Crall` and `Edward Wang` are the two names, and both are supported by
repository evidence: `git log` in the authoritative repository attributes 1943
commits to `edward.wang@kitware.com` against 2908 to `jon.crall@kitware.com`
(plus 56 to a second address of Jon's), and commit `33f0c18b` — the maintainer's
own `formalization.yaml` v0.4 migration — records the decision in terms:
*"Authors are Jon Crall and Edward Wang, maintainer Jon Crall, per the
maintainer. AI models are disclosed under automation, never as authors."* That is
a maintainer adjudication supported by contribution evidence, not an inference
from the mathematical paper's authorship or from organizational association, and
it is retained.

**The file headers are provenance, not authorship, and that is now said out
loud.** Mathlib-style `Authors:` headers across `ForTauCeti/**`, `DavisKahan/**`
and `YuWangSamworth2015/**` name model identifiers (`Claude Opus 5`,
`OpenAI GPT-5.6 Thinking`) beside `Jon Crall`, while the two Palomar
Challenge/Solution pairs name `Jon Crall, Edward Wang`. Read alone that looks
inconsistent with "models are never authors".

It is not, and the fix is not to sweep it. The metadata's own `tool_setup` field
says provenance is recorded in two places — commit trailers and module headers —
so those 886 headers *are* the repository's declared per-declaration model
attribution, and rewriting them would delete a provenance record the metadata
points at. Nine of them, moreover, name a model with no human beside it, so a
mechanical strip would either leave an empty `Authors:` line or invent a human
attribution. What was missing was the sentence distinguishing the two registers,
and `automation.methods[].tool_setup` in both entry metadata files now carries
it: the headers are provenance including models; `project.authors` is authorship
and carries only people.

**HUMAN REVIEW ITEM, minor.** If the maintainer would rather the headers not use
the `Authors:` field for model provenance, the clean change is to move model
names to a separate header line across all three packages — a mechanical sweep,
but one that decides a repository-wide convention and needs the nine
human-less headers adjudicated. Not taken here.

---

## None of this was Palomar-specific convenience

Every library item this pass required is a paper-facing statement the
authoritative package should carry anyway — the source rank condition on Theorem
3, the exact `SourceSingularGap` denominator, the paired-singular-vector
equivalence, and the Section 1 illustration at the article's own block. That is
why they landed in `YuWangSamworth2015/` and not in a Palomar directory.
