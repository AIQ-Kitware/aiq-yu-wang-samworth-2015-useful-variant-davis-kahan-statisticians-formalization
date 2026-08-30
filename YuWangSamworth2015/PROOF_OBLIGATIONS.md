# Proof obligations

Numbering below is the **published** Biometrika numbering, checked against the
article on 2026-08-13: Theorem 1, Theorem 2, Corollary 1, Theorem 3, Lemma A1,
equations (1)–(4), appendix equations (A1)–(A8).  The 2014 arXiv preprint shares
one counter and numbers the last three Corollary 3, Theorem 4 and Lemma 5, which
is what many Lean declaration names in this library still spell.  The census
records the translation table under gap `preprint-numbering-aliases`; the names
are not being changed because `comparator/*.json` pins some of them.

## Numbered paper results

Every numbered result has a theorem surface.  They are not all at the same
distance from the printed page — Theorem 2 and Corollary 1 are source-exact,
Theorem 3 is a documented correction, and Theorem 1 and Lemma A1 are more general
than printed:

* Theorem 1, in unitarily invariant, Frobenius and operator-norm form — more
  general than printed, and with an intrinsic separation rather than the printed
  `δ`, whose endpoint conventions are inverted (census gap
  `theorem1-sample-endpoint-conventions`);
* Theorem 2, both conclusions, for **arbitrary ordered eigenframes** — the
  paper's `V̂` is any orthonormal family with `Σ̂ v̂ⱼ = λ̂ⱼ v̂ⱼ`, with no sample
  eigengap, so a repeated sample eigenvalue leaves it undetermined and the
  theorem must quantify over the choice;
* Corollary 1, both displays, including the literal real sign-aligned bound
  `‖v̂ − v‖ ≤ 2^{3/2} ‖Σ̂ − Σ‖_op / Δⱼ` under `v̂ᵀv ≥ 0`;
* Theorem 3, right and left, in the corrected form (see below);
* Lemma A1, both halves.

The canonical paper-facing Theorem 2 surface is now
`theorem2_sinTheta` / `theorem2_alignedFrame`.  It specializes to real operators
on `Real^p` and displays the source arithmetic directly as `r ≤ s`, `s < p`, and
`d = s - r + 1`.  `IsEigenvectorBlock` means exactly orthonormal columns plus the
ordered eigenvector equations.  `SourcePopulationGap` makes `Delta` the exact
source denominator: outside the full-space endpoint case it is the greatest
real satisfying `PopulationBoundaryGap`, hence the printed finite minimum; the
full-space branch represents the source's `+infinity` convention.  The semantic
alignment dictionary expands both gap predicates so neither a weaker population
gap nor any sample separation can be hidden.  The sine conclusion names
`sinThetaNorm` explicitly and ties it to its Lean realization by an equality
hypothesis.  Both conclusions write the perturbation term directly as
`frobeniusNorm (SigmaHat - Sigma)`, a reducible application-level abbreviation
for the existing Frobenius seminorm.  The aligned conclusion returns
`O : Matrix (Fin d) (Fin d) Real` in the orthogonal group, comparing the
supplied `Vhat O` against the supplied `V`.

The older source-indexed `RCLike` wrappers remain as implementation-oriented
generalizations.  There the same block arithmetic is normalized to
`r + d = s + 1` and `s + 1 ≤ n`, and the endpoint conventions `λ_0 = +∞` and
`λ_{p+1} = −∞` are modelled by vacuous quantification.  The bridge constrains
only the population spectrum, so `λ̂_s = λ̂_{s+1}` remains admissible.

## Additional completed source material

* the sharper residual-numerator forms of Theorem 2 that the paper says its
  proof establishes — `‖sin Θ‖_F ≤ ‖V̂Λ − ΣV̂‖_F / Δ` and the aligned form with
  the factor `2^{1/2}`;
* corrected equation (4), with the printed polynomial refuted;
* the refutation of Theorem 3's printed rank-boundary convention, and the
  corrected boundary condition in singular-value notation;
* direct right and left rank-one singular-vector corollaries;
* exact operator/Frobenius minimum and aligned-frame constants;
* all three Section 2 sharpness constructions, including the *published*
  middle-block one, over the full parameter range `0 < ε < 3` — maximal whenever
  `2d < p`, since at `ε = 3` the perturbed level `2+ε` merges with `5` and its
  multiplicity becomes `p−d` rather than `d`;
* the Section 1 numerical illustration that Theorem 1's separation `δ` can
  vanish, together with the operator-level population gap at the same block;
* the deterministic content of the Section 3 diagnosis: the Weyl recovery of a
  mixed gap, the fact that on the event it needs it reproduces Theorem 2's
  constant, and a witness that the event can fail.

## Source defects recorded

Two printed statements in this paper are false as printed, and both are machine
checked in both directions.

1. **Equation (4).** The printed right-hand side omits a square on
   `2 − ‖v̂ − v‖²`.  Corrected identity and counterexample in
   `Symmetric/AngleIdentity.lean`.
2. **Theorem 3's convention `σ²_{rank(A)+1} := −∞`.** Found 2026-08-13; no
   erratum located.  Taking `s = rank(A)` makes the printed denominator
   infinite, so the printed bound asserts that the sample and population right
   singular subspaces coincide — and they can be orthogonal.  Refuted in
   `Rectangular/RankBoundary.lean`.  The repair is the convention the paper's
   own proof uses: `σ²_{q+1} := −∞` at the **ambient** dimension, with
   `σ_j := 0` for `min(p,q) < j`.  That is exactly the intrinsic gap of `A⋆A`
   that this library's theorems carry, so no new theorem was needed.

## Remaining non-numbered source-fidelity work

* equation (1) — the `r = s = j` display of **Theorem 1** — has no wrapper with
  a literal index and its *mixed* gap
  `min(|λ̂_{j-1} − λⱼ|, |λ̂_{j+1} − λⱼ|)`.  The boundary-gap machinery does not
  reach it: it converts a boundary condition on one sorted spectrum into an
  intrinsic separation of that same spectrum, whereas equation (1) compares the
  population eigenvalue against the **sample** spectrum, and with `λ̂ⱼ` repeated
  the mixed exterior gap is zero.  A literal wrapper therefore needs a
  simplicity hypothesis the source does not print at that display.  Theorem 1
  itself is proved here in a strictly more general unitarily invariant interval
  form;
* migrate reusable results from this paper package into canonical foundation modules.

Neither is a gap in a numbered result.

## Build guard

`YuWangSamworth2015` **is** a default build target: it joined `defaultTargets`
on 2026-08-02, so `lake build` compiles everything here and a regression cannot
land unnoticed.  The library also carries `warningAsError` under the Mathlib
standard linter set, matching the option set Tau Ceti's own `lean_lib` applies.

## Census state (2026-08-13)

`dev/yu-wang-samworth-2015-full-source-census.json`: **24 of 24 rows proved in
the default build.**  The two rows that were short on 2026-08-13 are closed:
the Section 1 numerical illustration is formalized, and the Section 3 row —
exposition, and still not proof debt — now carries the compiled deterministic
core of its claims.  Two gaps were retired with them, `section1-toy-example`
and `published-sharpness-example`.

Closing the published sharpness example needed new mathematics rather than new
bookkeeping.  Its block sits in the *middle* of both spectra, so the
branch-selection hypothesis cannot come from any "leading `d` eigenvectors"
argument, and the missing foundation was the position of an arbitrary
eigenvalue level set inside Mathlib's sorted eigenbasis:
`LinearMap.IsSymmetric.eigenvalues_level_eq_Ico` (every level set is the
contiguous index range `[m, m+d)`), `TauCeti.card_filter_lt_eigenvalues_basisDiagonal`
(for a diagonal operator `m` is read off the coefficient list), and
`YuWangSamworth2015.correspondingEigenblock_eigenvalueLevel`, of which the earlier
top-eigenspace constructor is now the case `m = 0`.

The census was rekeyed to the published numbering on 2026-08-13 and three of its
judgements were corrected in the process.  `YWS-T2-sinTheta`,
`YWS-T2-alignedBasis` and `YWS-C1-rankone` had been marked `compiled_exact`
while the only statement carrying them assumed `CorrespondingEigenblock`, which
is strictly stronger than the paper's hypothesis at a degenerate **sample**
eigenvalue — the exact case removing the sample eigengap exists to cover.
`YWS-T3-right` and `YWS-T3-left` are now `compiled_corrected` rather than
`compiled_exact`, because the printed convention they were claimed to match is
false.  A census that reports `compiled_exact` for a statement it has not
compared clause by clause with the printed one is worth less than no census.

## Source-shape work of 2026-08-13

Four things moved, none of them a new numbered result.

1. **The source's indexing.**  `YuWangSamworth2015.consecutiveEmb` and
   `YuWangSamworth2015.OrderedBlockBoundaryGap` state the paper's `r..s` block and its
   two-sided boundary gap; `OrderedBlockBoundaryGap.indexGap` propagates it to
   the intrinsic separation the general theorems consume, and antitonicity of
   the sorted spectrum is the only mathematics in it.  Theorem 2's two
   conclusions, both residual forms, Corollary 1 and Theorem 3 on both sides now
   have statements in that shape.
2. **The alignment.**  `YuWangSamworth2015.frameComp hv O` is the matrix product `V̂Ô`, and
   the aligned conclusions exhibit `Ô`.  A bundled linear isometry equivalence
   of the coordinate space is exactly an element of `O(d)`;
   `YuWangSamworth2015.adjoint_comp_self_eq_id` spells that out as `ÔᵀÔ = I`, and over `ℝ`
   `YuWangSamworth2015.frameAlignMatrix` produces the matrix itself, with
   `frameAlignMatrix_mem_orthogonalGroup` placing it in
   `Matrix.orthogonalGroup (Fin d) ℝ`.
3. **The published sharpness range.**  `ε < 1` was an artifact of the first
   proof.  The construction needs `2 < 2 + ε < 5`, and every lemma now carries
   `0 < ε < 3`; `card_middleSharpnessSample_level_three` records the breakpoint,
   which bites exactly when `2d < p` — at `p = 2d` there is no leading level `5`
   and the constraint is vacuous, so `ε < 3` is sufficient everywhere and
   necessary only for `2d < p`.
   The headline theorem also concludes the achieved distance `√(2d)`, so its
   statement carries the sharpness claim its docstring makes.
4. **The sample-degeneracy witness.**
   `yuWangSamworth_corollary1_scalarSample` instantiates Corollary 1 at
   `Σ = diag(1, 0)`, `Σ̂ = I/2`: every unit vector of the plane is an admissible
   `v̂₁` and the corollary bounds each of them.  A statement pinning `v̂` to a
   chosen eigenbasis of `Σ̂` would cover exactly one.
