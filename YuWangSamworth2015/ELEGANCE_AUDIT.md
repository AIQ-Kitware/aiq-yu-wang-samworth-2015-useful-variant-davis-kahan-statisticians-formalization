# In-place elegance audit

This audit was performed after the complete `YuWangSamworth2015` aggregate
built with warnings treated as errors.

## Changes made

1. **One Frobenius ideal foundation.**
   `rectangularFrobenius_twoSided_comp_le` now lives beside the Gram
   perturbation machinery. Appendix Lemma 5 consumes it instead of repeating
   the finite-dimensional Hilbert--Schmidt setup.
2. **Source-shaped Lemma 5 entry points.**
   Bundled linear isometries now represent matrices with orthonormal columns;
   bundled isometries for the transposed maps represent orthonormal rows. The
   lower-level contraction/recovery theorems remain available for reuse.
3. **No manual dimension witnesses.**
   The literal `sigma_1(A)` Theorem 4 and rank-one wrappers require
   `[Nontrivial E]` and derive positivity of `finrank` internally.
4. **Shared right/left proof core retained.**
   Both sides still pass through the same private Gram transport theorems; no
   constants or minimum estimates are duplicated.
5. **Source defect guarded.**
   The corrected equation (4) remains source-labeled, and a polynomial
   counterexample machine-checks that the printed unsquared formula is false.

## Intentionally deferred

* Literal contiguous-index `r..s` wrappers remain optional source-fidelity
  work; the intrinsic corresponding-block predicates are the cleaner theorem
  foundation.
* Reusable lemmas have not yet been migrated out of the paper package.
* The public theorem names have not been shortened before production
  integration, avoiding premature compatibility aliases.
