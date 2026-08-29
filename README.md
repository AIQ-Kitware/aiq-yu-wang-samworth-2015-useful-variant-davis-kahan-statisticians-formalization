# Yu–Wang–Samworth 2015: the population-gap sin-Θ theorem, in Lean 4

A machine-checked proof of the first conclusion of Theorem 2 of Yu, Wang and
Samworth, *A useful variant of the Davis–Kahan theorem for statisticians*,
Biometrika 102(2), 2015, 315–323, <https://doi.org/10.1093/biomet/asv008>.

## The result

For a symmetric operator `T` on a finite-dimensional real or complex inner product
space, a symmetric perturbation `S`, and a set `s` of eigenvalue indices whose
selected eigenvalues are separated from the unselected ones by at least `Δ > 0`,

  `√(∑_{j ∈ s} ∑_{k ∉ s} |⟪uₖ, v̂ⱼ⟫|²)  ≤  2 √(∑ₖ ‖(S − T) uₖ‖²) / Δ`

where `uₖ` is an eigenvector basis of `T` and `v̂ⱼ` one of `S`. The left side is
the Frobenius norm of `sin Θ`, the sines of the principal angles between the two
selected eigenspaces.

## Why it matters

The classical Davis–Kahan bound uses the gap between the population eigenvalues
and the *sample* eigenvalues next to them — a quantity the statistician does not
observe and is generally trying to estimate. Yu, Wang and Samworth's variant takes
the separation entirely inside the population spectrum: every hypothesis here
constrains `T` alone, and `S` enters only through `‖S − T‖`. That is what makes
the bound usable, and why the paper is cited across spectral methods — principal
component analysis, spectral clustering, covariance estimation, and network models
where an adjacency or Laplacian matrix concentrates around a population version.

The statement is at the paper's scope: finite dimension, an arbitrary index set
rather than a leading block, and an `RCLike` field so the real and complex cases
are one theorem. The constant `2` is the paper's.

## Fidelity

This entry formalizes the printed first conclusion of Theorem 2 with no added
hypothesis and no weakened conclusion.

Two divergences elsewhere in the same paper are recorded in the substantive
repository's census and are **not** part of this entry: printed Equation (4) does
not stand as written and is corrected there, and the paper's rank-boundary
convention required a correction. The second conclusion of Theorem 2 — existence
of an aligned orthogonal frame with the printed `2^{3/2}` constant — is formalized
in the substantive repository but is not compared here.

## Structure

`Challenge.lean` states the theorem against Mathlib alone, with a deliberate
statement-side hole. `Solution.lean` supplies the same declaration from the
substantive development, which is pinned as a Lake dependency. Comparator checks
that the two agree and that the proof uses only `propext`, `Quot.sound` and
`Classical.choice`.

The proof itself lives in the substantive repository, not here: it reduces the
Frobenius `sin Θ` overlap to a Sylvester-type separation estimate, and copying it
into a wrapper would create a second version to keep in step with the first.
