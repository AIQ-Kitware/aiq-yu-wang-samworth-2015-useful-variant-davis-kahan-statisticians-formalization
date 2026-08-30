/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Mathlib

/-!
# The Yu–Wang–Samworth population-gap sin-Θ theorem

## What this says

Let `T` be a symmetric operator on a `d`-dimensional real or complex inner product
space — in the statistical reading, a population covariance matrix `Σ` — and let
`S` be a symmetric perturbation of it, the sample covariance `Σ̂`. Fix a set `s`
of eigenvalue indices of `T`, so that `s` selects a block of the population
spectrum, and suppose every selected eigenvalue is separated from every unselected
one by at least `Δ > 0`.

Then the eigenvectors of `S` indexed by `s` are close to those of `T` indexed by
`s`, in the sense that the cross-block overlaps are small:

  `√(∑_{j ∈ s} ∑_{k ∉ s} |⟪uₖ, v̂ⱼ⟫|²)  ≤  2 √(∑ₖ ‖(S − T) uₖ‖²) / Δ`

where `uₖ` runs over an eigenvector basis of `T` and `v̂ⱼ` over one of `S`. The
left-hand side is the Frobenius norm of `sin Θ`, the matrix of sines of the
principal angles between the two selected eigenspaces; the right-hand side is a
Frobenius norm of the perturbation divided by the separation.

## Why this is the interesting statement

The classical Davis–Kahan theorem bounds the same quantity using the gap between
the selected population eigenvalues and the *sample* eigenvalues adjacent to them.
That gap is not observable and, worse, is exactly what a statistician is trying to
estimate; bounding it requires a further eigenvalue perturbation argument, and the
resulting bound degrades when the sample eigenvalues move.

Yu, Wang and Samworth's contribution is that the separation may be taken entirely
within the *population* spectrum, as `hgap` does here: every hypothesis is a
statement about `T`, and `S` enters only through `‖S − T‖`. That is what makes the
bound usable in statistics, and it is why the paper is cited across the spectral
methods literature — principal component analysis, spectral clustering, covariance
estimation, and network models where an adjacency or Laplacian matrix concentrates
around a population version.

The constant `2` here is the paper's, and the statement is at the paper's scope:
finite dimension, an arbitrary index set `s` rather than a leading block, and an
`RCLike` field so that the real and complex cases are one theorem.

## Source

Yi Yu, Tengyao Wang and Richard J. Samworth, *A useful variant of the Davis–Kahan
theorem for statisticians*, Biometrika 102(2), 2015, 315–323,
<https://doi.org/10.1093/biomet/asv008>. This is the first conclusion of their
Theorem 2.

The second conclusion of Theorem 2 — existence of an orthogonal matrix aligning
the sample eigenvector frame to the population one, with the printed `2^{3/2}`
constant — is also formalized in the accompanying development, and is not part of
this entry.

## Comparator note

The proof below is a deliberate statement-side placeholder. The proof lives in the
solution module, which supplies it from the ordinary library development.
-/

namespace YuWangSamworth2015

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- **Yu–Wang–Samworth 2015, Theorem 2, first conclusion.**

The Frobenius `sin Θ` distance between the eigenspaces of `T` and `S` selected by
an index set `s` is at most `2 ‖S − T‖_F / Δ`, where `Δ` separates the selected
eigenvalues of `T` from the unselected ones.

Every *separation* hypothesis constrains only the population operator `T`: `hgap`
is a statement about the spectrum of `T` alone, and no gap in the spectrum of `S`
is assumed. (`S` is of course assumed symmetric, and the conclusion is read
against its eigenvector basis; what is absent is any gap condition on its
spectrum.) That is the point of the variant. -/
theorem sqrt_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n))
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2)
      ≤ 2 * Real.sqrt
          (∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2) / Δ := by
  sorry

end YuWangSamworth2015
