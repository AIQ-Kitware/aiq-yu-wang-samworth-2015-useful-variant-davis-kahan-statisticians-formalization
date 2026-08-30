/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Mathlib

/-!
# Yu–Wang–Samworth 2015: the population-gap perturbation theorems

Yi Yu, Tengyao Wang and Richard J. Samworth, *A useful variant of the Davis–Kahan
theorem for statisticians*, Biometrika **102** (2015) 315–323,
<https://doi.org/10.1093/biomet/asv008>. Published numbering throughout.

## The problem

Let `Σ` be a real symmetric `p × p` matrix — a population covariance — and `Σ̂` a
symmetric estimate of it. Fix a block `r, …, s` of eigenvalue indices, in
nonincreasing order, and let `V` and `V̂` hold orthonormal eigenvectors of `Σ` and
`Σ̂` at those indices. How far can the sample eigenspace be from the population
one?

The classical Davis–Kahan answer divides the perturbation by a separation between
the population eigenvalues *in* the block and the sample eigenvalues *outside* it.
That quantity mixes the two spectra, so it is random, unobserved, and can vanish
even when the population spectrum is well separated. The paper's own illustration,
in its §1, is `Σ = diag(50, 40, 30, 20, 10)` and `Σ̂ = diag(54, 37, 32, 23, 21)` at
the eigenvectors for the second, third and fourth largest eigenvalues — `r = 2`,
`s = 4` in the paper's one-based indexing, which is the Lean block `r = 1`,
`s = 3` below. There `λ₄ = 20` lies in the exterior ray `(−∞, λ̂₅] = (−∞, 21]`, so
the classical separation is `0` and Theorem 1 says nothing, while the population
gap `min(λ₁ − λ₂, λ₄ − λ₅) = 10` is as large as one likes.

## What Yu, Wang and Samworth prove

The separation may be taken **entirely inside the population spectrum**. Writing
`Δ = min(λ_{r−1} − λ_r, λ_s − λ_{s+1})` and `E = Σ̂ − Σ`,

* `‖sin Θ(V̂, V)‖_F ≤ 2 min(√d ‖E‖_op, ‖E‖_F) / Δ`, and
* some `Ô ∈ O(d)` has `‖V̂Ô − V‖_F ≤ 2^{3/2} min(√d ‖E‖_op, ‖E‖_F) / Δ`,

with `d = s − r + 1`. Every *separation* hypothesis constrains `Σ` alone: `Δ` is
built from the population spectrum only, and `Σ̂` enters the bound solely through
`E`. (`Σ̂` is of course assumed symmetric, and `V̂` is assumed to be one of its
eigenframes at the block; what is absent is any gap or separation condition on
its spectrum.) That is what makes the bound usable in statistics, and it is why
the paper is cited across spectral methods — principal component analysis,
spectral clustering, covariance estimation, and network models where an adjacency
or Laplacian matrix concentrates around a population version.

**No sample eigengap is assumed, and this is not a technicality.** `Σ̂` may have a
repeated eigenvalue at the block, in which case `V̂` is not determined; the
theorem quantifies over *every* admissible orthonormal sample eigenframe. A
formulation that pinned `V̂` to one chosen eigenbasis would be a different and
weaker statement. For `Σ = diag(1, 0)` and `Σ̂ = I/2` every unit vector of the
plane is an admissible sample eigenvector, and Corollary 1 below bounds the angle
for each of them.

`Δ` here is the paper's denominator itself, not merely a positive number below
it: outside the full-space endpoint case `SourcePopulationGap` identifies it as
the greatest real satisfying the two boundary inequalities, which is exactly the
printed minimum. The one exception is the full block `r = 1`, `s = p`, where the
paper's conventions make both exterior gaps `+∞`; see that definition's
docstring for what is claimed there.

## Contents

Theorem 2, both printed conclusions, and Corollary 1, both printed displays. The
Yu–Wang–Samworth paper also contains Theorem 1 (the classical baseline it starts
from), Theorem 3 (the rectangular singular-subspace extension) and Appendix Lemma
A1; those are formalized in the accompanying development and are not compared
here.

Two divergences elsewhere in the paper are recorded in the substantive
development and are not part of this entry: printed Equation (4) omits a square
and is refuted as printed, and Theorem 3's printed rank-boundary convention
`σ²_{rank(A)+1} := −∞` is false and is corrected there.

## Note on the proofs

Every proof below is a deliberate statement-side hole. The solution module
supplies the same declarations from the ordinary development.
-/

namespace YWSPalomar

open scoped InnerProductSpace BigOperators
open Module (finrank)

/-- The ambient space of the paper: real `p`-dimensional Euclidean space, on which
a real symmetric `p × p` matrix acts. -/
abbrev Rp (p : ℕ) : Type := EuclideanSpace ℝ (Fin p)

/-- `finrank ℝ (Rp p) = p`, so `Fin p` indexes the sorted spectrum. -/
theorem finrank_Rp (p : ℕ) : finrank ℝ (Rp p) = p := by simp

/-- **An eigenvector block at the indices `r, …, s`.**

`V` has orthonormal columns and its `i`-th column is an eigenvector of `Sigma` for
the `(r + i)`-th eigenvalue in nonincreasing order. Lean indices are zero-based,
so this is the paper's block `r, …, s` with one subtracted from its indices.

Nothing is assumed about multiplicity: at a repeated eigenvalue every orthonormal
choice inside the eigenspace satisfies this. -/
def IsEigenvectorBlock {p d r s : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V : Fin d → Rp p) : Prop :=
  Orthonormal ℝ V ∧
    ∀ i, Sigma (V i) =
      hSigma.eigenvalues (finrank_Rp p) (Fin.mk (r + (i : ℕ)) (by omega)) • V i

/-- **The population boundary gap of the block `r, …, s`.**

`Delta ≤ λ_{r−1} − λ_r` and `Delta ≤ λ_s − λ_{s+1}`. When the block starts at the
top or ends at the bottom the corresponding clause is vacuous, which is the
paper's `λ_0 = +∞` and `λ_{p+1} = −∞` written without extended reals.

Only the spectrum of `Sigma` occurs. There is no sample eigengap. -/
def PopulationBoundaryGap {p : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (∀ q j : Fin p, (q : ℕ) + 1 = r → (j : ℕ) = r →
      Delta ≤ hSigma.eigenvalues (finrank_Rp p) q
                - hSigma.eigenvalues (finrank_Rp p) j) ∧
    (∀ j q : Fin p, (j : ℕ) = s → (q : ℕ) = s + 1 →
      Delta ≤ hSigma.eigenvalues (finrank_Rp p) j
                - hSigma.eigenvalues (finrank_Rp p) q)

/-- **The paper's denominator `Δ = min(λ_{r−1} − λ_r, λ_s − λ_{s+1})`.**

Outside the full-block case the second disjunct says that `Delta` is the
*greatest* real satisfying both boundary inequalities, which is exactly that
minimum with a missing endpoint omitted. There `Delta` **is** the paper's
denominator, not merely a lower bound for it.

The first disjunct is the full block `r = 0`, `s + 1 = p`. There are then no
exterior eigenvalues at all, the paper's conventions make both exterior gaps
`+∞`, and no greatest finite real satisfies the two vacuous clauses — so the
second disjunct cannot be met and a separate branch is needed. In that case the
selected frame spans the whole space and `‖sin Θ‖_F = 0`, so every positive
finite `Delta` is an admissible surrogate for the infinite source denominator and
the theorems below hold for each of them. This branch does not assert that a
finite `Delta` is the paper's `+∞`. -/
def SourcePopulationGap {p : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (r = 0 ∧ s + 1 = p) ∨
    (PopulationBoundaryGap Sigma hSigma r s Delta ∧
      ∀ delta : ℝ, PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta)

/-- **The Frobenius norm** `‖A‖_F = √(∑ᵢ ‖A eᵢ‖²)` over the standard basis. -/
noncomputable def frobeniusNorm {p : ℕ} (A : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  Real.sqrt (∑ i, ‖A (EuclideanSpace.basisFun (Fin p) ℝ i)‖ ^ 2)

/-- **The Frobenius `sin Θ` distance between the spans of two orthonormal frames**,

`‖sin Θ(V̂, V)‖_F = √(∑ⱼ ‖P_{span(V)^⊥} V̂ⱼ‖²)`,

the sines of the principal angles between the two blocks, measured by projecting
each sample frame vector off the population block. -/
noncomputable def sinThetaDist {p d : ℕ} (V Vhat : Fin d → Rp p) : ℝ :=
  Real.sqrt (∑ j, ‖(Submodule.span ℝ (Set.range V))ᗮ.starProjection (Vhat j)‖ ^ 2)

/-- The operator norm of a linear endomorphism of `Rp p`. -/
noncomputable abbrev opNorm {p : ℕ} (A : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  ‖LinearMap.toContinuousLinearMap A‖

/-- The paper's numerator `min(√d ‖E‖_op, ‖E‖_F)`. -/
noncomputable abbrev perturbation {p : ℕ} (d : ℕ) (E : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  min (Real.sqrt d * opNorm E) (frobeniusNorm E)

/-- **Theorem 2, first conclusion.**

`‖sin Θ(V̂, V)‖_F ≤ 2 min(√d ‖E‖_op, ‖E‖_F) / Δ`, with `Δ` the population
boundary gap of the block and no hypothesis whatever on the spectrum of `Σ̂`. -/
theorem theorem2_sinTheta {p d r s : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rp p)
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    sinThetaDist V Vhat ≤ 2 * perturbation d (SigmaHat - Sigma) / Delta := by
  sorry

/-- **Theorem 2, second conclusion.**

There is an orthogonal `Ô ∈ O(d)` with
`‖V̂Ô − V‖_F ≤ 2^{3/2} min(√d ‖E‖_op, ‖E‖_F) / Δ`. The `i`-th column of `V̂Ô` is
`∑ⱼ Ô_{ji} V̂ⱼ`, and it is compared against the supplied population frame `V`. -/
theorem theorem2_alignedFrame {p d r s : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rp p)
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
        2 * Real.sqrt 2 * perturbation d (SigmaHat - Sigma) / Delta := by
  sorry

/-- **Corollary 1, first display.**

The rank-one case `r = s = j`: for unit eigenvectors `v` of `Σ` and `v̂` of `Σ̂` at
the `j`-th eigenvalue, `sin Θ(v̂, v) ≤ 2 ‖E‖_op / Δ_j`. The sine is the length of
the component of `v` orthogonal to `v̂`. `v̂` is arbitrary: at a repeated sample
eigenvalue the bound holds for every admissible choice. -/
theorem corollary1_sinTheta {p j : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hj : j < p) (v vHat : Rp p) (hv : ‖v‖ = 1) (hvHat : ‖vHat‖ = 1)
    (hSv : Sigma v = hSigma.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • v)
    (hShv : SigmaHat vHat = hSigmaHat.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • vHat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma j j Delta) :
    ‖(Submodule.span ℝ {vHat})ᗮ.starProjection v‖ ≤
      2 * opNorm (SigmaHat - Sigma) / Delta := by
  sorry

/-- **Corollary 1, second display.**

After orienting `v̂` so that `v̂ᵀv ≥ 0`,
`‖v̂ − v‖ ≤ 2^{3/2} ‖E‖_op / Δ_j`. -/
theorem corollary1_alignedVector {p j : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hj : j < p) (v vHat : Rp p) (hv : ‖v‖ = 1) (hvHat : ‖vHat‖ = 1)
    (hSv : Sigma v = hSigma.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • v)
    (hShv : SigmaHat vHat = hSigmaHat.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • vHat)
    (hsign : 0 ≤ inner ℝ vHat v)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma j j Delta) :
    ‖vHat - v‖ ≤ 2 * Real.sqrt 2 * opNorm (SigmaHat - Sigma) / Delta := by
  sorry

end YWSPalomar
