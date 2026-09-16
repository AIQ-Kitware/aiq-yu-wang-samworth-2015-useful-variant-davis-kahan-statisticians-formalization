/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Mathlib

/-!
# Comparator-stable public vocabulary for the YWS symmetric Solution

This module intentionally imports Mathlib alone and reproduces the Challenge
vocabulary prefix exactly. `Solution.lean` imports this module before the full
proof development so Comparator sees the same constants on both sides.
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

end YWSPalomar
