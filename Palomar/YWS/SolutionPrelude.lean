/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Mathlib

/-!
# Comparator-stable public vocabulary for the merged YWS Solution

This module intentionally imports Mathlib alone and reproduces the complete
helper-vocabulary prefix of `Challenge.lean` in the same order. The root
`Solution.lean` imports it before the substantive development so Comparator
sees identical helper constants on the Challenge and Solution sides.
-/

namespace YWSPalomar

open scoped InnerProductSpace BigOperators
open Module (finrank)

/-- The ambient space of the symmetric part of the paper. -/
abbrev Rp (p : ℕ) : Type := EuclideanSpace ℝ (Fin p)

/-- `finrank ℝ (Rp p) = p`, so `Fin p` indexes the sorted spectrum. -/
theorem finrank_Rp (p : ℕ) : finrank ℝ (Rp p) = p := by simp

/-- An orthonormal eigenvector block at the zero-based indices `r, ..., s`. -/
def IsEigenvectorBlock {p d r s : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V : Fin d → Rp p) : Prop :=
  Orthonormal ℝ V ∧
    ∀ i, Sigma (V i) =
      hSigma.eigenvalues (finrank_Rp p) (Fin.mk (r + (i : ℕ)) (by omega)) • V i

/-- The two population boundary-gap inequalities, with a missing endpoint
represented by a vacuous clause. -/
def PopulationBoundaryGap {p : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (∀ q j : Fin p, (q : ℕ) + 1 = r → (j : ℕ) = r →
      Delta ≤ hSigma.eigenvalues (finrank_Rp p) q
                - hSigma.eigenvalues (finrank_Rp p) j) ∧
    (∀ j q : Fin p, (j : ℕ) = s → (q : ℕ) = s + 1 →
      Delta ≤ hSigma.eigenvalues (finrank_Rp p) j
                - hSigma.eigenvalues (finrank_Rp p) q)

/-- The paper's population denominator exactly, except for the full-space block
where both source boundary gaps are infinite and every positive finite `Delta`
is an admissible surrogate because the sine distance is zero. -/
def SourcePopulationGap {p : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (r = 0 ∧ s + 1 = p) ∨
    (PopulationBoundaryGap Sigma hSigma r s Delta ∧
      ∀ delta : ℝ, PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta)

/-- Frobenius norm over the standard basis. -/
noncomputable def frobeniusNorm {p : ℕ} (A : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  Real.sqrt (∑ i, ‖A (EuclideanSpace.basisFun (Fin p) ℝ i)‖ ^ 2)

/-- Frobenius `sin Theta` distance between the spans of two orthonormal frames. -/
noncomputable def sinThetaDist {p d : ℕ} (V Vhat : Fin d → Rp p) : ℝ :=
  Real.sqrt (∑ j, ‖(Submodule.span ℝ (Set.range V))ᗮ.starProjection (Vhat j)‖ ^ 2)

/-- Operator norm of an endomorphism. -/
noncomputable abbrev opNorm {p : ℕ} (A : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  ‖LinearMap.toContinuousLinearMap A‖

/-- Theorem 2's numerator `min(sqrt(d)||E||_op, ||E||_F)`. -/
noncomputable abbrev perturbation {p : ℕ} (d : ℕ) (E : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  min (Real.sqrt d * opNorm E) (frobeniusNorm E)

end YWSPalomar

namespace YWSRectangular

open scoped InnerProductSpace BigOperators
open Module (finrank)

/-- Real `n`-dimensional Euclidean space; a `p x q` matrix is `Rn q →ₗ[ℝ] Rn p`. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- `finrank ℝ (Rn n) = n`. -/
theorem finrank_Rn (n : ℕ) : finrank ℝ (Rn n) = n := by simp

/-- A right singular block in Gram form. -/
def IsRightSingularBlock {p q d r s : ℕ} (A : Rn q →ₗ[ℝ] Rn p)
    (_hr : r ≤ s) (_hd : d = s - r + 1) (V : Fin d → Rn q) : Prop :=
  Orthonormal ℝ V ∧
    ∀ i, (LinearMap.adjoint A ∘ₗ A) (V i) = A.singularValues (r + (i : ℕ)) ^ 2 • V i

/-- A left singular block in Gram form. -/
def IsLeftSingularBlock {p q d r s : ℕ} (A : Rn q →ₗ[ℝ] Rn p)
    (_hr : r ≤ s) (_hd : d = s - r + 1) (U : Fin d → Rn p) : Prop :=
  Orthonormal ℝ U ∧
    ∀ i, (A ∘ₗ LinearMap.adjoint A) (U i) = A.singularValues (r + (i : ℕ)) ^ 2 • U i

/-- Squared population singular boundary-gap inequalities, read in the ambient
right (`q`) or left (`p`) Gram spectrum. -/
def SingularBoundaryGap {p q : ℕ} (n : ℕ) (A : Rn q →ₗ[ℝ] Rn p) (r s : ℕ)
    (Delta : ℝ) : Prop :=
  (∀ a b : Fin n, (a : ℕ) + 1 = r → (b : ℕ) = r →
      Delta ≤ A.singularValues (a : ℕ) ^ 2 - A.singularValues (b : ℕ) ^ 2) ∧
    (∀ a b : Fin n, (a : ℕ) = s → (b : ℕ) = s + 1 →
      Delta ≤ A.singularValues (a : ℕ) ^ 2 - A.singularValues (b : ℕ) ^ 2)

/-- The corrected exact singular-value denominator. The full-ambient-block branch
records the source's two infinite exterior boundaries without identifying a
finite `Delta` with infinity. -/
def SourceSingularGap {p q : ℕ} (n : ℕ) (A : Rn q →ₗ[ℝ] Rn p) (r s : ℕ)
    (Delta : ℝ) : Prop :=
  (r = 0 ∧ s + 1 = n) ∨
    (SingularBoundaryGap n A r s Delta ∧
      ∀ delta : ℝ, SingularBoundaryGap n A r s delta → delta ≤ Delta)

/-- Frobenius norm of a rectangular map over the standard basis of its domain. -/
noncomputable def frobeniusNorm {p q : ℕ} (D : Rn q →ₗ[ℝ] Rn p) : ℝ :=
  Real.sqrt (∑ i, ‖D (EuclideanSpace.basisFun (Fin q) ℝ i)‖ ^ 2)

/-- Operator norm. -/
noncomputable abbrev opNorm {p q : ℕ} (D : Rn q →ₗ[ℝ] Rn p) : ℝ :=
  ‖LinearMap.toContinuousLinearMap D‖

/-- Frobenius `sin Theta` distance between two orthonormal frames. -/
noncomputable def sinThetaDist {n d : ℕ} (V Vhat : Fin d → Rn n) : ℝ :=
  Real.sqrt (∑ j, ‖(Submodule.span ℝ (Set.range V))ᗮ.starProjection (Vhat j)‖ ^ 2)

/-- Theorem 3's numerator without the leading constant `2`. -/
noncomputable abbrev coefficient {p q : ℕ} (d : ℕ) (A D : Rn q →ₗ[ℝ] Rn p) : ℝ :=
  (2 * A.singularValues 0 + opNorm D) * min (Real.sqrt d * opNorm D) (frobeniusNorm D)

end YWSRectangular
