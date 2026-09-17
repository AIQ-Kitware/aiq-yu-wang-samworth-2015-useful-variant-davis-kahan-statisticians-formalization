/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Mathlib

/-!
# Yu-Wang-Samworth 2015 population-gap perturbation bounds

This single Challenge covers the paper-facing population-gap results of Yi Yu,
Tengyao Wang and Richard J. Samworth, *A useful variant of the Davis-Kahan
theorem for statisticians*, Biometrika **102** (2015) 315-323.

Theorem 2 and Corollary 1 concern eigenspaces of real symmetric matrices. Their
denominator uses only the population spectrum; no sample eigengap is assumed.
Corollary 1 writes out the unit normalization inherited from its `d = 1`
derivation from Theorem 2, because the standalone printed display omits it and
its second bound is false without it.

Theorem 3 extends the population-gap idea to right and left singular subspaces of
general real `p x q` matrices. Its printed convention
`sigma^2_(rank(A)+1) := -infinity` is false at the rank boundary. The declarations
below use the corrected ambient Gram-spectrum convention required by the paper's
own proof while retaining its separate block restriction `1 <= r <= s <= rank(A)`.
The paired-singular-vector equivalences record that the Gram formulation agrees
with the paper's formulation at the selected positive singular values.

Accordingly the merged entry is conservatively `adapts`: Theorem 2 is
source-exact, Corollary 1 is source-faithful with inherited normalization
explicit, and Theorem 3 is source-corrected.
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

/-! ## Compared theorem declarations -/

namespace YWSPalomar

open scoped InnerProductSpace BigOperators
open Module (finrank)

/-- Theorem 2, first conclusion: the population-gap Frobenius sine bound. -/
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

/-- Theorem 2, second conclusion: an aligned-frame bound against the supplied
population frame. -/
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
      Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
        2 * Real.sqrt 2 * perturbation d (SigmaHat - Sigma) / Delta := by
  sorry

/-- Corollary 1, first display, with the inherited unit normalization explicit. -/
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

/-- Corollary 1, second display, with normalization explicit and the printed
orientation condition. -/
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

namespace YWSRectangular

open scoped InnerProductSpace BigOperators
open Module (finrank)

/-- At source-selected positive singular values, the right Gram form is equivalent
to the paper's paired singular-vector equations. -/
theorem isRightSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : Rn q →ₗ[ℝ] Rn p} {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A)) (V : Fin d → Rn q) :
    IsRightSingularBlock A hr hd V ↔
      Orthonormal ℝ V ∧
        ∃ U : Fin d → Rn p, Orthonormal ℝ U ∧
          ∀ i, A (V i) = A.singularValues (r + (i : ℕ)) • U i ∧
            LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i := by
  sorry

/-- The left counterpart of the paired-singular-vector equivalence. -/
theorem isLeftSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : Rn q →ₗ[ℝ] Rn p} {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A)) (U : Fin d → Rn p) :
    IsLeftSingularBlock A hr hd U ↔
      Orthonormal ℝ U ∧
        ∃ V : Fin d → Rn q, Orthonormal ℝ V ∧
          ∀ i, LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i ∧
            A (V i) = A.singularValues (r + (i : ℕ)) • U i := by
  sorry

/-- Corrected Theorem 3, right singular subspaces, sine conclusion. -/
theorem theorem3_rightSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    sinThetaDist V Vhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  sorry

/-- Corrected Theorem 3, right singular subspaces, aligned-frame conclusion. -/
theorem theorem3_rightAlignedFrame {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
        2 * Real.sqrt 2 * coefficient d A (Ahat - A) / Delta := by
  sorry

/-- Corrected Theorem 3, left singular subspaces, sine conclusion. -/
theorem theorem3_leftSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    sinThetaDist U Uhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  sorry

/-- Corrected Theorem 3, left singular subspaces, aligned-frame conclusion. -/
theorem theorem3_leftAlignedFrame {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖(∑ j, O j i • Uhat j) - U i‖ ^ 2) ≤
        2 * Real.sqrt 2 * coefficient d A (Ahat - A) / Delta := by
  sorry

end YWSRectangular
