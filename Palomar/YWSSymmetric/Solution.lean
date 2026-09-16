/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Palomar.YWSSymmetric.SolutionPrelude
import YuWangSamworth2015.Symmetric.Theorem2
import YuWangSamworth2015.Symmetric.Corollary1

/-!
# Solution: the Yu--Wang--Samworth population-gap theorems

The public vocabulary is imported from `SolutionPrelude`, which imports Mathlib
alone and is source-identical to the Challenge vocabulary prefix. This keeps the
exported constants stable for Comparator. The bridges below then connect those
constants to the substantive YWS development.
-/

open TauCeti YuWangSamworth2015 YuWangSamworth2015.DavisKahanTheory

namespace YWSPalomar

open scoped InnerProductSpace BigOperators
open Module (finrank)

section Bridges

variable {p d : ℕ}

/-- The challenge's Frobenius norm is the Frobenius unitarily invariant seminorm. -/
theorem frobeniusNorm_eq (A : Rp p →ₗ[ℝ] Rp p) :
    frobeniusNorm A = UnitarilyInvariantSeminorm.frobenius ℝ (Rp p) A :=
  (UnitarilyInvariantSeminorm.frobenius_apply ℝ (Rp p) A (finrank_Rp p)
    (EuclideanSpace.basisFun (Fin p) ℝ)).symm

/-- The challenge's `sin Θ` distance is the Frobenius sine distance between the
spans of the two frames. -/
theorem sinThetaDist_eq {V Vhat : Fin d → Rp p}
    (hV : Orthonormal ℝ V) (hVhat : Orthonormal ℝ Vhat) :
    sinThetaDist V Vhat =
      sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)) := by
  simp only [sinThetaDist]
  rw [← sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal hV hVhat]
  exact Real.sqrt_sq (sinThetaFrobenius_nonneg _ _)

/-- The challenge's numerator is the development's. -/
theorem perturbation_eq (E : Rp p →ₗ[ℝ] Rp p) :
    perturbation d E =
      min (Real.sqrt d * ‖LinearMap.toContinuousLinearMap E‖)
        (YuWangSamworth2015.frobeniusNorm E) := by
  rw [perturbation, frobeniusNorm_eq]

end Bridges

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
  rw [sinThetaDist_eq hV.1 hVhat.1, perturbation_eq]
  exact YuWangSamworth2015.theorem2_sinTheta Sigma SigmaHat hSigma hSigmaHat hr hs hd V Vhat
    hV hVhat _ rfl Delta hDelta hgap

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
  rw [perturbation_eq]
  exact YuWangSamworth2015.theorem2_alignedFrame Sigma SigmaHat hSigma hSigmaHat hr hs hd
    V Vhat hV hVhat Delta hDelta hgap

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
  have hproj : ‖(Submodule.span ℝ {vHat})ᗮ.starProjection v‖
      = ‖projection (Submodule.span ℝ {vHat})ᗮ v‖ := rfl
  rw [hproj, ← sinThetaFrobenius_span_singleton (W := Submodule.span ℝ {vHat}) hv]
  exact YuWangSamworth2015.corollary1_sinTheta Sigma SigmaHat hSigma hSigmaHat hj v vHat
    hv hvHat hSv hShv _ rfl Delta hDelta hgap

theorem corollary1_alignedVector {p j : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hj : j < p) (v vHat : Rp p) (hv : ‖v‖ = 1) (hvHat : ‖vHat‖ = 1)
    (hSv : Sigma v = hSigma.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • v)
    (hShv : SigmaHat vHat = hSigmaHat.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • vHat)
    (hsign : 0 ≤ inner ℝ vHat v)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma j j Delta) :
    ‖vHat - v‖ ≤ 2 * Real.sqrt 2 * opNorm (SigmaHat - Sigma) / Delta :=
  YuWangSamworth2015.corollary1_alignedVector Sigma SigmaHat hSigma hSigmaHat hj v vHat
    hv hvHat hSv hShv hsign Delta hDelta hgap

end YWSPalomar
