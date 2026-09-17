/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Palomar.YWS.SolutionPrelude
import YuWangSamworth2015.Symmetric.Theorem2
import YuWangSamworth2015.Symmetric.Corollary1
import YuWangSamworth2015.Rectangular.SourceTheorem3

/-!
# Solution: Yu--Wang--Samworth population-gap perturbation theorems

`Palomar.YWS.SolutionPrelude` imports Mathlib alone and reproduces the complete
Challenge helper vocabulary before this module imports the substantive proof
development. The proof adapters below are the already-verified symmetric and
general-matrix adapters, composed into one standard root Solution.
-/

open TauCeti YuWangSamworth2015 YuWangSamworth2015.DavisKahanTheory

namespace YWSPalomar

open scoped InnerProductSpace BigOperators
open Module (finrank)

section Bridges

variable {p d : ℕ}

theorem frobeniusNorm_eq (A : Rp p →ₗ[ℝ] Rp p) :
    frobeniusNorm A = UnitarilyInvariantSeminorm.frobenius ℝ (Rp p) A :=
  (UnitarilyInvariantSeminorm.frobenius_apply ℝ (Rp p) A (finrank_Rp p)
    (EuclideanSpace.basisFun (Fin p) ℝ)).symm

theorem sinThetaDist_eq {V Vhat : Fin d → Rp p}
    (hV : Orthonormal ℝ V) (hVhat : Orthonormal ℝ Vhat) :
    sinThetaDist V Vhat =
      sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)) := by
  simp only [sinThetaDist]
  rw [← sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal hV hVhat]
  exact Real.sqrt_sq (sinThetaFrobenius_nonneg _ _)

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

namespace YWSRectangular

open scoped InnerProductSpace BigOperators
open Module (finrank)

section Bridges

variable {p q n d : ℕ}

theorem frobeniusNorm_eq (D : Rn q →ₗ[ℝ] Rn p) :
    frobeniusNorm D = RectangularUnitarilyInvariantSeminorm.frobenius.toFun D := by
  classical
  rw [RectangularUnitarilyInvariantSeminorm.frobenius_apply D
    ((EuclideanSpace.basisFun (Fin q) ℝ).reindex (finCongr (finrank_Rn q).symm))]
  refine congrArg Real.sqrt ?_
  refine (Fintype.sum_equiv (finCongr (finrank_Rn q)) _ _ fun i => ?_).symm
  simp

theorem sinThetaDist_eq {V Vhat : Fin d → Rn n}
    (hV : Orthonormal ℝ V) (hVhat : Orthonormal ℝ Vhat) :
    sinThetaDist V Vhat =
      sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)) := by
  simp only [sinThetaDist]
  rw [← sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal hV hVhat]
  exact Real.sqrt_sq (sinThetaFrobenius_nonneg _ _)

end Bridges

theorem isRightSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : Rn q →ₗ[ℝ] Rn p} {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A)) (V : Fin d → Rn q) :
    IsRightSingularBlock A hr hd V ↔
      Orthonormal ℝ V ∧
        ∃ U : Fin d → Rn p, Orthonormal ℝ U ∧
          ∀ i, A (V i) = A.singularValues (r + (i : ℕ)) • U i ∧
            LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i :=
  YuWangSamworth2015.isRightSingularBlock_iff_pairedSingularVectors
    (hr := hr) (hd := hd) hrank V

theorem isLeftSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : Rn q →ₗ[ℝ] Rn p} {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A)) (U : Fin d → Rn p) :
    IsLeftSingularBlock A hr hd U ↔
      Orthonormal ℝ U ∧
        ∃ V : Fin d → Rn q, Orthonormal ℝ V ∧
          ∀ i, LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i ∧
            A (V i) = A.singularValues (r + (i : ℕ)) • U i :=
  YuWangSamworth2015.isLeftSingularBlock_iff_pairedSingularVectors
    (hr := hr) (hd := hd) hrank U

theorem theorem3_rightSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    sinThetaDist V Vhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  rw [sinThetaDist_eq hV.1 hVhat.1, coefficient, opNorm, frobeniusNorm_eq]
  exact (YuWangSamworth2015.theorem3_rightSinTheta A Ahat hr hrank hd V Vhat hV hVhat
    Delta hDelta hgap).trans_eq (by ring)

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
  obtain ⟨O, hO, hbound⟩ := YuWangSamworth2015.theorem3_rightAlignedFrame A Ahat hr hrank hd
    V Vhat hV hVhat Delta hDelta hgap
  refine ⟨O, hO, hbound.trans_eq ?_⟩
  rw [coefficient, opNorm, frobeniusNorm_eq]
  ring

theorem theorem3_leftSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    sinThetaDist U Uhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  rw [sinThetaDist_eq hU.1 hUhat.1, coefficient, opNorm, frobeniusNorm_eq]
  exact (YuWangSamworth2015.theorem3_leftSinTheta A Ahat hr hrank hd U Uhat hU hUhat
    Delta hDelta hgap).trans_eq (by ring)

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
  obtain ⟨O, hO, hbound⟩ := YuWangSamworth2015.theorem3_leftAlignedFrame A Ahat hr hrank hd
    U Uhat hU hUhat Delta hDelta hgap
  refine ⟨O, hO, hbound.trans_eq ?_⟩
  rw [coefficient, opNorm, frobeniusNorm_eq]
  ring

end YWSRectangular
