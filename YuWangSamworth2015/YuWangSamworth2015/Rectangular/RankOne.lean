/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.Rectangular.Theorem4

/-!
# Rank-one singular-vector corollaries

These are the direct singular-vector analogues of Corollary 1 (Corollary 3 in
the 2014 preprint).  They are not separately numbered in the paper, but are a
common forward-citation use of Theorem 3 (Theorem 4 in that preprint).  The
proof reuses the existing rank-one symmetric theorem on the right and left Gram
operators, then applies the exact Gram perturbation bound.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Right singular-vector corollary, in intrinsic operator-norm form. -/
theorem yuWangSamworth_rightSingularVector_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {σ σhat Δ : ℝ}
    (hAu : rightGram A u = ((σ ^ 2 : ℝ) : 𝕜) • u)
    (hÂv : rightGram Â v = ((σhat ^ 2 : ℝ) : 𝕜) • v)
    (hcorr : CorrespondingRightSingularBlock A Â
      (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}))
    (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum (rightGram A)
      (Submodule.span 𝕜 {u})ᗮ, Δ ≤ |σ ^ 2 - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤
        2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          ‖(Â - A).toContinuousLinearMap‖ / Δ := by
  obtain ⟨c, hc, hbase⟩ := yuWangSamworth_eigenvector_le
    (isSymmetric_rightGram A) (isSymmetric_rightGram Â)
    hu hv hAu hÂv
    (by simpa only [CorrespondingRightSingularBlock] using hcorr)
    hΔ hgap
  refine ⟨c, hc, hbase.trans ?_⟩
  have hgram := opNorm_rightGram_sub_le_paperCoefficient A Â
  calc
    2 * Real.sqrt 2 *
          ‖(rightGram Â - rightGram A).toContinuousLinearMap‖ / Δ
        ≤ 2 * Real.sqrt 2 *
            ((2 * ‖A.toContinuousLinearMap‖ +
              ‖(Â - A).toContinuousLinearMap‖) *
              ‖(Â - A).toContinuousLinearMap‖) / Δ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgram (by positivity)) hΔ.le
    _ = 2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          ‖(Â - A).toContinuousLinearMap‖ / Δ := by ring

/-- Left singular-vector corollary, in intrinsic operator-norm form. -/
theorem yuWangSamworth_leftSingularVector_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {u v : F}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {σ σhat Δ : ℝ}
    (hAu : leftGram A u = ((σ ^ 2 : ℝ) : 𝕜) • u)
    (hÂv : leftGram Â v = ((σhat ^ 2 : ℝ) : 𝕜) • v)
    (hcorr : CorrespondingLeftSingularBlock A Â
      (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}))
    (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum (leftGram A)
      (Submodule.span 𝕜 {u})ᗮ, Δ ≤ |σ ^ 2 - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤
        2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          ‖(Â - A).toContinuousLinearMap‖ / Δ := by
  obtain ⟨c, hc, hbase⟩ := yuWangSamworth_eigenvector_le
    (isSymmetric_leftGram A) (isSymmetric_leftGram Â)
    hu hv hAu hÂv
    (by simpa only [CorrespondingLeftSingularBlock] using hcorr)
    hΔ hgap
  refine ⟨c, hc, hbase.trans ?_⟩
  have hgram := opNorm_leftGram_sub_le_paperCoefficient A Â
  calc
    2 * Real.sqrt 2 *
          ‖(leftGram Â - leftGram A).toContinuousLinearMap‖ / Δ
        ≤ 2 * Real.sqrt 2 *
            ((2 * ‖A.toContinuousLinearMap‖ +
              ‖(Â - A).toContinuousLinearMap‖) *
              ‖(Â - A).toContinuousLinearMap‖) / Δ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgram (by positivity)) hΔ.le
    _ = 2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          ‖(Â - A).toContinuousLinearMap‖ / Δ := by ring

/-- Literal `σ₁(A)` form of the right singular-vector corollary. -/
theorem yuWangSamworth_rightSingularVector_le
    {A Â : E →ₗ[𝕜] F} {u v : E} [Nontrivial E]
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {σ σhat Δ : ℝ}
    (hAu : rightGram A u = ((σ ^ 2 : ℝ) : 𝕜) • u)
    (hÂv : rightGram Â v = ((σhat ^ 2 : ℝ) : 𝕜) • v)
    (hcorr : CorrespondingRightSingularBlock A Â
      (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}))
    (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum (rightGram A)
      (Submodule.span 𝕜 {u})ᗮ, Δ ≤ |σ ^ 2 - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 +
            ‖(Â - A).toContinuousLinearMap‖) *
          ‖(Â - A).toContinuousLinearMap‖ / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_rightSingularVector_opNormCoefficient_le
      hu hv hAu hÂv hcorr hΔ hgap

/-- Literal `σ₁(A)` form of the left singular-vector corollary. -/
theorem yuWangSamworth_leftSingularVector_le
    {A Â : E →ₗ[𝕜] F} {u v : F} [Nontrivial E]
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {σ σhat Δ : ℝ}
    (hAu : leftGram A u = ((σ ^ 2 : ℝ) : 𝕜) • u)
    (hÂv : leftGram Â v = ((σhat ^ 2 : ℝ) : 𝕜) • v)
    (hcorr : CorrespondingLeftSingularBlock A Â
      (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}))
    (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum (leftGram A)
      (Submodule.span 𝕜 {u})ᗮ, Δ ≤ |σ ^ 2 - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 +
            ‖(Â - A).toContinuousLinearMap‖) *
          ‖(Â - A).toContinuousLinearMap‖ / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_leftSingularVector_opNormCoefficient_le
      hu hv hAu hÂv hcorr hΔ hgap

end DavisKahanTheory
end YuWangSamworth2015
