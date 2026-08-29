/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.GroundedImports

/-!
# Yu--Wang--Samworth Theorem 1

The paper begins by recording the classical Davis--Kahan theorem in the
interval/exterior form used by statisticians.  The repository already proves a
strictly more general unitarily invariant norm statement.  This module gives
that result a source-facing name and then exposes the Frobenius and operator
norm specializations appearing in the paper.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Yu--Wang--Samworth Theorem 1 in its strongest paper-advertised form:
any unitarily invariant norm may replace the Frobenius norm. -/
theorem yuWangSamworth_theorem1_uiNorm_le
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    N (sinThetaMap U V) ≤ N (B - A) / δ := by
  rw [le_div_iff₀ hδ]
  simpa only [mul_comm] using
    sinTheta_perturbation_le N hA hB hU hV hδ hgap

/-- The Frobenius statement displayed as equation (1) in the paper. -/
theorem yuWangSamworth_theorem1_frobenius_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    sinThetaFrobenius U V ≤
      UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A) / δ := by
  rw [sinThetaFrobenius_eq]
  exact yuWangSamworth_theorem1_uiNorm_le
      (UnitarilyInvariantSeminorm.frobenius 𝕜 E)
      hA hB hU hV hδ hgap

/-- The operator-norm specialization explicitly mentioned after equation (1). -/
theorem yuWangSamworth_theorem1_opNorm_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    ‖(sinThetaMap U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ / δ := by
  rw [le_div_iff₀ hδ]
  simpa only [mul_comm] using
    opNorm_sinThetaMap_le_of_intervalGap hA hB hU hV hδ hgap

end DavisKahanTheory
end YuWangSamworth2015
