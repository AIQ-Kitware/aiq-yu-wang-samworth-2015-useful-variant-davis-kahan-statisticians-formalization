/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.Rectangular.FrobeniusGram

/-!
# Yu--Wang--Samworth Appendix Lemma A1

Lemma A1 of the published Biometrika article; Lemma 5 of the 2014 preprint,
which is the numbering the module and declaration names here still spell.  They
are pinned by `comparator/*.json` and are deliberately not renamed; the
translation table lives in `dev/yu-wang-samworth-2015-full-source-census.json`
under gap `preprint-numbering-aliases`.

The paper states the result for matrices with orthonormal columns or rows.  The
basis-free formulation is a two-sided ideal estimate for the rectangular
Frobenius norm.  Orthonormal-column matrices have operator norm at most one;
for the row case the displayed recovery identity gives the reverse inequality.
This formulation is both source recognizable and reusable across dimensions.
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
/-- Lemma A1, orthonormal-column/contraction form:
`‖U⋆ A W‖_F ≤ ‖A‖_F`. -/
theorem yuWangSamworth_lemma5_columns
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : P →ₗ[𝕜] F) (W : Q →ₗ[𝕜] E)
    (hU : ‖U.toContinuousLinearMap‖ ≤ 1)
    (hW : ‖W.toContinuousLinearMap‖ ≤ 1) :
    RectangularUnitarilyInvariantSeminorm.frobenius
        (U.adjoint ∘ₗ A ∘ₗ W) ≤
      RectangularUnitarilyInvariantSeminorm.frobenius A := by
  have h := rectangularFrobenius_twoSided_comp_le U.adjoint A W
  have hUnorm :
      ‖U.adjoint.toContinuousLinearMap‖ = ‖U.toContinuousLinearMap‖ := by
    simp only [LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map]
  rw [hUnorm] at h
  have hF : 0 ≤ RectangularUnitarilyInvariantSeminorm.frobenius A :=
    (RectangularUnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜)).nonneg A
  calc
    RectangularUnitarilyInvariantSeminorm.frobenius (U.adjoint ∘ₗ A ∘ₗ W)
        ≤ ‖U.toContinuousLinearMap‖ *
            RectangularUnitarilyInvariantSeminorm.frobenius A *
              ‖W.toContinuousLinearMap‖ := h
    _ ≤ 1 * RectangularUnitarilyInvariantSeminorm.frobenius A *
          ‖W.toContinuousLinearMap‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hU hF) (norm_nonneg _)
    _ ≤ 1 * RectangularUnitarilyInvariantSeminorm.frobenius A * 1 := by
      exact mul_le_mul_of_nonneg_left hW (by simpa using hF)
    _ = RectangularUnitarilyInvariantSeminorm.frobenius A := by ring

/-- Lemma A1 with the source's orthonormal-column hypotheses expressed
coordinate-freely as pointwise norm preservation. -/
theorem yuWangSamworth_lemma5_isometricColumns
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : P →ₗ[𝕜] F) (W : Q →ₗ[𝕜] E)
    (hU : ∀ x : P, ‖U x‖ = ‖x‖)
    (hW : ∀ x : Q, ‖W x‖ = ‖x‖) :
    RectangularUnitarilyInvariantSeminorm.frobenius
        (U.adjoint ∘ₗ A ∘ₗ W) ≤
      RectangularUnitarilyInvariantSeminorm.frobenius A := by
  have hUnorm : ‖U.toContinuousLinearMap‖ ≤ 1 := by
    refine U.toContinuousLinearMap.opNorm_le_bound zero_le_one ?_
    intro x
    change ‖U x‖ ≤ 1 * ‖x‖
    calc
      ‖U x‖ = ‖x‖ := hU x
      _ ≤ 1 * ‖x‖ := by simp
  have hWnorm : ‖W.toContinuousLinearMap‖ ≤ 1 := by
    refine W.toContinuousLinearMap.opNorm_le_bound zero_le_one ?_
    intro x
    change ‖W x‖ ≤ 1 * ‖x‖
    calc
      ‖W x‖ = ‖x‖ := hW x
      _ ≤ 1 * ‖x‖ := by simp
  exact yuWangSamworth_lemma5_columns A U W hUnorm hWnorm

/-- Operator norm of a bundled linear isometry is at most one. -/
private theorem linearIsometry_opNorm_le_one
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (U : P →ₗᵢ[𝕜] Q) :
    ‖U.toLinearMap.toContinuousLinearMap‖ ≤ 1 := by
  refine U.toLinearMap.toContinuousLinearMap.opNorm_le_bound zero_le_one ?_
  intro x
  change ‖U x‖ ≤ 1 * ‖x‖
  rw [U.norm_map, one_mul]

/-- Lemma A1 in the literal orthonormal-column API: bundled linear isometries
encode matrices whose columns are orthonormal. -/
theorem yuWangSamworth_lemma5_orthonormalColumns
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : P →ₗᵢ[𝕜] F) (W : Q →ₗᵢ[𝕜] E) :
    RectangularUnitarilyInvariantSeminorm.frobenius
        (U.toLinearMap.adjoint ∘ₗ A ∘ₗ W.toLinearMap) ≤
      RectangularUnitarilyInvariantSeminorm.frobenius A := by
  exact yuWangSamworth_lemma5_columns A U.toLinearMap W.toLinearMap
    (linearIsometry_opNorm_le_one U) (linearIsometry_opNorm_le_one W)

/-- Lemma A1, orthonormal-row recovery form.  This lower-level theorem accepts
exactly the contraction and recovery facts used by the ideal proof. -/
theorem yuWangSamworth_lemma5_rows
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : P →ₗ[𝕜] F) (W : Q →ₗ[𝕜] E)
    (hU : ‖U.toContinuousLinearMap‖ ≤ 1)
    (hW : ‖W.toContinuousLinearMap‖ ≤ 1)
    (hrecover : U ∘ₗ (U.adjoint ∘ₗ A ∘ₗ W) ∘ₗ W.adjoint = A) :
    RectangularUnitarilyInvariantSeminorm.frobenius
        (U.adjoint ∘ₗ A ∘ₗ W) =
      RectangularUnitarilyInvariantSeminorm.frobenius A := by
  let C : Q →ₗ[𝕜] P := U.adjoint ∘ₗ A ∘ₗ W
  have hCdef : C = U.adjoint ∘ₗ A ∘ₗ W := rfl
  have hrecoverC : U ∘ₗ C ∘ₗ W.adjoint = A := by
    simpa only [hCdef] using hrecover
  have hC : 0 ≤ RectangularUnitarilyInvariantSeminorm.frobenius C :=
    (RectangularUnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜)).nonneg C
  have hWnorm :
      ‖W.adjoint.toContinuousLinearMap‖ = ‖W.toContinuousLinearMap‖ := by
    simp only [LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map]
  apply le_antisymm
  · simpa only [hCdef] using yuWangSamworth_lemma5_columns A U W hU hW
  · calc
      RectangularUnitarilyInvariantSeminorm.frobenius A =
          RectangularUnitarilyInvariantSeminorm.frobenius
            (U ∘ₗ C ∘ₗ W.adjoint) := by rw [hrecoverC]
      _ ≤ ‖U.toContinuousLinearMap‖ *
            RectangularUnitarilyInvariantSeminorm.frobenius C *
              ‖W.adjoint.toContinuousLinearMap‖ :=
        rectangularFrobenius_twoSided_comp_le U C W.adjoint
      _ = ‖U.toContinuousLinearMap‖ *
            RectangularUnitarilyInvariantSeminorm.frobenius C *
              ‖W.toContinuousLinearMap‖ := by rw [hWnorm]
      _ ≤ 1 * RectangularUnitarilyInvariantSeminorm.frobenius C *
            ‖W.toContinuousLinearMap‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hU hC) (norm_nonneg _)
      _ ≤ 1 * RectangularUnitarilyInvariantSeminorm.frobenius C * 1 := by
        exact mul_le_mul_of_nonneg_left hW (by simpa using hC)
      _ = RectangularUnitarilyInvariantSeminorm.frobenius C := by ring
      _ = RectangularUnitarilyInvariantSeminorm.frobenius
            (U.adjoint ∘ₗ A ∘ₗ W) := by rw [hCdef]

/-- Precomposition by the adjoint of a linear isometry preserves the
rectangular Frobenius norm.  This is the row-side analogue of
`RectangularUnitarilyInvariantSeminorm.frobenius_linearIsometry_comp`. -/
private theorem rectangularFrobenius_comp_adjoint_linearIsometry
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (W : E →ₗᵢ[𝕜] Q) :
    RectangularUnitarilyInvariantSeminorm.frobenius
        (A ∘ₗ W.toLinearMap.adjoint) =
      RectangularUnitarilyInvariantSeminorm.frobenius A := by
  calc
    RectangularUnitarilyInvariantSeminorm.frobenius
        (A ∘ₗ W.toLinearMap.adjoint) =
        RectangularUnitarilyInvariantSeminorm.frobenius
          (A ∘ₗ W.toLinearMap.adjoint).adjoint :=
      (rectangularFrobenius_adjoint
        (A ∘ₗ W.toLinearMap.adjoint)).symm
    _ = RectangularUnitarilyInvariantSeminorm.frobenius
          (W.toLinearMap ∘ₗ A.adjoint) := by
      rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
    _ = RectangularUnitarilyInvariantSeminorm.frobenius A.adjoint :=
      RectangularUnitarilyInvariantSeminorm.frobenius_linearIsometry_comp
        W A.adjoint
    _ = RectangularUnitarilyInvariantSeminorm.frobenius A :=
      rectangularFrobenius_adjoint A

/-- Lemma A1 in the literal orthonormal-row API.  Here `U` and `W` bundle the
transposed row maps, whose columns are orthonormal.

The proof factors into the two one-sided invariance laws rather than recovering
`A` through a fourfold composition.  Besides being shorter, this avoids costly
normalization of nested adjoints and compositions. -/
theorem yuWangSamworth_lemma5_orthonormalRows
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : F →ₗᵢ[𝕜] P) (W : E →ₗᵢ[𝕜] Q) :
    RectangularUnitarilyInvariantSeminorm.frobenius
        (U.toLinearMap ∘ₗ (A ∘ₗ W.toLinearMap.adjoint)) =
      RectangularUnitarilyInvariantSeminorm.frobenius A := by
  calc
    RectangularUnitarilyInvariantSeminorm.frobenius
        (U.toLinearMap ∘ₗ (A ∘ₗ W.toLinearMap.adjoint)) =
        RectangularUnitarilyInvariantSeminorm.frobenius
          (A ∘ₗ W.toLinearMap.adjoint) :=
      RectangularUnitarilyInvariantSeminorm.frobenius_linearIsometry_comp
        U (A ∘ₗ W.toLinearMap.adjoint)
    _ = RectangularUnitarilyInvariantSeminorm.frobenius A :=
      rectangularFrobenius_comp_adjoint_linearIsometry A W

end DavisKahanTheory
end YuWangSamworth2015
