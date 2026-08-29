/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.GroundedImports
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFrobenius

/-!
# Frobenius perturbation bounds for rectangular Gram operators

This module supplies the missing Frobenius branch in the rectangular
Yu--Wang--Samworth argument.  For `D = Â - A`, it proves

`‖Â⋆Â - A⋆A‖_F ≤ (‖Â‖ + ‖A‖) ‖D‖_F`

and the analogous left-Gram estimate.  The proof deliberately goes through the
basis-free Hilbert--Schmidt ideal law already available in the repository, then
uses the finite-dimensional Frobenius realization.  This avoids duplicating a
basis expansion and works uniformly over every `RCLike` scalar field.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators ENNReal

open DavisKahan.ExactSinTheta

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Every operator between finite-dimensional Hilbert spaces is
Hilbert--Schmidt in the paper's approximation-number model. -/
private theorem isPaperHilbertSchmidt_finite
    (A : E →L[𝕜] F) [CompleteSpace E] [CompleteSpace F] :
    IsPaperHilbertSchmidt A := by
  unfold IsPaperHilbertSchmidt
  rw [paperHilbertSchmidtEnergy_eq_ofReal_sum_sq_singularValues]
  exact ENNReal.ofReal_ne_top

/-- A rectangular Frobenius norm is invariant under adjoint. -/
theorem rectangularFrobenius_adjoint (A : E →ₗ[𝕜] F) :
    RectangularUnitarilyInvariantSeminorm.frobenius A.adjoint =
      RectangularUnitarilyInvariantSeminorm.frobenius A := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have h := paperHilbertSchmidtNorm_adjoint A.toContinuousLinearMap
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    paperHilbertSchmidtNorm_eq_rectangularFrobenius,
    paperHilbertSchmidtNorm_eq_rectangularFrobenius] at h
  exact h

/-- The Frobenius norm of a square product is bounded by the operator norm of
its left factor times the rectangular Frobenius norm of its right factor.

The intermediate Hilbert space may differ from the domain/codomain of the
square product; this is the cross-dimensional ideal estimate needed for Gram
operators. -/
theorem frobenius_comp_rectangular_le_opNorm_mul
    (C : F →ₗ[𝕜] E) (A : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius 𝕜 E (C ∘ₗ A) ≤
      ‖C.toContinuousLinearMap‖ *
        RectangularUnitarilyInvariantSeminorm.frobenius A := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have hA : IsPaperHilbertSchmidt A.toContinuousLinearMap :=
    isPaperHilbertSchmidt_finite A.toContinuousLinearMap
  have h := paperHilbertSchmidtNorm_comp_le
    C.toContinuousLinearMap hA (ContinuousLinearMap.id 𝕜 E)
  rw [ContinuousLinearMap.comp_id] at h
  have h' :
      paperHilbertSchmidtNorm
          (C.toContinuousLinearMap ∘L A.toContinuousLinearMap) ≤
        ‖C.toContinuousLinearMap‖ *
          paperHilbertSchmidtNorm A.toContinuousLinearMap :=
    h.trans (mul_le_of_le_one_right
      (mul_nonneg (norm_nonneg _)
        (paperHilbertSchmidtNorm_nonneg A.toContinuousLinearMap))
      ContinuousLinearMap.norm_id_le)
  rw [paperHilbertSchmidtNorm_eq_frobenius,
    paperHilbertSchmidtNorm_eq_rectangularFrobenius] at h'
  have hcomp :
      (C.toContinuousLinearMap ∘L A.toContinuousLinearMap).toLinearMap =
        C ∘ₗ A := by
    ext x
    rfl
  rwa [hcomp] at h'

/-- Two-sided rectangular Frobenius ideal inequality.  This is the reusable
operator-ideal statement behind both the Gram estimates and Appendix Lemma A1
(Lemma 5 in the 2014 preprint). -/
theorem rectangularFrobenius_twoSided_comp_le
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
      [FiniteDimensional 𝕜 G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [FiniteDimensional 𝕜 H]
    (L : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) (R : H →ₗ[𝕜] E) :
    RectangularUnitarilyInvariantSeminorm.frobenius (L ∘ₗ A ∘ₗ R) ≤
      ‖L.toContinuousLinearMap‖ *
        RectangularUnitarilyInvariantSeminorm.frobenius A *
          ‖R.toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  let : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  let : CompleteSpace H := FiniteDimensional.complete 𝕜 H
  have hA : IsPaperHilbertSchmidt A.toContinuousLinearMap :=
    isPaperHilbertSchmidt_finite A.toContinuousLinearMap
  have h := paperHilbertSchmidtNorm_comp_le
    L.toContinuousLinearMap hA R.toContinuousLinearMap
  rw [paperHilbertSchmidtNorm_eq_rectangularFrobenius,
    paperHilbertSchmidtNorm_eq_rectangularFrobenius] at h
  have hcomp :
      (L.toContinuousLinearMap ∘L A.toContinuousLinearMap ∘L
        R.toContinuousLinearMap).toLinearMap = L ∘ₗ A ∘ₗ R := by
    ext x
    rfl
  rwa [hcomp] at h

/-- Frobenius perturbation bound for the right Gram operator. -/
theorem frobenius_rightGram_sub_le
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius 𝕜 E
        (rightGram Â - rightGram A) ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        RectangularUnitarilyInvariantSeminorm.frobenius (Â - A) := by
  let D : E →ₗ[𝕜] F := Â - A
  have hidentity :
      rightGram Â - rightGram A =
        Â.adjoint ∘ₗ D + D.adjoint ∘ₗ A := by
    simpa only [D] using rightGram_sub_rightGram A Â
  rw [hidentity]
  refine (UnitarilyInvariantSeminorm.frobenius 𝕜 E).add_le _ _ |>.trans ?_
  have hleft :
      UnitarilyInvariantSeminorm.frobenius 𝕜 E (Â.adjoint ∘ₗ D) ≤
        ‖Â.toContinuousLinearMap‖ *
          RectangularUnitarilyInvariantSeminorm.frobenius D := by
    have h := frobenius_comp_rectangular_le_opNorm_mul Â.adjoint D
    simpa only [LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map] using h
  have hright :
      UnitarilyInvariantSeminorm.frobenius 𝕜 E (D.adjoint ∘ₗ A) ≤
        ‖A.toContinuousLinearMap‖ *
          RectangularUnitarilyInvariantSeminorm.frobenius D := by
    have h := frobenius_comp_rectangular_le_opNorm_mul A.adjoint D
    rw [← (UnitarilyInvariantSeminorm.frobenius 𝕜 E).apply_adjoint
      (D.adjoint ∘ₗ A), LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint]
    simpa only [LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map] using h
  calc
    UnitarilyInvariantSeminorm.frobenius 𝕜 E (Â.adjoint ∘ₗ D) +
          UnitarilyInvariantSeminorm.frobenius 𝕜 E (D.adjoint ∘ₗ A)
        ≤ ‖Â.toContinuousLinearMap‖ *
              RectangularUnitarilyInvariantSeminorm.frobenius D +
            ‖A.toContinuousLinearMap‖ *
              RectangularUnitarilyInvariantSeminorm.frobenius D :=
      add_le_add hleft hright
    _ = (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
          RectangularUnitarilyInvariantSeminorm.frobenius D := by ring

/-- Frobenius perturbation bound for the left Gram operator. -/
theorem frobenius_leftGram_sub_le
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius 𝕜 F
        (leftGram Â - leftGram A) ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        RectangularUnitarilyInvariantSeminorm.frobenius (Â - A) := by
  let D : E →ₗ[𝕜] F := Â - A
  have hidentity :
      leftGram Â - leftGram A =
        D ∘ₗ Â.adjoint + A ∘ₗ D.adjoint := by
    simpa only [D] using leftGram_sub_leftGram A Â
  rw [hidentity]
  refine (UnitarilyInvariantSeminorm.frobenius 𝕜 F).add_le _ _ |>.trans ?_
  have hleft :
      UnitarilyInvariantSeminorm.frobenius 𝕜 F (D ∘ₗ Â.adjoint) ≤
        ‖Â.toContinuousLinearMap‖ *
          RectangularUnitarilyInvariantSeminorm.frobenius D := by
    have h := frobenius_comp_rectangular_le_opNorm_mul
      (E := F) (F := E) Â D.adjoint
    rw [← (UnitarilyInvariantSeminorm.frobenius 𝕜 F).apply_adjoint
      (D ∘ₗ Â.adjoint), LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint]
    simpa only [rectangularFrobenius_adjoint] using h
  have hright :
      UnitarilyInvariantSeminorm.frobenius 𝕜 F (A ∘ₗ D.adjoint) ≤
        ‖A.toContinuousLinearMap‖ *
          RectangularUnitarilyInvariantSeminorm.frobenius D := by
    have h := frobenius_comp_rectangular_le_opNorm_mul
      (E := F) (F := E) A D.adjoint
    simpa only [rectangularFrobenius_adjoint] using h
  calc
    UnitarilyInvariantSeminorm.frobenius 𝕜 F (D ∘ₗ Â.adjoint) +
          UnitarilyInvariantSeminorm.frobenius 𝕜 F (A ∘ₗ D.adjoint)
        ≤ ‖Â.toContinuousLinearMap‖ *
              RectangularUnitarilyInvariantSeminorm.frobenius D +
            ‖A.toContinuousLinearMap‖ *
              RectangularUnitarilyInvariantSeminorm.frobenius D :=
      add_le_add hleft hright
    _ = (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
          RectangularUnitarilyInvariantSeminorm.frobenius D := by ring

omit [FiniteDimensional 𝕜 F] in
/-- The common Gram coefficient is bounded by the source-shaped
Yu--Wang--Samworth coefficient.  Keeping this arithmetic fact separate lets the
operator and Frobenius branches share exactly the same normalization step. -/
theorem sum_opNorm_le_paperCoefficient (A Â : E →ₗ[𝕜] F) :
    ‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖ ≤
      2 * ‖A.toContinuousLinearMap‖ +
        ‖(Â - A).toContinuousLinearMap‖ := by
  have hÂ :
      ‖Â.toContinuousLinearMap‖ ≤
        ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖ := by
    have h := norm_add_le A.toContinuousLinearMap
      (Â - A).toContinuousLinearMap
    have hadd :
        A.toContinuousLinearMap + (Â - A).toContinuousLinearMap =
          Â.toContinuousLinearMap := by
      ext x
      change A x + (Â x - A x) = Â x
      abel
    rwa [hadd] at h
  linarith

/-- Operator-norm perturbation bound with the exact coefficient displayed in
Yu--Wang--Samworth Theorem 3 (Theorem 4 in the 2014 preprint). -/
theorem opNorm_rightGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    ‖(rightGram Â - rightGram A).toContinuousLinearMap‖ ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  refine (opNorm_rightGram_sub_le A Â).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â) (norm_nonneg _)

/-- Left-Gram operator-norm counterpart with the exact paper coefficient. -/
theorem opNorm_leftGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    ‖(leftGram Â - leftGram A).toContinuousLinearMap‖ ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  refine (opNorm_leftGram_sub_le A Â).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â) (norm_nonneg _)

/-- Frobenius perturbation bound for the right Gram operator with the exact
coefficient displayed in Yu--Wang--Samworth Theorem 3 (Theorem 4 in the 2014
preprint). -/
theorem frobenius_rightGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius 𝕜 E
        (rightGram Â - rightGram A) ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        RectangularUnitarilyInvariantSeminorm.frobenius (Â - A) := by
  refine (frobenius_rightGram_sub_le A Â).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â)
    ((RectangularUnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜)).nonneg _)

/-- Left-Gram Frobenius counterpart with the exact paper coefficient. -/
theorem frobenius_leftGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius 𝕜 F
        (leftGram Â - leftGram A) ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        RectangularUnitarilyInvariantSeminorm.frobenius (Â - A) := by
  refine (frobenius_leftGram_sub_le A Â).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â)
    ((RectangularUnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜)).nonneg _)

end DavisKahanTheory
end YuWangSamworth2015
