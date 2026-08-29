/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.Rectangular.FrobeniusGram

/-!
# The Yu--Wang--Samworth singular-subspace theorem

Theorem 3 of the published Biometrika article; Theorem 4 of the 2014 preprint,
which is the numbering the declaration names in this module predate.

This module packages the rectangular theorem through the two Gram operators.
The proof is deliberately factored into three layers:

1. a generic transport theorem applies the already formalized symmetric
   Yu--Wang--Samworth theorem to any pair of self-adjoint Gram operators;
2. the right and left wrappers supply only their operator/Frobenius Gram
   perturbation estimates;
3. source-shaped corollaries rewrite the population operator norm as the top
   singular value `σ₁`.

Thus the right and left statements cannot drift apart, and the paper's
`min (sqrt d * ||Ahat-A||_op) ||Ahat-A||_F` numerator is assembled only once.

## What is proved here is the *corrected* theorem

Two deliberate departures from the printed statement, both recorded in
`dev/yu-wang-samworth-2015-full-source-census.json`.

* **The printed rank-boundary convention is false.**  Theorem 3 fixes
  `1 ≤ r ≤ s ≤ rank(A)` and declares `σ²_{rank(A)+1} := −∞`, which makes the
  denominator infinite at `s = rank(A)` and so asserts a zero angle between
  subspaces that can be orthogonal.  The gap hypothesis carried below is the
  *intrinsic* separation of the sorted spectrum of `A⋆A`, which counts the zero
  eigenvalues and is the correct reading (`σ²_{q+1} := −∞` at the ambient
  dimension, as the paper's own proof requires).  See
  `YuWangSamworth2015.Rectangular.RankBoundary` for the machine-checked
  refutation of the printed convention.
* **`CorrespondingRightSingularBlock` is narrower than the printed
  hypothesis.**  It pins both blocks to Mathlib's chosen Gram eigenbases,
  whereas the paper takes `V`, `V̂` to be any orthonormal frames of singular
  vectors, with no sample separation.  The theorems named `..._frame_le` below
  carry the printed hypothesis; the index-block forms are kept for callers who
  already hold that datum.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Ordered-index correspondence for right singular blocks, expressed through
squared singular values of the right Gram operators. -/
def CorrespondingRightSingularBlock (A Â : E →ₗ[𝕜] F)
    (U V : Submodule 𝕜 E) : Prop :=
  CorrespondingEigenblock (isSymmetric_rightGram A)
    (isSymmetric_rightGram Â) U V

/-- Ordered-index correspondence for left singular blocks. -/
def CorrespondingLeftSingularBlock (A Â : E →ₗ[𝕜] F)
    (U V : Submodule 𝕜 F) : Prop :=
  CorrespondingEigenblock (isSymmetric_leftGram A)
    (isSymmetric_leftGram Â) U V

/-- Population squared-singular-value gap for a right singular block. -/
def RightSingularInternalGap (A : E →ₗ[𝕜] F)
    (U : Submodule 𝕜 E) (Δ : ℝ) : Prop :=
  InternalGap (rightGram A) U Δ

/-- Population squared-singular-value gap for a left singular block. -/
def LeftSingularInternalGap (A : E →ₗ[𝕜] F)
    (U : Submodule 𝕜 F) (Δ : ℝ) : Prop :=
  InternalGap (leftGram A) U Δ

private theorem correspondingEigenblock_reduces_population
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H}
    (hcorr : CorrespondingEigenblock hG hĜ U V) : IsInvariant G U := by
  obtain ⟨n, hn, s, hU, -⟩ := hcorr
  rw [hU]
  exact reduces_spanIndices hG hn ↑s

private theorem correspondingEigenblock_reduces_perturbed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H}
    (hcorr : CorrespondingEigenblock hG hĜ U V) : IsInvariant Ĝ V := by
  obtain ⟨n, hn, s, -, hV⟩ := hcorr
  rw [hV]
  exact reduces_spanIndices hĜ hn ↑s

private theorem correspondingEigenblock_finrank_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H}
    (hcorr : CorrespondingEigenblock hG hĜ U V) :
    finrank 𝕜 U = finrank 𝕜 V := by
  obtain ⟨n, hn, s, hU, hV⟩ := hcorr
  rw [hU, hV, (hG.eigenvectorBasis hn).finrank_spanIndices,
    (hĜ.eigenvectorBasis hn).finrank_spanIndices]

/-- The minimum in Theorem 2 transports through a common Gram coefficient
without choosing an operator/Frobenius branch globally. -/
private theorem gram_min_le_scaled_min {d : ℕ}
    {gramOp gramFrob c perturbOp perturbFrob : ℝ}
    (hop : gramOp ≤ c * perturbOp)
    (hfrob : gramFrob ≤ c * perturbFrob) :
    min (Real.sqrt d * gramOp) gramFrob ≤
      c * min (Real.sqrt d * perturbOp) perturbFrob := by
  have hop' :
      Real.sqrt d * gramOp ≤ c * (Real.sqrt d * perturbOp) := by
    calc
      Real.sqrt d * gramOp ≤ Real.sqrt d * (c * perturbOp) :=
        mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg d)
      _ = c * (Real.sqrt d * perturbOp) := by ring
  rcases le_total (Real.sqrt d * perturbOp) perturbFrob with hmin | hmin
  · rw [min_eq_left hmin]
    exact (min_le_left _ _).trans hop'
  · rw [min_eq_right hmin]
    exact (min_le_right _ _).trans hfrob

/-- Generic Gram transport for the sine-distance part of Theorem 3. -/
private theorem yuWangSamworth_gram_sinTheta_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hcorr : CorrespondingEigenblock hG hĜ U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ c perturbOp perturbFrob : ℝ} (hΔ : 0 < Δ)
    (hgap : InternalGap G U Δ)
    (hop : ‖(Ĝ - G).toContinuousLinearMap‖ ≤ c * perturbOp)
    (hfrob : UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G) ≤
      c * perturbFrob) :
    sinThetaFrobenius U V ≤
      2 * c * min (Real.sqrt d * perturbOp) perturbFrob / Δ := by
  have hbase := yuWangSamworth_sinTheta_le hG hĜ
    (correspondingEigenblock_reduces_population hG hĜ hcorr)
    (correspondingEigenblock_reduces_perturbed hG hĜ hcorr)
    hcorr hrank hΔ hgap
  refine hbase.trans ?_
  have hmin := gram_min_le_scaled_min (d := d) hop hfrob
  calc
    2 * min (Real.sqrt d * ‖(Ĝ - G).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G)) / Δ
        ≤ 2 * (c * min (Real.sqrt d * perturbOp) perturbFrob) / Δ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (by norm_num)) hΔ.le
    _ = 2 * c * min (Real.sqrt d * perturbOp) perturbFrob / Δ := by ring

/-- Generic Gram transport for the aligned-frame part of Theorem 3. -/
private theorem yuWangSamworth_gram_alignedBasis_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hcorr : CorrespondingEigenblock hG hĜ U V)
    {d : ℕ} (hrankU : finrank 𝕜 U = d)
    {Δ c perturbOp perturbFrob : ℝ} (hΔ : 0 < Δ)
    (hgap : InternalGap G U Δ)
    (hop : ‖(Ĝ - G).toContinuousLinearMap‖ ≤ c * perturbOp)
    (hfrob : UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G) ≤
      c * perturbFrob) :
    ∃ (u v : Fin d → H), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 * c *
          min (Real.sqrt d * perturbOp) perturbFrob / Δ := by
  have hrankV : finrank 𝕜 V = d := by
    rw [← hrankU]
    exact (correspondingEigenblock_finrank_eq hG hĜ hcorr).symm
  obtain ⟨u, v, hu, hv, hspanU, hspanV, hbase⟩ :=
    yuWangSamworth_alignedBasis_le hG hĜ
      (correspondingEigenblock_reduces_population hG hĜ hcorr)
      (correspondingEigenblock_reduces_perturbed hG hĜ hcorr)
      hcorr hrankU hrankV hΔ hgap
  refine ⟨u, v, hu, hv, hspanU, hspanV, hbase.trans ?_⟩
  have hmin := gram_min_le_scaled_min (d := d) hop hfrob
  calc
    2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(Ĝ - G).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G)) / Δ
        ≤ 2 * Real.sqrt 2 *
            (c * min (Real.sqrt d * perturbOp) perturbFrob) / Δ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (by positivity)) hΔ.le
    _ = 2 * Real.sqrt 2 * c *
          min (Real.sqrt d * perturbOp) perturbFrob / Δ := by ring

/-- Theorem 3, right singular subspaces, index-block form with the intrinsic
operator-norm coefficient.

This is the **corrected** theorem, not the printed one: its gap hypothesis is the
intrinsic separation of the sorted spectrum of `A⋆A`, and the printed convention
`σ²_{rank(A)+1} := −∞` is false.  See the module header and
`YuWangSamworth2015.Rectangular.RankBoundary`. -/
theorem yuWangSamworth_rightSingularSubspace_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularInternalGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_sinTheta_le
    (isSymmetric_rightGram A) (isSymmetric_rightGram Â)
    (by simpa only [CorrespondingRightSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [RightSingularInternalGap] using hgap)
  · exact opNorm_rightGram_sub_le_paperCoefficient A Â
  · exact frobenius_rightGram_sub_le_paperCoefficient A Â

/-- Theorem 3, left singular subspaces, index-block form with the intrinsic
operator-norm coefficient.  Corrected, as on the right; see the module header. -/
theorem yuWangSamworth_leftSingularSubspace_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularInternalGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_sinTheta_le
    (isSymmetric_leftGram A) (isSymmetric_leftGram Â)
    (by simpa only [CorrespondingLeftSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [LeftSingularInternalGap] using hgap)
  · exact opNorm_leftGram_sub_le_paperCoefficient A Â
  · exact frobenius_leftGram_sub_le_paperCoefficient A Â

/-- Right-singular aligned-frame conclusion with the intrinsic coefficient. -/
theorem yuWangSamworth_rightSingularAlignedBasis_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularInternalGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_alignedBasis_le
    (isSymmetric_rightGram A) (isSymmetric_rightGram Â)
    (by simpa only [CorrespondingRightSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [RightSingularInternalGap] using hgap)
  · exact opNorm_rightGram_sub_le_paperCoefficient A Â
  · exact frobenius_rightGram_sub_le_paperCoefficient A Â

/-- Left-singular aligned-frame conclusion with the intrinsic coefficient. -/
theorem yuWangSamworth_leftSingularAlignedBasis_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularInternalGap A U Δ) :
    ∃ (u v : Fin d → F), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_alignedBasis_le
    (isSymmetric_leftGram A) (isSymmetric_leftGram Â)
    (by simpa only [CorrespondingLeftSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [LeftSingularInternalGap] using hgap)
  · exact opNorm_leftGram_sub_le_paperCoefficient A Â
  · exact frobenius_leftGram_sub_le_paperCoefficient A Â

/-- In positive finite domain dimension, the population operator norm is its
top singular value.

Paper-facing specialization of
`TauCeti.opNorm_eq_singularValues_zero`, which states the same identity with the
dimension supplied explicitly.  Kept only because the Yu--Wang--Samworth
statements are phrased with `[Nontrivial E]` rather than a named dimension; it
carries no proof of its own and should be inlined when this lane migrates. -/
theorem opNorm_eq_topSingularValue [Nontrivial E] (A : E →ₗ[𝕜] F) :
    ‖A.toContinuousLinearMap‖ = A.singularValues 0 :=
  TauCeti.opNorm_eq_singularValues_zero A rfl Module.finrank_pos

/-- Literal source-coefficient form of the right-singular sine bound. -/
theorem yuWangSamworth_rightSingularSubspace_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularInternalGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * A.singularValues 0 +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_rightSingularSubspace_opNormCoefficient_le
      hcorr hrank hΔ hgap

/-- Literal source-coefficient form of the left-singular sine bound. -/
theorem yuWangSamworth_leftSingularSubspace_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularInternalGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * A.singularValues 0 +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_leftSingularSubspace_opNormCoefficient_le
      hcorr hrank hΔ hgap

/-- Literal source-coefficient right aligned-frame conclusion. -/
theorem yuWangSamworth_rightSingularAlignedBasis_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularInternalGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_rightSingularAlignedBasis_opNormCoefficient_le
      hcorr hrank hΔ hgap

/-- Literal source-coefficient left aligned-frame conclusion. -/
theorem yuWangSamworth_leftSingularAlignedBasis_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularInternalGap A U Δ) :
    ∃ (u v : Fin d → F), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_leftSingularAlignedBasis_opNormCoefficient_le
      hcorr hrank hΔ hgap

/-! ## Theorem 3 at the source's generality

The blocks above are pinned to Mathlib's chosen Gram eigenbases, which — exactly
as in the symmetric case — is stronger than the printed hypothesis.  Yu, Wang
and Samworth take `V` and `V̂` to be *any* matrices with orthonormal columns
satisfying `A vⱼ = σⱼ uⱼ` and `Â vHatⱼ = σ̂ⱼ ûⱼ`, with no separation assumed among
the sample singular values; a repeated `σ̂` leaves `V̂` undetermined and the
theorem still quantifies over the choice.

Passing to the Gram operators — the paper's own route — `A vⱼ = σⱼ uⱼ` is
`A⋆A vⱼ = σⱼ² vⱼ`, so the printed hypothesis is an ordered eigenframe of
`rightGram A` at the indices of the sorted squared singular values.
-/

/-- **An ordered right singular frame**: an orthonormal family of right singular
vectors of `A` belonging to the squared singular values at the indices `e`.
Equivalently, an ordered eigenframe of the right Gram operator `A⋆A`. -/
def IsOrderedRightSingularFrame (A : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)
    {d : ℕ} (e : Fin d ↪ Fin n) (v : Fin d → E) : Prop :=
  IsOrderedEigenframe (isSymmetric_rightGram A) hn e v

/-- **An ordered left singular frame**, the same for `A A⋆`. -/
def IsOrderedLeftSingularFrame (A : E →ₗ[𝕜] F) {m : ℕ} (hm : finrank 𝕜 F = m)
    {d : ℕ} (e : Fin d ↪ Fin m) (u : Fin d → F) : Prop :=
  IsOrderedEigenframe (isSymmetric_leftGram A) hm e u

/-- The characteristic lemma for `IsOrderedRightSingularFrame`. -/
theorem isOrderedRightSingularFrame_iff {A : E →ₗ[𝕜] F} {n : ℕ}
    {hn : finrank 𝕜 E = n} {d : ℕ} {e : Fin d ↪ Fin n} {v : Fin d → E} :
    IsOrderedRightSingularFrame A hn e v ↔
      IsOrderedEigenframe (isSymmetric_rightGram A) hn e v :=
  Iff.rfl

/-- The characteristic lemma for `IsOrderedLeftSingularFrame`. -/
theorem isOrderedLeftSingularFrame_iff {A : E →ₗ[𝕜] F} {m : ℕ}
    {hm : finrank 𝕜 F = m} {d : ℕ} {e : Fin d ↪ Fin m} {u : Fin d → F} :
    IsOrderedLeftSingularFrame A hm e u ↔
      IsOrderedEigenframe (isSymmetric_leftGram A) hm e u :=
  Iff.rfl

/-- Generic Gram transport for the sine-distance part of Theorem 3, at frame
generality. -/
private theorem yuWangSamworth_gram_sinTheta_frame_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} {hG : G.IsSymmetric} {hĜ : Ĝ.IsSymmetric}
    {n d : ℕ} {hn : finrank 𝕜 H = n} {e : Fin d ↪ Fin n} {u v : Fin d → H}
    (hu : IsOrderedEigenframe hG hn e u) (hv : IsOrderedEigenframe hĜ hn e v)
    {Δ c perturbOp perturbFrob : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hG.eigenvalues hn (e i) - hG.eigenvalues hn k|)
    (hop : ‖(Ĝ - G).toContinuousLinearMap‖ ≤ c * perturbOp)
    (hfrob : UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G) ≤ c * perturbFrob) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ≤
      2 * c * min (Real.sqrt d * perturbOp) perturbFrob / Δ := by
  refine (yuWangSamworth_sinTheta_frame_le hu hv hΔ hgap).trans ?_
  have hmin := gram_min_le_scaled_min (d := d) hop hfrob
  calc
    2 * min (Real.sqrt d * ‖(Ĝ - G).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G)) / Δ
        ≤ 2 * (c * min (Real.sqrt d * perturbOp) perturbFrob) / Δ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (by norm_num)) hΔ.le
    _ = 2 * c * min (Real.sqrt d * perturbOp) perturbFrob / Δ := by ring

/-- Generic Gram transport for the aligned-frame part of Theorem 3, at frame
generality. -/
private theorem yuWangSamworth_gram_alignedBasis_frame_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} {hG : G.IsSymmetric} {hĜ : Ĝ.IsSymmetric}
    {n d : ℕ} {hn : finrank 𝕜 H = n} {e : Fin d ↪ Fin n} {u v : Fin d → H}
    (hu : IsOrderedEigenframe hG hn e u) (hv : IsOrderedEigenframe hĜ hn e v)
    {Δ c perturbOp perturbFrob : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hG.eigenvalues hn (e i) - hG.eigenvalues hn k|)
    (hop : ‖(Ĝ - G).toContinuousLinearMap‖ ≤ c * perturbOp)
    (hfrob : UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G) ≤ c * perturbFrob) :
    ∃ (u' v' : Fin d → H), Orthonormal 𝕜 u' ∧ Orthonormal 𝕜 v' ∧
      Submodule.span 𝕜 (Set.range u') = Submodule.span 𝕜 (Set.range u) ∧
      Submodule.span 𝕜 (Set.range v') = Submodule.span 𝕜 (Set.range v) ∧
      Real.sqrt (∑ i, ‖v' i - u' i‖ ^ 2) ≤
        2 * Real.sqrt 2 * c * min (Real.sqrt d * perturbOp) perturbFrob / Δ := by
  obtain ⟨u', v', hu', hv', hspanU, hspanV, hbase⟩ :=
    yuWangSamworth_alignedBasis_frame_le hu hv hΔ hgap
  refine ⟨u', v', hu', hv', hspanU, hspanV, hbase.trans ?_⟩
  have hmin := gram_min_le_scaled_min (d := d) hop hfrob
  calc
    2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(Ĝ - G).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius 𝕜 H (Ĝ - G)) / Δ
        ≤ 2 * Real.sqrt 2 *
            (c * min (Real.sqrt d * perturbOp) perturbFrob) / Δ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (by positivity)) hΔ.le
    _ = 2 * Real.sqrt 2 * c *
          min (Real.sqrt d * perturbOp) perturbFrob / Δ := by ring

/-- **Theorem 3, right singular subspaces, at the printed generality.**

`V`, `V̂` are arbitrary orthonormal right singular frames of `A`, `Â` at a common
index block, with a gap only on the population squared singular values.  The
denominator is the *intrinsic* gap of `A⋆A`, which — unlike the paper's printed
`σ_{rank(A)+1}² := −∞` convention — sees the zero part of the spectrum; see
`YuWangSamworth2015.Rectangular.RankBoundary` for why that matters. -/
theorem yuWangSamworth_rightSingularSubspace_frame_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {n d : ℕ} {hn : finrank 𝕜 E = n}
    {e : Fin d ↪ Fin n} {v vHat : Fin d → E}
    (hv : IsOrderedRightSingularFrame A hn e v)
    (hvHat : IsOrderedRightSingularFrame Â hn e vHat)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |(isSymmetric_rightGram A).eigenvalues hn (e i) -
            (isSymmetric_rightGram A).eigenvalues hn k|) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range v))
        (Submodule.span 𝕜 (Set.range vHat)) ≤
      2 * (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_gram_sinTheta_frame_le
      (isOrderedRightSingularFrame_iff.mp hv) (isOrderedRightSingularFrame_iff.mp hvHat)
      hΔ hgap (opNorm_rightGram_sub_le_paperCoefficient A Â)
      (frobenius_rightGram_sub_le_paperCoefficient A Â)

/-- **Theorem 3, left singular subspaces, at the printed generality.** -/
theorem yuWangSamworth_leftSingularSubspace_frame_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {m d : ℕ} {hm : finrank 𝕜 F = m}
    {e : Fin d ↪ Fin m} {u û : Fin d → F}
    (hu : IsOrderedLeftSingularFrame A hm e u)
    (hû : IsOrderedLeftSingularFrame Â hm e û)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin m), k ∉ Set.range (⇑e) →
      Δ ≤ |(isSymmetric_leftGram A).eigenvalues hm (e i) -
            (isSymmetric_leftGram A).eigenvalues hm k|) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range û)) ≤
      2 * (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_gram_sinTheta_frame_le
      (isOrderedLeftSingularFrame_iff.mp hu) (isOrderedLeftSingularFrame_iff.mp hû)
      hΔ hgap (opNorm_leftGram_sub_le_paperCoefficient A Â)
      (frobenius_leftGram_sub_le_paperCoefficient A Â)

/-- **Theorem 3, right aligned-frame conclusion, at the printed generality.** -/
theorem yuWangSamworth_rightSingularAlignedBasis_frame_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {n d : ℕ} {hn : finrank 𝕜 E = n}
    {e : Fin d ↪ Fin n} {v vHat : Fin d → E}
    (hv : IsOrderedRightSingularFrame A hn e v)
    (hvHat : IsOrderedRightSingularFrame Â hn e vHat)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |(isSymmetric_rightGram A).eigenvalues hn (e i) -
            (isSymmetric_rightGram A).eigenvalues hn k|) :
    ∃ (w ŵ : Fin d → E), Orthonormal 𝕜 w ∧ Orthonormal 𝕜 ŵ ∧
      Submodule.span 𝕜 (Set.range w) = Submodule.span 𝕜 (Set.range v) ∧
      Submodule.span 𝕜 (Set.range ŵ) = Submodule.span 𝕜 (Set.range vHat) ∧
      Real.sqrt (∑ i, ‖ŵ i - w i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_gram_alignedBasis_frame_le
      (isOrderedRightSingularFrame_iff.mp hv) (isOrderedRightSingularFrame_iff.mp hvHat)
      hΔ hgap (opNorm_rightGram_sub_le_paperCoefficient A Â)
      (frobenius_rightGram_sub_le_paperCoefficient A Â)

/-- **Theorem 3, left aligned-frame conclusion, at the printed generality.** -/
theorem yuWangSamworth_leftSingularAlignedBasis_frame_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {m d : ℕ} {hm : finrank 𝕜 F = m}
    {e : Fin d ↪ Fin m} {u û : Fin d → F}
    (hu : IsOrderedLeftSingularFrame A hm e u)
    (hû : IsOrderedLeftSingularFrame Â hm e û)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin m), k ∉ Set.range (⇑e) →
      Δ ≤ |(isSymmetric_leftGram A).eigenvalues hm (e i) -
            (isSymmetric_leftGram A).eigenvalues hm k|) :
    ∃ (w ŵ : Fin d → F), Orthonormal 𝕜 w ∧ Orthonormal 𝕜 ŵ ∧
      Submodule.span 𝕜 (Set.range w) = Submodule.span 𝕜 (Set.range u) ∧
      Submodule.span 𝕜 (Set.range ŵ) = Submodule.span 𝕜 (Set.range û) ∧
      Real.sqrt (∑ i, ‖ŵ i - w i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_gram_alignedBasis_frame_le
      (isOrderedLeftSingularFrame_iff.mp hu) (isOrderedLeftSingularFrame_iff.mp hû)
      hΔ hgap (opNorm_leftGram_sub_le_paperCoefficient A Â)
      (frobenius_leftGram_sub_le_paperCoefficient A Â)

end DavisKahanTheory
end YuWangSamworth2015
