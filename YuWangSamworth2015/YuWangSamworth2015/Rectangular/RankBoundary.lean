/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.Rectangular.Theorem4

/-!
# The rank-boundary defect in the printed singular-subspace theorem

Yu, Wang and Samworth's singular-subspace theorem (Theorem 3 of the published
Biometrika article, Theorem 4 of the 2014 preprint) is stated as

> Fix `1 ≤ r ≤ s ≤ rank(A)` and assume
> `min(σ_{r-1}² − σ_r², σ_s² − σ_{s+1}²) > 0`,
> where `σ_0² := ∞` and `σ_{rank(A)+1}² := −∞`.

The second convention is wrong.  Their proof passes to `AᵀA ∈ ℝ^{q×q}`, "with
eigenvalues `σ_1² ≥ … ≥ σ_q²`", and applies their Theorem 2, whose convention is
`λ_{q+1} := −∞` — at the *ambient* index `q`, not at `rank(A)`.  When
`rank(A) < q` the Gram operator still has a zero eigenspace, and the two
conventions disagree exactly there.

The consequence is not a harmless mismatch.  Taking `s = rank(A)` makes the
printed denominator `min(∞, ∞) = ∞`, so the printed bound asserts
`‖sin Θ(V̂, V)‖_F ≤ 0` — the sample and population right singular subspaces
coincide — while they can be orthogonal.  The refutation below exhibits that:
two rank-one orthogonal projections whose top right singular vectors are
perpendicular, with `r = s = 1 = rank(A)`.

Since Lean has no `∞` here, the printed denominator is encoded faithfully as
"larger than every real": the refuted claim is that the bound holds *for every*
positive `Δ` in the denominator.  It fails, because the angle is a fixed
positive number and the numerator is a fixed finite one.

**The repository's own theorem is not affected**, and is the natural repair:
`YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularSubspace_frame_le` takes
the gap as an intrinsic separation of the sorted spectrum of `A⋆A`, which counts
the zero eigenvalues.  So the corrected reading of the printed convention is
`σ_{q+1}² := −∞` for the right blocks (and `σ_{p+1}² := −∞` for the left), with
`σ_j := 0` for `min(p,q) < j`.  Under that reading the printed statement is true
and is exactly what this repository proves.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open Module (finrank)
open scoped InnerProductSpace RealInnerProductSpace BigOperators

section Projections

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
/-- The two-level operator with levels `0` and `1` is the orthogonal
projection. -/
theorem twoLevelOperator_zero_one (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    twoLevelOperator (𝕜 := 𝕜) 0 1 U = projection U := by
  ext x
  rw [twoLevelOperator_apply]
  simp

/-- **An orthogonal projection is its own right Gram operator.**  It is
self-adjoint and idempotent, so `P⋆P = P`; its squared singular values are
therefore its eigenvalues `1` and `0`. -/
theorem rightGram_projection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    rightGram (projection U) = projection U := by
  rw [rightGram, projection_adjoint]
  ext x
  change U.starProjection (U.starProjection x) = U.starProjection x
  exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)

omit [FiniteDimensional 𝕜 E] in
/-- The range of an orthogonal projection is the subspace it projects onto, so
its rank is that subspace's dimension. -/
theorem range_projection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.range (projection U) = U := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, rfl⟩
    exact U.starProjection_apply_mem x
  · exact ⟨x, Submodule.starProjection_eq_self_iff.mpr hx⟩

/-- **Orthogonal lines are at the maximal angle.**  `‖sin Θ‖_F = 1` for the
lines through two orthogonal unit vectors. -/
theorem sinThetaFrobenius_orthogonal_lines {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (horth : ⟪v, w⟫_𝕜 = 0) :
    sinThetaFrobenius (Submodule.span 𝕜 {v}) (Submodule.span 𝕜 {w}) = 1 := by
  have hon : ∀ {x : E}, ‖x‖ = 1 → Orthonormal 𝕜 (fun _ : Fin 1 => x) := by
    intro x hx
    rw [orthonormal_iff_ite]
    intro i k
    simp [Subsingleton.elim i k, inner_self_eq_norm_sq_to_K, hx]
  have hrangev : Submodule.span 𝕜 (Set.range fun _ : Fin 1 => v)
      = Submodule.span 𝕜 {v} := by rw [Set.range_const]
  have hrangew : Submodule.span 𝕜 (Set.range fun _ : Fin 1 => w)
      = Submodule.span 𝕜 {w} := by rw [Set.range_const]
  have hbridge := sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal
    (hon hv) (hon hw)
  rw [hrangev, hrangew] at hbridge
  have hmem : w ∈ (Submodule.span 𝕜 {v})ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr horth
  have hproj : (Submodule.span 𝕜 {v})ᗮ.starProjection w = w :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  have hsq : sinThetaFrobenius (Submodule.span 𝕜 {v}) (Submodule.span 𝕜 {w}) ^ 2 = 1 := by
    rw [hbridge, Fin.sum_univ_one, hproj, hw, one_pow]
  have hnn : (0 : ℝ) ≤ sinThetaFrobenius (Submodule.span 𝕜 {v}) (Submodule.span 𝕜 {w}) :=
    sinThetaFrobenius_nonneg _ _
  nlinarith [hsq, hnn]

end Projections

section Refutation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **The printed rank-boundary convention of the singular-subspace theorem is
false.**

Take `A` and `Â` to be the orthogonal projections onto two perpendicular lines.
Both have rank one, so `r = s = 1 = rank(A)` satisfies `1 ≤ r ≤ s ≤ rank(A)`;
both have squared singular values `1, 0`, so `v` and `w` are top right singular
vectors; and the printed hypothesis
`min(σ_0² − σ_1², σ_s² − σ_{s+1}²) > 0` holds under the printed conventions
`σ_0² := ∞`, `σ_{rank(A)+1}² := −∞`, which also make the denominator infinite.

Yet the two right singular subspaces are orthogonal, so `‖sin Θ‖_F = 1` — stated
as its own conclusion below — and no finite denominator, a fortiori not an
infinite one, makes the printed bound true.  The correct denominator here is
`σ_1² − σ_2² = 1 − 0 = 1`, which is what the intrinsic gap of `A⋆A` supplies and
what `singularBoundaryGap_of_rank_le` records in singular-value notation. -/
theorem yuWangSamworth_theorem3_printed_rankBoundary_refutation
    {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (horth : ⟪v, w⟫ = 0) :
    ∃ A Â : E →ₗ[ℝ] E,
      finrank ℝ (LinearMap.range A) = 1 ∧
      finrank ℝ (LinearMap.range Â) = 1 ∧
      rightGram A v = (1 : ℝ) • v ∧
      rightGram Â w = (1 : ℝ) • w ∧
      sinThetaFrobenius (Submodule.span ℝ {v}) (Submodule.span ℝ {w}) = 1 ∧
      ¬ ∀ Δ : ℝ, 0 < Δ →
          sinThetaFrobenius (Submodule.span ℝ {v}) (Submodule.span ℝ {w}) ≤
            2 * (2 * ‖A.toContinuousLinearMap‖ + ‖(Â - A).toContinuousLinearMap‖) *
              min (Real.sqrt 1 * ‖(Â - A).toContinuousLinearMap‖)
                (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  classical
  have hv0 : v ≠ 0 := by rw [← norm_ne_zero_iff, hv]; norm_num
  have hw0 : w ≠ 0 := by rw [← norm_ne_zero_iff, hw]; norm_num
  refine ⟨projection (Submodule.span ℝ {v}), projection (Submodule.span ℝ {w}),
    ?_, ?_, ?_, ?_, sinThetaFrobenius_orthogonal_lines hv hw horth, ?_⟩
  · rw [range_projection, finrank_span_singleton hv0]
  · rw [range_projection, finrank_span_singleton hw0]
  · rw [rightGram_projection, one_smul]
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self v)
  · rw [rightGram_projection, one_smul]
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self w)
  · -- The angle is `1`; the numerator is finite; so a large enough `Δ` breaks it.
    set A : E →ₗ[ℝ] E := projection (Submodule.span ℝ {v})
    set Â : E →ₗ[ℝ] E := projection (Submodule.span ℝ {w})
    set K : ℝ := 2 * ‖A.toContinuousLinearMap‖ + ‖(Â - A).toContinuousLinearMap‖ with hK
    set D : ℝ := ‖(Â - A).toContinuousLinearMap‖ with hD
    have hK0 : 0 ≤ K := by positivity
    have hD0 : 0 ≤ D := norm_nonneg _
    have hsin : sinThetaFrobenius (Submodule.span ℝ {v}) (Submodule.span ℝ {w}) = 1 :=
      sinThetaFrobenius_orthogonal_lines hv hw horth
    intro hall
    have hΔpos : (0 : ℝ) < 2 * K * D + 1 := by positivity
    have hbound := hall (2 * K * D + 1) hΔpos
    rw [hsin] at hbound
    have hmin : min (Real.sqrt 1 * D)
        (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) ≤ D := by
      refine (min_le_left _ _).trans_eq ?_
      rw [Real.sqrt_one, one_mul]
    have hnum : 2 * K * min (Real.sqrt 1 * D)
        (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) ≤ 2 * K * D := by
      have h2K : (0 : ℝ) ≤ 2 * K := by positivity
      exact mul_le_mul_of_nonneg_left hmin h2K
    have hfinal : 2 * K * min (Real.sqrt 1 * D)
        (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / (2 * K * D + 1)
          ≤ 2 * K * D / (2 * K * D + 1) :=
      div_le_div_of_nonneg_right hnum hΔpos.le
    have hlt : 2 * K * D / (2 * K * D + 1) < 1 := by
      rw [div_lt_one hΔpos]
      linarith
    linarith [hbound.trans hfinal]

/-- **The refutation in the paper's own setting**, real `2 × 2` matrices:
`A` and `Â` are the projections onto the two coordinate axes of `ℝ²`. -/
theorem yuWangSamworth_theorem3_printed_rankBoundary_refutation_euclidean :
    ∃ A Â : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      finrank ℝ (LinearMap.range A) = 1 ∧
      finrank ℝ (LinearMap.range Â) = 1 ∧
      rightGram A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
        = (1 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∧
      rightGram Â (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        = (1 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) ∧
      sinThetaFrobenius
          (Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)})
          (Submodule.span ℝ {EuclideanSpace.single (1 : Fin 2) (1 : ℝ)}) = 1 ∧
      ¬ ∀ Δ : ℝ, 0 < Δ →
          sinThetaFrobenius
              (Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)})
              (Submodule.span ℝ {EuclideanSpace.single (1 : Fin 2) (1 : ℝ)}) ≤
            2 * (2 * ‖A.toContinuousLinearMap‖ + ‖(Â - A).toContinuousLinearMap‖) *
              min (Real.sqrt 1 * ‖(Â - A).toContinuousLinearMap‖)
                (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ := by
  have h0 : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ = 1 := by
    simp
  have h1 : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ = 1 := by
    simp
  have horth : ⟪(EuclideanSpace.single (0 : Fin 2) (1 : ℝ)),
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))⟫ = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp
  exact yuWangSamworth_theorem3_printed_rankBoundary_refutation h0 h1 horth

end Refutation

end DavisKahanTheory
end YuWangSamworth2015
