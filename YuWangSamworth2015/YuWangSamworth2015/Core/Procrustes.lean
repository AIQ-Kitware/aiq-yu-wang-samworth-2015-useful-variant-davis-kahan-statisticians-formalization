/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import YuWangSamworth2015.Core.Statistics

/-! # The one-sided Procrustes alignment `V̂ Ô`

Yu, Wang and Samworth's second conclusion compares the *sample* frame, rotated
inside its own span, against the population frame left where it is:

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`, with `Ô ∈ O(d)`.

`YuWangSamworth2015.exists_aligned_orthonormalBasis` records the weaker existential in which
*both* frames are replaced by new ones spanning the same subspaces.  That is
enough to derive the numerical bound and nothing else: a reader cannot tell from
it that the population frame is untouched, nor recover the `d × d` alignment.
The alignment is not lost, only hidden — `sum_sq_norm_aligned_le_sinThetaSq`
rotates `v` by the polar unitary of the overlap operator and leaves `u` alone —
so this file names it.

`frameComp hv O` is the paper's matrix product `V̂ Ô`: its `i`-th column is
`∑ⱼ Ôⱼᵢ v̂ⱼ`.  `O` is a bundled `EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜
(Fin d)`, which over `ℝ` is exactly an element of `O(d)`; `adjoint_comp_self_eq_id`
spells that out as `Ôᵀ Ô = I`.

## Main results

* `YuWangSamworth2015.frameComp`: the rotated frame `V̂ Ô`, with its expansion, orthonormality
  and span.
* `YuWangSamworth2015.exists_unitary_sum_sq_norm_frameComp_sub_le`: the Procrustes step
  `‖V̂ Ô − V‖²_F ≤ 2 ‖sin Θ‖²_F` with the alignment exhibited.
* `YuWangSamworth2015.yuWangSamworth_alignedFrame_le` and
  `YuWangSamworth2015.yuWangSamworth_alignedFrame_le_residual`: Theorem 2's second
  conclusion and its sharper residual form, both with an explicit `Ô`.
* `YuWangSamworth2015.frameAlignMatrix` and
  `YuWangSamworth2015.yuWangSamworth_alignedFrame_real_le`: over `ℝ`, the same conclusion
  with `Ô` an honest element of `Matrix.orthogonalGroup (Fin d) ℝ` and the
  columns of `V̂Ô` written as the matrix products `∑ⱼ Ôⱼᵢ v̂ⱼ`.
-/

public section

namespace YuWangSamworth2015
open TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {d : ℕ}

/-- **`Ôᵀ Ô = I`.**  A bundled linear isometry equivalence of the coordinate space
is an orthogonal (unitary) matrix; this is that statement in the form a reader of
the paper expects, so that `Ô ∈ O(d)` needs no interpretation. -/
theorem adjoint_comp_self_eq_id
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    LinearMap.adjoint (O.toLinearEquiv.toLinearMap) ∘ₗ O.toLinearEquiv.toLinearMap =
      LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  refine ext_inner_left 𝕜 fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.id_apply]
  exact O.inner_map_map y x

/-- **The rotated frame `V̂ Ô`.**  Column `i` of the product of the frame `v` with
the coordinate isometry `O`; see `frameComp_apply` for the expansion. -/
noncomputable def frameComp {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) : Fin d → E :=
  fun i => familyIsometry hv (O (EuclideanSpace.single i 1))

omit [FiniteDimensional 𝕜 E] in
/-- **The characteristic lemma.**  `(V̂ Ô)ᵢ = ∑ⱼ Ôⱼᵢ v̂ⱼ`: the definition is a
matrix product, written through the coordinate isometry. -/
theorem frameComp_apply {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) (i : Fin d) :
    frameComp hv O i = ∑ j, O (EuclideanSpace.single i 1) j • v j := by
  rw [frameComp, familyIsometry_apply]

omit [FiniteDimensional 𝕜 E] in
/-- The rotated frame is again orthonormal: both `O` and the coordinate isometry
of `v` preserve inner products. -/
theorem orthonormal_frameComp {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    Orthonormal 𝕜 (frameComp hv O) := by
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪familyIsometry hv (O (EuclideanSpace.single i (1 : 𝕜))),
      familyIsometry hv (O (EuclideanSpace.single j (1 : 𝕜)))⟫_𝕜 = if i = j then 1 else 0
  rw [(familyIsometry hv).inner_map_map, O.inner_map_map]
  exact orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i j

/-- Rotating a frame does not move its span — `V̂ Ô` and `V̂` are frames of the
same subspace, which is why the alignment costs nothing on the sine side. -/
theorem span_range_frameComp {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    Submodule.span 𝕜 (Set.range (frameComp hv O)) = Submodule.span 𝕜 (Set.range v) :=
  span_range_eq_of_orthonormal_of_mem (orthonormal_frameComp hv O)
    (fun i => by rw [frameComp_apply]
                 exact Submodule.sum_smul_mem _ _ fun j _ =>
                   Submodule.subset_span (Set.mem_range_self j))
    (by rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin])

/-- **Coordinate-map form of frame alignment.**

If `O` rotates the frame `v` toward `u`, then the inverse coordinate rotation
`O⁻¹` is close, pointwise, to the overlap operator `U⋆V`.  More precisely,

`‖(O⁻¹ - overlapOp hu hv) x‖ ≤ ‖V O - U‖_F ‖x‖`.

This is the bridge from an aligned eigenframe theorem to weighted spectral
coordinates.  It does not require the overlap operator to be invertible or
locally close to an isometry. -/
theorem norm_symm_sub_overlapOp_apply_le_frameError
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d))
    (x : EuclideanSpace 𝕜 (Fin d)) :
    ‖(O.symm.toLinearEquiv.toLinearMap - overlapOp hu hv) x‖ ≤
      Real.sqrt (∑ i, ‖frameComp hv O i - u i‖ ^ 2) * ‖x‖ := by
  set y : E := familyIsometry hv x with hy
  have hynorm : ‖y‖ = ‖x‖ := by
    rw [hy, (familyIsometry hv).norm_map]
  have hcoord : ∀ i : Fin d,
      ((O.symm.toLinearEquiv.toLinearMap - overlapOp hu hv) x) i =
        ⟪frameComp hv O i - u i, y⟫_𝕜 := by
    intro i
    have hOcoord : (O.symm.toLinearEquiv.toLinearMap x) i =
        ⟪frameComp hv O i, y⟫_𝕜 := by
      calc
        (O.symm.toLinearEquiv.toLinearMap x) i = (O.symm x) i := rfl
        _ = ⟪EuclideanSpace.single i (1 : 𝕜), O.symm x⟫_𝕜 := by
          rw [EuclideanSpace.inner_single_left, map_one, one_mul]
        _ = ⟪O (EuclideanSpace.single i (1 : 𝕜)), O (O.symm x)⟫_𝕜 :=
          (O.inner_map_map _ _).symm
        _ = ⟪O (EuclideanSpace.single i (1 : 𝕜)), x⟫_𝕜 := by
          rw [O.apply_symm_apply]
        _ = ⟪familyIsometry hv (O (EuclideanSpace.single i (1 : 𝕜))),
              familyIsometry hv x⟫_𝕜 :=
          ((familyIsometry hv).inner_map_map _ _).symm
        _ = ⟪frameComp hv O i, y⟫_𝕜 := by
          rw [frameComp, hy]
    have hMcoord : overlapOp hu hv x i = ⟪u i, y⟫_𝕜 := by
      rw [hy]
      exact overlapOp_coord hu hv x i
    rw [LinearMap.sub_apply]
    change (O.symm.toLinearEquiv.toLinearMap x) i - overlapOp hu hv x i = _
    rw [hOcoord, hMcoord, inner_sub_left]
  have hsum :
      ∑ i, ‖((O.symm.toLinearEquiv.toLinearMap - overlapOp hu hv) x) i‖ ^ 2 ≤
        (∑ i, ‖frameComp hv O i - u i‖ ^ 2) * ‖y‖ ^ 2 := by
    calc
      ∑ i, ‖((O.symm.toLinearEquiv.toLinearMap - overlapOp hu hv) x) i‖ ^ 2
          ≤ ∑ i, ‖frameComp hv O i - u i‖ ^ 2 * ‖y‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [hcoord i]
            have hinner := norm_inner_le_norm (𝕜 := 𝕜) (frameComp hv O i - u i) y
            have hpow := pow_le_pow_left₀ (norm_nonneg _) hinner 2
            simpa [mul_pow] using hpow
      _ = (∑ i, ‖frameComp hv O i - u i‖ ^ 2) * ‖y‖ ^ 2 := by
        rw [Finset.sum_mul]
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i, ‖((O.symm.toLinearEquiv.toLinearMap - overlapOp hu hv) x) i‖ ^ 2)
        ≤ Real.sqrt ((∑ i, ‖frameComp hv O i - u i‖ ^ 2) * ‖y‖ ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (∑ i, ‖frameComp hv O i - u i‖ ^ 2) * ‖y‖ := by
      rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _),
        Real.sqrt_sq (norm_nonneg y)]
    _ = Real.sqrt (∑ i, ‖frameComp hv O i - u i‖ ^ 2) * ‖x‖ := by
      rw [hynorm]

/-- **The Procrustes step, with the alignment exhibited.**

`‖V̂ Ô − V‖²_F ≤ 2 ‖sin Θ(V̂, V)‖²_F` for an orthogonal `Ô` acting on the
coordinate space of the frames, with the population frame `u` held fixed.  `Ô` is
the polar unitary of the overlap operator, so no minimization is left implicit. -/
theorem exists_unitary_sum_sq_norm_frameComp_sub_le {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        ∑ i, ‖frameComp hv O i - u i‖ ^ 2 ≤
          2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
            (Submodule.span 𝕜 (Set.range v)) ^ 2 := by
  refine ⟨(choosePolarUnitary (overlapOp hu hv)).symm,
    fun x y => LinearIsometryEquiv.inner_map_map _ x y, ?_⟩
  have h := sum_sq_norm_aligned_le_sinThetaSq hu hv
  rwa [sinThetaSq_eq_sinThetaFrobenius_sq_of_spans hu hv rfl rfl] at h

/-- **Procrustes alignment from any Frobenius sine bound.**

Given orthonormal frames `V`, `V̂` and *any* bound `C` on the Frobenius sine
distance between their spans, there is a unitary `Ô` on the block's coordinate
space with `‖V̂ Ô − V‖_F ≤ √2 · C`, where `V` is the supplied frame rather than
some other frame of the same span.

This is the alignment half of the paper's argument separated from the
perturbation half: it knows nothing about eigenvectors, singular vectors, or
gaps, so every theorem with a Frobenius sine bound gets its aligned-frame
conclusion by supplying that bound here.  The symmetric and rectangular theorems
both use it. -/
theorem exists_unitary_sqrt_sum_sq_norm_frameComp_sub_le {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) {C : ℝ}
    (hsine : sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) ≤ C) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv O i - u i‖ ^ 2) ≤ Real.sqrt 2 * C := by
  obtain ⟨O, hO, hsum⟩ := exists_unitary_sum_sq_norm_frameComp_sub_le hu hv
  refine ⟨O, hO, ?_⟩
  have hsnn : (0 : ℝ) ≤ sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) := sinThetaFrobenius_nonneg _ _
  calc Real.sqrt (∑ i, ‖frameComp hv O i - u i‖ ^ 2)
      ≤ Real.sqrt (2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 * C := mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, with an explicit `Ô`.**

For arbitrary ordered eigenframes `V`, `V̂` at a common index block and a
population-only gap `Δ`, there is an orthogonal `Ô` on the `d`-dimensional
coordinate space with

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`.

Unlike `yuWangSamworth_alignedBasis_frame_le` the population frame is the one
supplied, not a new frame of the same span. -/
theorem yuWangSamworth_alignedFrame_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
              (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ := by
  obtain ⟨O, hO, hsum⟩ :=
    exists_unitary_sum_sq_norm_frameComp_sub_le hu.orthonormal hv.orthonormal
  refine ⟨O, hO, ?_⟩
  have hsine := yuWangSamworth_sinTheta_frame_le hu hv hΔ hgap
  have hsnn : (0 : ℝ) ≤ sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) :=
    by rw [sinThetaFrobenius_eq]; exact (UnitarilyInvariantSeminorm.frobenius 𝕜 E).nonneg _
  calc Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2)
      ≤ Real.sqrt (2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 * (2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = 2 * Real.sqrt 2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ := by ring

/-- **Yu--Wang--Samworth alignment as a coordinate-map bound.**

Under the population-only gap hypotheses of Theorem 2, there is an isometric
coordinate map `W` whose distance from the overlap operator is controlled by
the same aligned-frame envelope.  This is the form needed by weighted spectral
embeddings such as classical MDS: `W` can act directly on coordinate vectors,
while `overlapOp` supplies the algebraic commutator/reconstruction decomposition.

No local near-isometry or small-polar-factor hypothesis is required. -/
theorem yuWangSamworth_alignmentMap_sub_overlapOp_apply_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ W : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪W x, W y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
      ∀ x, ‖(W - overlapOp hu.orthonormal hv.orthonormal) x‖ ≤
        (2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ) * ‖x‖ := by
  obtain ⟨O, _hO, hframe⟩ := yuWangSamworth_alignedFrame_le hu hv hΔ hgap
  refine ⟨O.symm.toLinearEquiv.toLinearMap,
    fun x y => O.symm.inner_map_map x y, fun x => ?_⟩
  exact (norm_symm_sub_overlapOp_apply_le_frameError
    hu.orthonormal hv.orthonormal O x).trans
      (mul_le_mul_of_nonneg_right hframe (norm_nonneg x))

/-- **The residual form of the aligned conclusion, with an explicit `Ô`.**
`‖V̂ Ô − V‖_F ≤ 2^{1/2} ‖V̂ Λ − Σ V̂‖_F / Δ`, the inequality Yu, Wang and Samworth
record as available from their proof before the residual is discarded. -/
theorem yuWangSamworth_alignedFrame_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          Real.sqrt 2 *
            Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ := by
  obtain ⟨O, hO, hsum⟩ :=
    exists_unitary_sum_sq_norm_frameComp_sub_le hu.orthonormal hv.orthonormal
  refine ⟨O, hO, ?_⟩
  have hsine := yuWangSamworth_sinTheta_le_residual hu hv hΔ hgap
  have hsnn : (0 : ℝ) ≤ sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) :=
    by rw [sinThetaFrobenius_eq]; exact (UnitarilyInvariantSeminorm.frobenius 𝕜 E).nonneg _
  calc Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2)
      ≤ Real.sqrt (2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 *
          (Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 *
          Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ := by
        ring

/-! ## Over `ℝ`: `Ô` as an element of `O(d)`

The source is a real-matrix paper, and its `Ô` is an orthogonal matrix.  A
bundled `EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)` is exactly
that, but a reader should not have to know it, so the real statement below
produces the matrix itself, together with its membership in
`Matrix.orthogonalGroup (Fin d) ℝ`. -/

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **The matrix of a coordinate isometry** in the standard basis:
`Ôⱼᵢ = (Ô eᵢ)ⱼ`.  Over `ℝ` this is the paper's orthogonal matrix. -/
@[expose]
noncomputable def frameAlignMatrix
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j i => O (EuclideanSpace.single i 1) j

@[simp] theorem frameAlignMatrix_apply
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (j i : Fin d) :
    frameAlignMatrix O j i = O (EuclideanSpace.single i 1) j := rfl

/-- **`Ô ∈ O(d)`.**  The columns of `frameAlignMatrix O` are the images of an
orthonormal basis under an isometry, so `ÔᵀÔ = I`. -/
theorem frameAlignMatrix_mem_orthogonalGroup
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    frameAlignMatrix O ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
  refine (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mpr ?_
  ext i k
  have hO := O.inner_map_map (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single k (1 : ℝ))
  have hsingle : ⟪(EuclideanSpace.single i (1 : ℝ)),
      (EuclideanSpace.single k (1 : ℝ))⟫_ℝ = if i = k then 1 else 0 :=
    orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i k
  rw [Matrix.mul_apply, Matrix.one_apply, ← hsingle, ← hO, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [Matrix.transpose_apply, RCLike.inner_apply, mul_comm]

omit [FiniteDimensional ℝ F] in
/-- The columns of `V̂Ô` in matrix notation. -/
theorem frameComp_eq_sum_frameAlignMatrix {v : Fin d → F} (hv : Orthonormal ℝ v)
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    frameComp hv O i = ∑ j, frameAlignMatrix O j i • v j :=
  frameComp_apply hv O i

/-- **Procrustes alignment from any Frobenius sine bound, over `ℝ` with `Ô ∈ O(d)`.**

`exists_unitary_sqrt_sum_sq_norm_frameComp_sub_le` at `𝕜 = ℝ`, with the coordinate
isometry replaced by its matrix and the columns of `V̂ Ô` written out as
`(V̂ Ô)ᵢ = ∑ⱼ Ôⱼᵢ v̂ⱼ`. -/
theorem exists_orthogonal_sqrt_sum_sq_norm_sub_le {u v : Fin d → F}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) {C : ℝ}
    (hsine : sinThetaFrobenius (Submodule.span ℝ (Set.range u))
      (Submodule.span ℝ (Set.range v)) ≤ C) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • v j) - u i‖ ^ 2) ≤ Real.sqrt 2 * C := by
  obtain ⟨O, -, hbound⟩ := exists_unitary_sqrt_sum_sq_norm_frameComp_sub_le hu hv hsine
  refine ⟨frameAlignMatrix O, frameAlignMatrix_mem_orthogonalGroup O, ?_⟩
  have hcols : ∀ i, (∑ j, frameAlignMatrix O j i • v j) = frameComp hv O i :=
    fun i => (frameComp_eq_sum_frameAlignMatrix hv O i).symm
  simpa only [hcols] using hbound

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, over `ℝ` with `Ô ∈ O(d)`.**

The literal printed statement: there is an orthogonal `d × d` matrix `Ô` with

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`,

where the `i`-th column of `V̂ Ô` is `∑ⱼ Ôⱼᵢ v̂ⱼ` and `V` is the supplied
population frame.  This is `yuWangSamworth_alignedFrame_le` at `𝕜 = ℝ`, with the
coordinate isometry replaced by its matrix. -/
theorem yuWangSamworth_alignedFrame_real_le
    {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank ℝ F = n} {e : Fin d ↪ Fin n} {u v : Fin d → F}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • v j) - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius ℝ F (B - A)) / Δ := by
  obtain ⟨O, -, hbound⟩ := yuWangSamworth_alignedFrame_le hu hv hΔ hgap
  refine ⟨frameAlignMatrix O, frameAlignMatrix_mem_orthogonalGroup O, ?_⟩
  have hcols : ∀ i, (∑ j, frameAlignMatrix O j i • v j) = frameComp hv.orthonormal O i :=
    fun i => (frameComp_eq_sum_frameAlignMatrix hv.orthonormal O i).symm
  simpa only [hcols] using hbound

end Real

end YuWangSamworth2015
