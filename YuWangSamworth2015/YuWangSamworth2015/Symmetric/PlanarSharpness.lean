/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.GroundedImports

/-!
# Yu--Wang--Samworth Section 2: the small-angle sharpness scale

The paper's second sharpness construction, for nearby one-dimensional
eigenspaces:

> `Σ = diag(3,1)` and `Σ̂ = R_ε Σ R_ε^T` with `R_ε` the rotation with entries
> `√(1-ε²)` and `ε`.  For `v = (1,0)ᵀ` and `v̂` the leading eigenvector of `Σ̂`,
> `sin Θ(v̂, v) = ε`, `‖v̂ − v‖² = 2 − 2√(1-ε²)`, and
> `2‖Σ̂ − Σ‖_op / (3 − 1) = 2ε`.
> Thus the sine bound is tight up to factor `2`, and the vector bound up to
> `2^{3/2}`, even in a small-angle regime.

## The model, stated without coordinates

`Σ = diag(3,1)` is the operator that is `3` on the line `ℝ v` and `1` on its
complement — that is `TauCeti.twoLevelOperator 1 3 (𝕜 ∙ v)` — and conjugating by
a rotation only moves the line.  So the pair `(Σ, Σ̂)` is exactly
`(twoLevelOperator 1 3 (𝕜 ∙ v), twoLevelOperator 1 3 (𝕜 ∙ v̂))` for two unit
vectors, and `TauCeti.twoLevelOperator_sub` gives `Σ̂ − Σ = 2 (P_{v̂} − P_v)`
with no matrix entries anywhere.

Two consequences of stating it this way.  The rotation parameter is replaced by
the overlap `c = ⟪v, v̂⟫`, with `ε = √(1-c²)` — the paper's `ε` is the sine, and
`√(1-ε²)` its cosine.  And nothing forces the ambient space to be
two-dimensional: the construction and every conclusion hold for two lines in any
finite-dimensional space, of which the paper's `ℝ²` is the smallest case.

*A note on the printed `v̂`.*  The paper writes `v̂ = (√(1-ε²), −ε)ᵀ`, which is
the leading eigenvector of `R_ε^T Σ R_ε`, not of `R_ε Σ R_ε^T`.  The sign does
not affect any displayed quantity — all three depend on `v̂` only through
`⟪v, v̂⟫ = √(1-ε²)` — so the model here fixes the overlap rather than a sign
convention.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {v w : E} {c : ℝ}

/-! ## The angle between the two lines -/

omit [FiniteDimensional 𝕜 E] in
/-- The projection of one unit vector onto the line of another has length the
overlap. -/
theorem norm_projection_span_singleton (hv : ‖v‖ = 1) (hc0 : 0 ≤ c)
    (hoverlap : ⟪v, w⟫_𝕜 = (c : 𝕜)) :
    ‖projection (𝕜 ∙ v) w‖ = c := by
  have hproj : projection (𝕜 ∙ v) w = ⟪v, w⟫_𝕜 • v := by
    change (𝕜 ∙ v).starProjection w = _
    rw [Submodule.starProjection_singleton, hv]
    simp
  rw [hproj, norm_smul, hv, mul_one, hoverlap, RCLike.norm_ofReal, abs_of_nonneg hc0]

omit [FiniteDimensional 𝕜 E] in
/-- **The sine of the angle between the two lines is `√(1 - c²)`.**  This is the
paper's `ε`. -/
theorem norm_projection_orthogonal_span_singleton (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hc0 : 0 ≤ c) (hoverlap : ⟪v, w⟫_𝕜 = (c : 𝕜)) :
    ‖projection (𝕜 ∙ v)ᗮ w‖ = Real.sqrt (1 - c ^ 2) := by
  have hsq : ‖projection (𝕜 ∙ v)ᗮ w‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_starProjection_orthogonal_sq hw,
      norm_projection_span_singleton hv hc0 hoverlap]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-! ## The model satisfies the theorem's hypotheses -/

omit [FiniteDimensional 𝕜 E] in
/-- The leading eigenspace of the model is the line it was built from. -/
theorem eigenspace_planarSharpness (u : E) :
    eigenspace (twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ u)) ((3 : ℝ) : 𝕜) = 𝕜 ∙ u :=
  eigenspace_twoLevelOperator (by norm_num)

omit [FiniteDimensional 𝕜 E] in
/-- Each line is one-dimensional, so the two blocks have equal rank `d = 1`. -/
theorem finrank_span_singleton_of_norm_one (hv : ‖v‖ = 1) :
    finrank 𝕜 (𝕜 ∙ v) = 1 :=
  finrank_span_singleton (by rw [← norm_ne_zero_iff, hv]; norm_num)

/-- The two leading eigenspaces are a corresponding eigenblock. -/
theorem correspondingEigenblock_planarSharpness (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {n : ℕ} (hn : finrank 𝕜 E = n) :
    CorrespondingEigenblock
      (isSymmetric_twoLevelOperator (𝕜 := 𝕜) (a := 1) (b := 3) (U := 𝕜 ∙ v))
      (isSymmetric_twoLevelOperator (𝕜 := 𝕜) (a := 1) (b := 3) (U := 𝕜 ∙ w))
      (eigenspace (twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ v)) ((3 : ℝ) : 𝕜))
      (eigenspace (twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ w)) ((3 : ℝ) : 𝕜)) :=
  correspondingEigenblock_topEigenspace _ _ hn
    (eigenvalues_twoLevelOperator_le (by norm_num) hn)
    (by rw [eigenspace_planarSharpness, finrank_span_singleton_of_norm_one hv])
    (eigenvalues_twoLevelOperator_le (by norm_num) hn)
    (by rw [eigenspace_planarSharpness, finrank_span_singleton_of_norm_one hw])

omit [FiniteDimensional 𝕜 E] in
/-- **The population gap is `λ₁ − λ₂ = 3 − 1 = 2`.** -/
theorem internalGap_planarSharpness :
    InternalGap (twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ v))
      (eigenspace (twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ v)) ((3 : ℝ) : 𝕜)) 2 := by
  rw [eigenspace_planarSharpness]
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
    internalGap_twoLevelOperator (𝕜 := 𝕜) (a := 1) (b := 3) (U := 𝕜 ∙ v)

/-! ## The achieved distances -/

/-- **`‖sin Θ(v̂, v)‖_F = ε`.**  The single angle between the two lines. -/
theorem sinThetaFrobenius_planarSharpness (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hc0 : 0 ≤ c) (hoverlap : ⟪v, w⟫_𝕜 = (c : 𝕜)) :
    sinThetaFrobenius (𝕜 ∙ w) (𝕜 ∙ v) = Real.sqrt (1 - c ^ 2) := by
  rw [sinThetaFrobenius_span_singleton hw,
    norm_projection_orthogonal_span_singleton hv hw hc0 hoverlap]

/-- **`‖Σ̂ − Σ‖_op = 2ε`.**  The perturbation is `2` times the projector
difference, and for equal-rank blocks that is the sine map. -/
theorem opNorm_planarSharpness_perturbation (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hc0 : 0 ≤ c) (hoverlap : ⟪v, w⟫_𝕜 = (c : 𝕜)) :
    ‖(twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ w) -
        twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ v)).toContinuousLinearMap‖ =
      2 * Real.sqrt (1 - c ^ 2) := by
  have hrank : finrank 𝕜 (𝕜 ∙ w) = finrank 𝕜 (𝕜 ∙ v) := by
    rw [finrank_span_singleton_of_norm_one hv, finrank_span_singleton_of_norm_one hw]
  rw [twoLevelOperator_sub, map_smul, norm_smul,
    opNorm_projection_sub_eq_opNorm_sinThetaMap (𝕜 ∙ w) (𝕜 ∙ v) hrank,
    opNorm_sinThetaMap_span_singleton hw,
    norm_projection_orthogonal_span_singleton hv hw hc0 hoverlap]
  congr 1
  rw [show ((3 : ℝ) : 𝕜) - ((1 : ℝ) : 𝕜) = ((2 : ℝ) : 𝕜) by
    rw [← RCLike.ofReal_sub]; norm_num, RCLike.norm_ofReal]
  norm_num

omit [FiniteDimensional 𝕜 E] in
/-- **`‖v̂ − v‖² = 2 − 2√(1-ε²)`.**  The paper's vector displacement, written
through the overlap. -/
theorem norm_sub_sq_planarSharpness (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hoverlap : ⟪v, w⟫_𝕜 = (c : 𝕜)) :
    ‖w - v‖ ^ 2 = 2 - 2 * c := by
  rw [@norm_sub_sq 𝕜, hv, hw]
  rw [show ⟪w, v⟫_𝕜 = (c : 𝕜) by rw [← inner_conj_symm, hoverlap, RCLike.conj_ofReal]]
  simp
  ring

/-! ## The sharpness statement -/

/-- **Yu--Wang--Samworth Section 2, small-angle sharpness.**

Writing `ε := √(1 - c²)` for the sine of the angle between the two lines, the
model satisfies every hypothesis of `YuWangSamworth2015.yuWangSamworth_sinTheta_le` at
`d = 1` and `Δ = 2`, achieves `‖sin Θ(v̂, v)‖_F = ε`, and the theorem's
operator-norm branch `2 √d ‖E‖_op / Δ` equals `2ε`.

So the sine bound is tight up to *exactly* the factor `2` the paper claims, at
every angle — in particular in the small-angle regime, which is the point of
this example: the orthogonal-blocks construction only pins the constant down at
the maximal angle. -/
theorem yuWangSamworth_sharpness_planarRotation (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hc0 : 0 ≤ c) (hoverlap : ⟪v, w⟫_𝕜 = (c : 𝕜)) :
    2 * (Real.sqrt 1 *
          ‖(twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ w) -
            twoLevelOperator (𝕜 := 𝕜) 1 3 (𝕜 ∙ v)).toContinuousLinearMap‖) / 2 =
      2 * sinThetaFrobenius (𝕜 ∙ w) (𝕜 ∙ v) := by
  rw [opNorm_planarSharpness_perturbation hv hw hc0 hoverlap,
    sinThetaFrobenius_planarSharpness hv hw hc0 hoverlap, Real.sqrt_one]
  ring

end DavisKahanTheory
end YuWangSamworth2015
