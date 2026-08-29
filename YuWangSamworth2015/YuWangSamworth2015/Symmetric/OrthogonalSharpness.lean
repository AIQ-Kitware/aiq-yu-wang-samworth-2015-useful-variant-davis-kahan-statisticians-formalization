/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.GroundedImports

/-!
# Yu--Wang--Samworth Section 2: the orthogonal-blocks sharpness example

The paper's first sharpness construction, from the discussion after Theorem 2:

> `Σ = diag(3,…,3,1,…,1)` with `d` threes, and
> `Σ̂ = diag(2-ε,…,2-ε,2,…,2)` with `p-d` copies of `2-ε`,
> where `0 < ε` and `1 ≤ d ≤ ⌊p/2⌋`.  The top-`d` eigenspaces are orthogonal,
> so for every `O ∈ O(d)`,
> `‖V̂O − V‖_F = √2 ‖sin Θ(V̂, V)‖_F = √(2d)`,
> while `2^{3/2} √d ‖E‖_op / (λ_d − λ_{d+1}) = √(2d)(1+ε)`.

Everything on that line is proved here, against the *same* hypotheses the
theorem carries: `correspondingEigenblock_orthogonalSharpness` supplies the
branch-selection datum and `internalGap_orthogonalSharpness` the population
gap, so the example is a genuine instance of
`YuWangSamworth2015.yuWangSamworth_alignedBasis_le` rather than a numerical coincidence.
The conclusion is that the constant `2^{3/2}` and the `√d` dimension dependence
of that theorem cannot be improved: the achieved distance is `√(2d)` and the
bound is `√(2d)(1+ε)` for arbitrarily small `ε`.

The model is stated for an arbitrary orthonormal basis of an arbitrary
finite-dimensional `RCLike` inner product space rather than for `ℝ^p`, which
costs nothing and covers the paper's real matrices by taking
`EuclideanSpace ℝ (Fin p)` with its standard basis.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ## The model data -/

/-- `Σ = diag(3,…,3,1,…,1)`: the population covariance of the paper's
orthogonal-blocks example, with `3` on the first `d` indices. -/
def orthogonalSharpnessPopulationData (p d : ℕ) : Fin p → ℝ :=
  fun i => if (i : ℕ) < d then 3 else 1

/-- `Σ̂ = diag(2-ε,…,2-ε,2,…,2)`: the perturbed covariance, with `2` on the
*last* `d` indices.  The displacement of the leading block from the front to
the back of the index range is what makes the two top-`d` eigenspaces
orthogonal. -/
def orthogonalSharpnessSampleData (p d : ℕ) (ε : ℝ) : Fin p → ℝ :=
  fun i => if (i : ℕ) < p - d then 2 - ε else 2

section Counting

/-- The initial segment of `Fin p` of length `d` has `d` elements. -/
private theorem card_filter_val_lt (p d : ℕ) (hdp : d ≤ p) :
    (Finset.univ.filter (fun i : Fin p => (i : ℕ) < d)).card = d := by
  classical
  have himg : (Finset.univ.filter (fun i : Fin p => (i : ℕ) < d)).image Fin.val
      = Finset.range d := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    exact ⟨by rintro ⟨i, hi, rfl⟩; exact hi,
      fun hm => ⟨⟨m, lt_of_lt_of_le hm hdp⟩, hm, rfl⟩⟩
  have hcard := Finset.card_image_of_injective
    (Finset.univ.filter (fun i : Fin p => (i : ℕ) < d)) Fin.val_injective
  rw [himg, Finset.card_range] at hcard
  exact hcard.symm

/-- The terminal segment of `Fin p` above `p - d` has `d` elements. -/
private theorem card_filter_not_val_lt (p d : ℕ) (hdp : d ≤ p) :
    (Finset.univ.filter (fun i : Fin p => ¬ ((i : ℕ) < p - d))).card = d := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin p))) (p := fun i : Fin p => (i : ℕ) < p - d)
  rw [card_filter_val_lt p (p - d) (Nat.sub_le p d), Finset.card_univ,
    Fintype.card_fin] at hsum
  omega

end Counting

section Model

variable {p d : ℕ} {ε : ℝ}

/-- Every population eigenvalue is at most `3`. -/
theorem orthogonalSharpnessPopulationData_le :
    ∀ i, orthogonalSharpnessPopulationData p d i ≤ 3 := by
  intro i
  rw [orthogonalSharpnessPopulationData]
  split_ifs <;> norm_num

/-- Every perturbed eigenvalue is at most `2`. -/
theorem orthogonalSharpnessSampleData_le (hε : 0 < ε) :
    ∀ i, orthogonalSharpnessSampleData p d ε i ≤ 2 := by
  intro i
  rw [orthogonalSharpnessSampleData]
  split_ifs <;> linarith

open scoped Classical in
/-- The population level set at `3` is the leading `d` indices. -/
theorem card_orthogonalSharpnessPopulation_level (hdp : d ≤ p) :
    ({i | ((orthogonalSharpnessPopulationData p d i : ℝ) : 𝕜) = ((3 : ℝ) : 𝕜)} :
      Finset (Fin p)).card = d := by
  classical
  refine Eq.trans (congrArg Finset.card ?_) (card_filter_val_lt p d hdp)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    orthogonalSharpnessPopulationData, RCLike.ofReal_inj]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by norm_num) h

open scoped Classical in
/-- The perturbed level set at `2` is the trailing `d` indices. -/
theorem card_orthogonalSharpnessSample_level (hε : 0 < ε) (hdp : d ≤ p) :
    ({i | ((orthogonalSharpnessSampleData p d ε i : ℝ) : 𝕜) = ((2 : ℝ) : 𝕜)} :
      Finset (Fin p)).card = d := by
  classical
  refine Eq.trans (congrArg Finset.card ?_) (card_filter_not_val_lt p d hdp)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    orthogonalSharpnessSampleData, RCLike.ofReal_inj]
  split_ifs with h
  · exact iff_of_false (fun hc => absurd (by linarith : ε = 0) (ne_of_gt hε))
      (not_not_intro h)
  · exact iff_of_true rfl h

variable (b : OrthonormalBasis (Fin p) 𝕜 E)

/-- The population operator of the model. -/
noncomputable def orthogonalSharpnessPopulation (d : ℕ) : E →ₗ[𝕜] E :=
  basisDiagonal b (orthogonalSharpnessPopulationData p d)

/-- The perturbed operator of the model. -/
noncomputable def orthogonalSharpnessSample (d : ℕ) (ε : ℝ) : E →ₗ[𝕜] E :=
  basisDiagonal b (orthogonalSharpnessSampleData p d ε)

omit [FiniteDimensional 𝕜 E] in
/-- The population top-`d` eigenspace is the leading index block. -/
theorem eigenspace_orthogonalSharpnessPopulation :
    eigenspace (orthogonalSharpnessPopulation b d) ((3 : ℝ) : 𝕜) =
      b.spanIndices {i : Fin p | (i : ℕ) < d} := by
  rw [orthogonalSharpnessPopulation, eigenspace_basisDiagonal]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, orthogonalSharpnessPopulationData, RCLike.ofReal_inj]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by norm_num) h

omit [FiniteDimensional 𝕜 E] in
/-- The perturbed top-`d` eigenspace is the trailing index block. -/
theorem eigenspace_orthogonalSharpnessSample (hε : 0 < ε) :
    eigenspace (orthogonalSharpnessSample b d ε) ((2 : ℝ) : 𝕜) =
      b.spanIndices {i : Fin p | ¬ ((i : ℕ) < p - d)} := by
  rw [orthogonalSharpnessSample, eigenspace_basisDiagonal]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, orthogonalSharpnessSampleData, RCLike.ofReal_inj]
  split_ifs with h
  · exact iff_of_false (fun hc => absurd (by linarith : ε = 0) (ne_of_gt hε))
      (not_not_intro h)
  · exact iff_of_true rfl h

/-! ## The example satisfies the theorem's hypotheses -/

omit [FiniteDimensional 𝕜 E] in
private theorem finrank_of_orthonormalBasis (b : OrthonormalBasis (Fin p) 𝕜 E) :
    finrank 𝕜 E = p := by
  rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]

/-- The two leading eigenspaces are a corresponding eigenblock: both are
selected by the leading `d` indices of their own sorted eigenbasis. -/
theorem correspondingEigenblock_orthogonalSharpness (hε : 0 < ε) (hdp : d ≤ p) :
    CorrespondingEigenblock
      (isSymmetric_basisDiagonal b (orthogonalSharpnessPopulationData p d))
      (isSymmetric_basisDiagonal b (orthogonalSharpnessSampleData p d ε))
      (eigenspace (orthogonalSharpnessPopulation b d) ((3 : ℝ) : 𝕜))
      (eigenspace (orthogonalSharpnessSample b d ε) ((2 : ℝ) : 𝕜)) :=
  correspondingEigenblock_basisDiagonal b b _ _ (finrank_of_orthonormalBasis b)
    orthogonalSharpnessPopulationData_le (orthogonalSharpnessSampleData_le hε)
    (card_orthogonalSharpnessPopulation_level hdp)
    (card_orthogonalSharpnessSample_level hε hdp)

omit [FiniteDimensional 𝕜 E] in
/-- **The top-`d` eigenspaces are orthogonal** — the whole point of the
construction.  The population block is the leading `d` indices, the perturbed
block is the trailing `d`, and `2d ≤ p` keeps them disjoint. -/
theorem orthogonal_orthogonalSharpness (hε : 0 < ε) (hdp : 2 * d ≤ p) :
    eigenspace (orthogonalSharpnessPopulation b d) ((3 : ℝ) : 𝕜) ≤
      (eigenspace (orthogonalSharpnessSample b d ε) ((2 : ℝ) : 𝕜))ᗮ := by
  rw [eigenspace_orthogonalSharpnessPopulation, eigenspace_orthogonalSharpnessSample b hε,
    OrthonormalBasis.orthogonal_spanIndices]
  refine OrthonormalBasis.spanIndices_mono b fun i hi => ?_
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
  simp only [Set.mem_ofPred_eq] at hi
  omega

omit [FiniteDimensional 𝕜 E] in
/-- The population block has the paper's dimension `d`. -/
theorem finrank_eigenspace_orthogonalSharpnessPopulation (hdp : d ≤ p) :
    finrank 𝕜 (eigenspace (orthogonalSharpnessPopulation b d) ((3 : ℝ) : 𝕜)) = d := by
  classical
  rw [eigenspace_orthogonalSharpnessPopulation,
    OrthonormalBasis.finrank_spanIndices_set]
  refine Eq.trans (congrArg Finset.card ?_) (card_filter_val_lt p d hdp)
  ext i
  simp

omit [FiniteDimensional 𝕜 E] in
/-- The perturbed block has the same dimension `d`. -/
theorem finrank_eigenspace_orthogonalSharpnessSample (hε : 0 < ε) (hdp : d ≤ p) :
    finrank 𝕜 (eigenspace (orthogonalSharpnessSample b d ε) ((2 : ℝ) : 𝕜)) = d := by
  classical
  rw [eigenspace_orthogonalSharpnessSample b hε,
    OrthonormalBasis.finrank_spanIndices_set]
  refine Eq.trans (congrArg Finset.card ?_) (card_filter_not_val_lt p d hdp)
  ext i
  simp

omit [FiniteDimensional 𝕜 E] in
/-- **The population gap is `λ_d − λ_{d+1} = 3 − 1 = 2`.**  The restricted
spectrum of the leading block is `{3}` and of its complement is `{1}`.

No size hypotheses on `d`: if either block is trivial the separation holds
vacuously, so the statement is cleanest without them. -/
theorem internalGap_orthogonalSharpness :
    InternalGap (orthogonalSharpnessPopulation b d)
      (eigenspace (orthogonalSharpnessPopulation b d) ((3 : ℝ) : 𝕜)) 2 := by
  intro lam μ hlam hμ
  rw [eigenspace_orthogonalSharpnessPopulation] at hlam hμ
  -- The block carries only the value `3`.
  have h3 : lam = 3 := by
    obtain ⟨i, hi, rfl⟩ :=
      restrictedSpectrum_basisDiagonal_subset b _ _ hlam
    simp only [Set.mem_ofPred_eq] at hi
    simp [orthogonalSharpnessPopulationData, hi]
  -- Its complement carries only the value `1`.
  have h1 : μ = 1 := by
    rw [OrthonormalBasis.orthogonal_spanIndices] at hμ
    obtain ⟨i, hi, rfl⟩ :=
      restrictedSpectrum_basisDiagonal_subset b _ _ hμ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hi
    simp [orthogonalSharpnessPopulationData, hi]
  rw [h3, h1]
  norm_num

/-- **The perturbation has operator norm `1 + ε`.**  The largest displacement is
on the leading block, where `Σ̂` reads `2 − ε` against `Σ`'s `3`. -/
theorem opNorm_orthogonalSharpness_perturbation (hε : 0 < ε) (hd : 1 ≤ d)
    (hdp : 2 * d ≤ p) :
    ‖(orthogonalSharpnessSample b d ε -
        orthogonalSharpnessPopulation b d).toContinuousLinearMap‖ = 1 + ε := by
  have hp0 : 0 < p := by omega
  rw [orthogonalSharpnessSample, orthogonalSharpnessPopulation, basisDiagonal_sub]
  refine norm_basisDiagonal_eq b _ (by linarith) ?_ (i₀ := ⟨0, hp0⟩) ?_
  · intro i
    simp only [Pi.sub_apply, orthogonalSharpnessSampleData,
      orthogonalSharpnessPopulationData, abs_le]
    split_ifs <;> constructor <;> linarith
  · have h0d : (0 : ℕ) < d := hd
    have h0pd : (0 : ℕ) < p - d := by omega
    simp only [Pi.sub_apply, orthogonalSharpnessSampleData,
      orthogonalSharpnessPopulationData]
    rw [ite_eq_left (by simpa using h0pd), ite_eq_left (by simpa using h0d)]
    rw [show (2 - ε) - 3 = -(1 + ε) by ring, abs_neg, abs_of_pos (by linarith)]

/-! ## The achieved distances -/

/-- **`‖sin Θ(V̂, V)‖_F = √d`.**  The blocks are orthogonal, so every principal
angle is a right angle and the sine cross-projection is the block projector
itself. -/
theorem sinThetaFrobenius_orthogonalSharpness (hε : 0 < ε) (hd : 1 ≤ d)
    (hdp : 2 * d ≤ p) :
    sinThetaFrobenius (eigenspace (orthogonalSharpnessPopulation b d) ((3 : ℝ) : 𝕜))
        (eigenspace (orthogonalSharpnessSample b d ε) ((2 : ℝ) : 𝕜)) =
      Real.sqrt d := by
  classical
  rw [eigenspace_orthogonalSharpnessPopulation, eigenspace_orthogonalSharpnessSample b hε,
    sinThetaFrobenius_spanIndices_of_subset_compl b (finrank_of_orthonormalBasis b) _ _
      (fun i hi => by
        simp only [Set.mem_ofPred_eq] at hi
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
        omega)]
  congr 1
  rw [Set.toFinset_ofPred]
  exact_mod_cast card_filter_val_lt p d (by omega)

omit [FiniteDimensional 𝕜 E] in
/-- **Every aligned orthonormal pair is at distance exactly `√(2d)`.**  This is
the paper's `‖V̂O − V‖_F = √(2d)` for every `O ∈ O(d)`: orthogonality makes the
distance independent of the alignment, so no choice of `O` can do better. -/
theorem dist_orthogonalSharpness_aligned (hε : 0 < ε)
    (hdp : 2 * d ≤ p) {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v)
    (hspanU : Submodule.span 𝕜 (Set.range u) =
      eigenspace (orthogonalSharpnessPopulation b d) ((3 : ℝ) : 𝕜))
    (hspanV : Submodule.span 𝕜 (Set.range v) =
      eigenspace (orthogonalSharpnessSample b d ε) ((2 : ℝ) : 𝕜)) :
    Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) = Real.sqrt (2 * d) := by
  rw [sum_sq_norm_sub_eq_of_le_orthogonal
    (orthogonal_orthogonalSharpness (b := b) (d := d) (ε := ε) hε hdp) hu hv
    (fun i => hspanU ▸ Submodule.subset_span ⟨i, rfl⟩)
    (fun i => hspanV ▸ Submodule.subset_span ⟨i, rfl⟩)]

/-! ## The sharpness statement -/

/-- **Yu--Wang--Samworth Section 2, orthogonal-blocks sharpness.**

The aligned-basis bound of `YuWangSamworth2015.yuWangSamworth_alignedBasis_le` is attained
up to the factor `1 + ε`: the model satisfies every hypothesis of that theorem,
every aligned orthonormal pair realizes distance exactly `√(2d)`, and the
theorem's operator-norm branch `2^{3/2} √d ‖E‖_op / Δ` equals `√(2d)(1+ε)`.
Letting `ε ↓ 0` shows the constant `2^{3/2}` and the `√d` dimension dependence
cannot be uniformly improved. -/
theorem yuWangSamworth_sharpness_orthogonalBlocks (hε : 0 < ε) (hd : 1 ≤ d)
    (hdp : 2 * d ≤ p) :
    2 * Real.sqrt 2 *
        (Real.sqrt d * ‖(orthogonalSharpnessSample b d ε -
          orthogonalSharpnessPopulation b d).toContinuousLinearMap‖) / 2 =
      Real.sqrt (2 * d) * (1 + ε) := by
  rw [opNorm_orthogonalSharpness_perturbation b hε hd hdp,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  ring

end Model

end DavisKahanTheory
end YuWangSamworth2015
