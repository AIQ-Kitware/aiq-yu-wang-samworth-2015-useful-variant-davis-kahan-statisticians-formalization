/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.GroundedImports

/-!
# Yu--Wang--Samworth Section 2: the published middle-block sharpness example

The sharpness construction of the *published* Biometrika article, from the
discussion after Theorem 2:

> `Σ = diag(λ₁,…,λ_p)` with `λ₁ = ⋯ = λ_{p-2d} = 5`,
> `λ_{p-2d+1} = ⋯ = λ_{p-d} = 3` and `λ_{p-d+1} = ⋯ = λ_p = 1`; and `Σ̂`
> diagonal with first `p-2d` entries `5`, next `d` entries `2` and last `d`
> entries `2+ε`.  The block of interest is the eigenvectors for the eigenvalue
> `3`, so the population gap is two-sided, `min(5-3, 3-1) = 2`.

`YuWangSamworth2015/Symmetric/OrthogonalSharpness.lean` formalizes the 2014
preprint's earlier construction, in which the block of interest is the *top*
eigenspace.  Both prove the same sharpness claim, but only the published one
exercises a two-sided population gap, and that is exactly what made it hard to
formalize: its block sits in the *middle* of both spectra, so the branch
selection cannot be produced by "leading `d` eigenvectors" reasoning.

`YuWangSamworth2015.correspondingEigenblock_basisDiagonal_level` is the constructor that
closes that gap.  It rests on
`LinearMap.IsSymmetric.eigenvalues_level_eq_Ico` — every eigenvalue level set of
a symmetric operator is a contiguous range of sorted indices — and on
`TauCeti.card_filter_lt_eigenvalues_basisDiagonal`, which reads the position of
that range off the coefficient list.

The displacement that creates orthogonality is now *within* the two spectra: the
population block sits at coordinates `p-2d …p-d-1` while the perturbed block,
which occupies the same *ordered* positions because `2+ε` is the second largest
sample eigenvalue, sits at coordinates `p-d …p-1`.

## The parameter range

Everything below is proved for the full range `0 < ε < 3`.  The construction
needs `2 < 2 + ε < 5`: the inequality on the right is what puts `2+ε` *second*
in the sorted sample spectrum, so that the perturbed block occupies the same
ordered positions as the population block of threes, and the inequality on the
left is what separates it from the `d` sample eigenvalues equal to `2`.

That range is maximal **when `2 * d < p`**, which is the case the example is
about.  `card_middleSharpnessSample_level_three` computes the multiplicity of
the level `2+ε` at `ε = 3` to be `p - d`: it has merged with the leading level
`5`, so for `2 * d < p` it differs from the population block's `d` and the two
blocks are no longer a corresponding eigenblock.  At `ε = 0` the level merges
downwards with the `2`s instead.  Neither endpoint is a counterexample to the
sharpness claim — the construction simply stops describing what it claims to.

In the degenerate case `p = 2 * d` there is no leading level `5` at all, `p - d`
*is* `d`, and the ordering constraint disappears: every `ε > 0` would do.  The
uniform hypothesis `ε < 3` carried below is therefore sufficient everywhere and
necessary only for `2 * d < p`.

As in the preprint example the model is stated over an arbitrary orthonormal
basis of an arbitrary finite-dimensional `RCLike` inner product space, which
covers the paper's real `p × p` matrices at `EuclideanSpace ℝ (Fin p)`.
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

/-- `Σ = diag(5,…,5,3,…,3,1,…,1)`: the population covariance of the published
example, with `d` threes in the middle. -/
def middleSharpnessPopulationData (p d : ℕ) : Fin p → ℝ :=
  fun i => if (i : ℕ) < p - 2 * d then 5 else if (i : ℕ) < p - d then 3 else 1

/-- `Σ̂ = diag(5,…,5,2,…,2,2+ε,…,2+ε)`: the perturbed covariance.  Its second
largest eigenvalue is `2+ε`, carried by the *last* `d` coordinates, so the block
occupying the same ordered positions as the population block of threes is
orthogonal to it. -/
def middleSharpnessSampleData (p d : ℕ) (ε : ℝ) : Fin p → ℝ :=
  fun i => if (i : ℕ) < p - 2 * d then 5 else if (i : ℕ) < p - d then 2 else 2 + ε

section Counting

/-- An index range of `Fin p` has the expected number of elements. -/
private theorem card_filter_val_Ico (p a b : ℕ) (hb : b ≤ p) :
    (Finset.univ.filter (fun i : Fin p => a ≤ (i : ℕ) ∧ (i : ℕ) < b)).card = b - a := by
  classical
  have himg :
      (Finset.univ.filter (fun i : Fin p => a ≤ (i : ℕ) ∧ (i : ℕ) < b)).image Fin.val
        = Finset.Ico a b := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    exact ⟨by rintro ⟨i, hi, rfl⟩; exact hi,
      fun hm => ⟨⟨m, lt_of_lt_of_le hm.2 hb⟩, hm, rfl⟩⟩
  have hcard := Finset.card_image_of_injective
    (Finset.univ.filter (fun i : Fin p => a ≤ (i : ℕ) ∧ (i : ℕ) < b)) Fin.val_injective
  rw [himg, Nat.card_Ico] at hcard
  exact hcard.symm

end Counting

section Model

variable {p d : ℕ} {ε : ℝ}

open scoped Classical in
/-- The population eigenvalues strictly above `3` are the leading `p - 2d`. -/
theorem card_middleSharpnessPopulation_gt (hdp : 2 * d ≤ p) :
    ({i | (3 : ℝ) < middleSharpnessPopulationData p d i} : Finset (Fin p)).card
      = p - 2 * d := by
  classical
  have hset : ({i | (3 : ℝ) < middleSharpnessPopulationData p d i} : Finset (Fin p))
      = Finset.univ.filter (fun i : Fin p => 0 ≤ (i : ℕ) ∧ (i : ℕ) < p - 2 * d) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [middleSharpnessPopulationData]
    split_ifs with h1 h2
    · exact iff_of_true (by norm_num) ⟨Nat.zero_le _, h1⟩
    · exact iff_of_false (by norm_num) (by omega)
    · exact iff_of_false (by norm_num) (by omega)
  rw [hset, card_filter_val_Ico p 0 (p - 2 * d) (by omega), Nat.sub_zero]

open scoped Classical in
/-- The perturbed eigenvalues strictly above `2+ε` are the same leading
`p - 2d` indices — which is why the two blocks correspond. -/
theorem card_middleSharpnessSample_gt (hε : 0 < ε) (hε1 : ε < 3) (hdp : 2 * d ≤ p) :
    ({i | (2 + ε : ℝ) < middleSharpnessSampleData p d ε i} : Finset (Fin p)).card
      = p - 2 * d := by
  classical
  have hset : ({i | (2 + ε : ℝ) < middleSharpnessSampleData p d ε i} : Finset (Fin p))
      = Finset.univ.filter (fun i : Fin p => 0 ≤ (i : ℕ) ∧ (i : ℕ) < p - 2 * d) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [middleSharpnessSampleData]
    split_ifs with h1 h2
    · exact iff_of_true (by linarith) ⟨Nat.zero_le _, h1⟩
    · exact iff_of_false (by linarith) (by omega)
    · exact iff_of_false (by linarith) (by omega)
  rw [hset, card_filter_val_Ico p 0 (p - 2 * d) (by omega), Nat.sub_zero]

open scoped Classical in
/-- The population level set at `3` is the middle `d` indices. -/
theorem card_middleSharpnessPopulation_level (hdp : 2 * d ≤ p) :
    ({i | ((middleSharpnessPopulationData p d i : ℝ) : 𝕜) = ((3 : ℝ) : 𝕜)} :
      Finset (Fin p)).card = d := by
  classical
  have hset :
      ({i | ((middleSharpnessPopulationData p d i : ℝ) : 𝕜) = ((3 : ℝ) : 𝕜)} :
        Finset (Fin p))
      = Finset.univ.filter
          (fun i : Fin p => p - 2 * d ≤ (i : ℕ) ∧ (i : ℕ) < p - d) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      middleSharpnessPopulationData, RCLike.ofReal_inj]
    split_ifs with h1 h2
    · exact iff_of_false (by norm_num) (by omega)
    · exact iff_of_true rfl ⟨by omega, h2⟩
    · exact iff_of_false (by norm_num) (by omega)
  rw [hset, card_filter_val_Ico p (p - 2 * d) (p - d) (by omega)]
  omega

open scoped Classical in
/-- The perturbed level set at `2+ε` is the trailing `d` indices. -/
theorem card_middleSharpnessSample_level (hε : 0 < ε) (hε1 : ε < 3) (hdp : 2 * d ≤ p) :
    ({i | ((middleSharpnessSampleData p d ε i : ℝ) : 𝕜) = ((2 + ε : ℝ) : 𝕜)} :
      Finset (Fin p)).card = d := by
  classical
  have hset :
      ({i | ((middleSharpnessSampleData p d ε i : ℝ) : 𝕜) = ((2 + ε : ℝ) : 𝕜)} :
        Finset (Fin p))
      = Finset.univ.filter (fun i : Fin p => p - d ≤ (i : ℕ) ∧ (i : ℕ) < p) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, middleSharpnessSampleData,
      RCLike.ofReal_inj]
    split_ifs with h1 h2
    · exact iff_of_false (by linarith) (by omega)
    · exact iff_of_false (by linarith) (by omega)
    · exact iff_of_true rfl ⟨by omega, i.2⟩
  rw [hset, card_filter_val_Ico p (p - d) p le_rfl]
  omega

open scoped Classical in
/-- **The multiplicity of the perturbed level at the upper endpoint `ε = 3`.**

At `ε = 3` the perturbed level `2+ε` coincides with the leading level `5`, so its
level set is no longer the trailing `d` indices but the `p-d` indices outside the
middle range.  Whenever `2 * d < p` that differs from the population block's `d`,
so `correspondingEigenblock_basisDiagonal_level` no longer applies and the
construction breaks: `0 < ε < 3` is then the exact range in which the published
model means what it says, not a convenience.  (When `p = 2 * d` the count `p - d`
is `d` and nothing breaks; see the parameter-range discussion in the module
docstring.) -/
theorem card_middleSharpnessSample_level_three (hdp : 2 * d ≤ p) :
    ({i | ((middleSharpnessSampleData p d 3 i : ℝ) : 𝕜) = ((2 + 3 : ℝ) : 𝕜)} :
      Finset (Fin p)).card = p - d := by
  classical
  have hset :
      ({i | ((middleSharpnessSampleData p d 3 i : ℝ) : 𝕜) = ((2 + 3 : ℝ) : 𝕜)} :
        Finset (Fin p))
      = (Finset.univ.filter
          (fun i : Fin p => p - 2 * d ≤ (i : ℕ) ∧ (i : ℕ) < p - d))ᶜ := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      middleSharpnessSampleData, RCLike.ofReal_inj]
    split_ifs with h1 h2
    · exact iff_of_true (by norm_num) (by omega)
    · exact iff_of_false (by norm_num) (by omega)
    · exact iff_of_true (by norm_num) (by omega)
  rw [hset, Finset.card_compl, card_filter_val_Ico p (p - 2 * d) (p - d) (by omega),
    Fintype.card_fin]
  omega

variable (b : OrthonormalBasis (Fin p) 𝕜 E)

/-- The population operator of the published model. -/
noncomputable def middleSharpnessPopulation (d : ℕ) : E →ₗ[𝕜] E :=
  basisDiagonal b (middleSharpnessPopulationData p d)

/-- The perturbed operator of the published model. -/
noncomputable def middleSharpnessSample (d : ℕ) (ε : ℝ) : E →ₗ[𝕜] E :=
  basisDiagonal b (middleSharpnessSampleData p d ε)

omit [FiniteDimensional 𝕜 E] in
/-- The population block of threes is the middle index range. -/
theorem eigenspace_middleSharpnessPopulation :
    eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜) =
      b.spanIndices {i : Fin p | p - 2 * d ≤ (i : ℕ) ∧ (i : ℕ) < p - d} := by
  rw [middleSharpnessPopulation, eigenspace_basisDiagonal]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, middleSharpnessPopulationData, RCLike.ofReal_inj]
  split_ifs with h1 h2
  · exact iff_of_false (by norm_num) (by omega)
  · exact iff_of_true rfl ⟨by omega, h2⟩
  · exact iff_of_false (by norm_num) (by omega)

omit [FiniteDimensional 𝕜 E] in
/-- The perturbed block at `2+ε` is the trailing index range. -/
theorem eigenspace_middleSharpnessSample (hε : 0 < ε) (hε1 : ε < 3) :
    eigenspace (middleSharpnessSample b d ε) ((2 + ε : ℝ) : 𝕜) =
      b.spanIndices {i : Fin p | p - d ≤ (i : ℕ)} := by
  rw [middleSharpnessSample, eigenspace_basisDiagonal]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, middleSharpnessSampleData, RCLike.ofReal_inj]
  split_ifs with h1 h2
  · exact iff_of_false (by linarith) (by omega)
  · exact iff_of_false (by linarith) (by omega)
  · exact iff_of_true rfl (by omega)

/-! ## The example satisfies the theorem's hypotheses -/

omit [FiniteDimensional 𝕜 E] in
private theorem finrank_eq_of_orthonormalBasis (b : OrthonormalBasis (Fin p) 𝕜 E) :
    finrank 𝕜 E = p := by
  rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]

/-- **The two middle blocks are a corresponding eigenblock.**

Both are selected by the index range `[p-2d, p-d)` of their own sorted
eigenbasis: `p - 2d` eigenvalues lie above `3` in `Σ` and above `2+ε` in `Σ̂`,
and each level has multiplicity `d`.  This is the instance that the published
construction needs and that no top-eigenspace constructor can supply. -/
theorem correspondingEigenblock_middleSharpness (hε : 0 < ε) (hε1 : ε < 3)
    (hdp : 2 * d ≤ p) :
    CorrespondingEigenblock
      (isSymmetric_basisDiagonal b (middleSharpnessPopulationData p d))
      (isSymmetric_basisDiagonal b (middleSharpnessSampleData p d ε))
      (eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜))
      (eigenspace (middleSharpnessSample b d ε) ((2 + ε : ℝ) : 𝕜)) :=
  correspondingEigenblock_basisDiagonal_level b b _ _ (finrank_eq_of_orthonormalBasis b)
    ((card_middleSharpnessPopulation_gt hdp).trans
      (card_middleSharpnessSample_gt hε hε1 hdp).symm)
    ((card_middleSharpnessPopulation_level (𝕜 := 𝕜) hdp).trans
      (card_middleSharpnessSample_level (𝕜 := 𝕜) hε hε1 hdp).symm)

omit [FiniteDimensional 𝕜 E] in
/-- **The two blocks are orthogonal** — the point of the construction.  The
population block is the middle `d` indices and the perturbed block is the
trailing `d`. -/
theorem orthogonal_middleSharpness (hε : 0 < ε) (hε1 : ε < 3) :
    eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜) ≤
      (eigenspace (middleSharpnessSample b d ε) ((2 + ε : ℝ) : 𝕜))ᗮ := by
  rw [eigenspace_middleSharpnessPopulation b,
    eigenspace_middleSharpnessSample b hε hε1,
    OrthonormalBasis.orthogonal_spanIndices]
  refine OrthonormalBasis.spanIndices_mono b fun i hi => ?_
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  simp only [Set.mem_ofPred_eq] at hi
  omega

omit [FiniteDimensional 𝕜 E] in
/-- The population block has the paper's dimension `d`. -/
theorem finrank_eigenspace_middleSharpnessPopulation (hdp : 2 * d ≤ p) :
    finrank 𝕜 (eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜)) = d := by
  classical
  rw [eigenspace_middleSharpnessPopulation b,
    OrthonormalBasis.finrank_spanIndices_set, Set.toFinset_ofPred,
    card_filter_val_Ico p (p - 2 * d) (p - d) (by omega)]
  omega

omit [FiniteDimensional 𝕜 E] in
/-- **The population gap is two-sided: `min(5-3, 3-1) = 2`.**  The middle block
carries only the value `3`, and its complement carries `5` and `1`, both at
distance exactly `2`.  This is the feature the preprint's top-block example
lacks. -/
theorem internalGap_middleSharpness (hdp : 2 * d ≤ p) :
    InternalGap (middleSharpnessPopulation b d)
      (eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜)) 2 := by
  intro lam μ hlam hμ
  rw [eigenspace_middleSharpnessPopulation b] at hlam hμ
  have h3 : lam = 3 := by
    obtain ⟨i, hi, rfl⟩ :=
      restrictedSpectrum_basisDiagonal_subset b _ _ hlam
    simp only [Set.mem_ofPred_eq] at hi
    simp only [middleSharpnessPopulationData]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  have hout : μ = 5 ∨ μ = 1 := by
    rw [OrthonormalBasis.orthogonal_spanIndices] at hμ
    obtain ⟨i, hi, rfl⟩ :=
      restrictedSpectrum_basisDiagonal_subset b _ _ hμ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hi
    simp only [middleSharpnessPopulationData]
    by_cases h1 : (i : ℕ) < p - 2 * d
    · exact Or.inl (by rw [ite_eq_left h1])
    · exact Or.inr (by rw [ite_eq_right h1, ite_eq_right (by omega)])
  rw [h3]
  rcases hout with h | h <;> rw [h] <;> norm_num

/-- **The perturbation has operator norm `1 + ε`.**  The displacements are `0`
on the leading block, `-1` on the middle block and `1 + ε` on the trailing
block. -/
theorem opNorm_middleSharpness_perturbation (hε : 0 < ε) (hd : 1 ≤ d)
    (hdp : 2 * d ≤ p) :
    ‖(middleSharpnessSample b d ε -
        middleSharpnessPopulation b d).toContinuousLinearMap‖ = 1 + ε := by
  have hp0 : 0 < p := by omega
  rw [middleSharpnessSample, middleSharpnessPopulation, basisDiagonal_sub]
  refine norm_basisDiagonal_eq b _ (by linarith) ?_ (i₀ := ⟨p - 1, by omega⟩) ?_
  · intro i
    simp only [Pi.sub_apply, middleSharpnessSampleData, middleSharpnessPopulationData,
      abs_le]
    split_ifs <;> constructor <;> linarith
  · simp only [Pi.sub_apply, middleSharpnessSampleData, middleSharpnessPopulationData]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    rw [show (2 + ε) - 1 = 1 + ε by ring, abs_of_pos (by linarith)]

/-! ## The achieved distances -/

/-- **`‖sin Θ(V̂, V)‖_F = √d`.**  The two blocks are disjoint coordinate ranges,
so every principal angle is a right angle. -/
theorem sinThetaFrobenius_middleSharpness (hε : 0 < ε) (hε1 : ε < 3)
    (hdp : 2 * d ≤ p) :
    sinThetaFrobenius (eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜))
        (eigenspace (middleSharpnessSample b d ε) ((2 + ε : ℝ) : 𝕜)) =
      Real.sqrt d := by
  classical
  rw [eigenspace_middleSharpnessPopulation b,
    eigenspace_middleSharpnessSample b hε hε1,
    sinThetaFrobenius_spanIndices_of_subset_compl b (finrank_eq_of_orthonormalBasis b)
      _ _ (fun i hi => by simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hi ⊢; omega)]
  congr 1
  rw [Set.toFinset_ofPred, card_filter_val_Ico p (p - 2 * d) (p - d) (by omega)]
  exact_mod_cast (show p - d - (p - 2 * d) = d by omega)

omit [FiniteDimensional 𝕜 E] in
/-- **Every aligned orthonormal pair is at distance exactly `√(2d)`.**  This is
the paper's `‖V̂O − V‖_F = √(2d)` for every `O ∈ O(d)`. -/
theorem dist_middleSharpness_aligned (hε : 0 < ε) (hε1 : ε < 3)
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (hspanU : Submodule.span 𝕜 (Set.range u) =
      eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜))
    (hspanV : Submodule.span 𝕜 (Set.range v) =
      eigenspace (middleSharpnessSample b d ε) ((2 + ε : ℝ) : 𝕜)) :
    Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) = Real.sqrt (2 * d) := by
  rw [sum_sq_norm_sub_eq_of_le_orthogonal
    (orthogonal_middleSharpness (b := b) (d := d) (ε := ε) hε hε1) hu hv
    (fun i => hspanU ▸ Submodule.subset_span ⟨i, rfl⟩)
    (fun i => hspanV ▸ Submodule.subset_span ⟨i, rfl⟩)]

/-! ## The sharpness statement -/

/-- **Yu--Wang--Samworth Section 2, published middle-block sharpness.**

For every `0 < ε < 3` the model satisfies the hypotheses of
`YuWangSamworth2015.yuWangSamworth_alignedBasis_le` — a corresponding eigenblock
(`correspondingEigenblock_middleSharpness`) of dimension `d`
(`finrank_eigenspace_middleSharpnessPopulation`) with the genuinely two-sided
population gap `min(5-3, 3-1) = 2` (`internalGap_middleSharpness`) — and this
theorem is the resulting comparison: *every* aligned orthonormal pair of the two
blocks realizes distance exactly `√(2d)`, against a bound of `√(2d)(1+ε)`.

Letting `ε ↓ 0` shows the aligned-basis constant `2^{3/2}` and the `√d` dimension
dependence cannot be uniformly improved. -/
theorem yuWangSamworth_sharpness_middleBlock (hε : 0 < ε) (hε1 : ε < 3) (hd : 1 ≤ d)
    (hdp : 2 * d ≤ p) {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (hspanU : Submodule.span 𝕜 (Set.range u) =
      eigenspace (middleSharpnessPopulation b d) ((3 : ℝ) : 𝕜))
    (hspanV : Submodule.span 𝕜 (Set.range v) =
      eigenspace (middleSharpnessSample b d ε) ((2 + ε : ℝ) : 𝕜)) :
    Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) = Real.sqrt (2 * d) ∧
      2 * Real.sqrt 2 *
          (Real.sqrt d * ‖(middleSharpnessSample b d ε -
            middleSharpnessPopulation b d).toContinuousLinearMap‖) / 2 =
        Real.sqrt (2 * d) * (1 + ε) := by
  refine ⟨dist_middleSharpness_aligned b hε hε1 hu hv hspanU hspanV, ?_⟩
  rw [opNorm_middleSharpness_perturbation b hε hd hdp,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  ring

end Model

end DavisKahanTheory
end YuWangSamworth2015
