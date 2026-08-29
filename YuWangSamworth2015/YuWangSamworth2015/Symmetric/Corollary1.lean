/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.GroundedImports

/-!
# Corollary 1 with the source's neighbouring-eigenvalue gap

`YuWangSamworth2015.yuWangSamworth_eigenvector_frame_sinTheta_le` and
`YuWangSamworth2015.yuWangSamworth_eigenvector_real_le` prove Corollary 1 with the
*intrinsic* separation hypothesis `Δ ≤ |λⱼ − λ_k|` for every `k ≠ j`.  The source
assumes only

`Δⱼ = min(λ_{j-1} − λⱼ, λⱼ − λ_{j+1}) > 0`,

with `λ_0 = +∞` and `λ_{p+1} = −∞`.  For a sorted spectrum the two are the same
condition, and `YuWangSamworth2015.OrderedBlockBoundaryGap.gap_of_singleton` is the
implication; this module records the corollary as printed.

## Sample degeneracy

The reason the corollary is stated for *arbitrary* unit eigenvectors is that
Yu, Wang and Samworth assume nothing about `Σ̂`'s spectrum, so `λ̂ⱼ` may be
repeated and `v̂ⱼ` is then not determined.  `yuWangSamworth_corollary1_scalarSample`
is the extreme witness: for `Σ = diag(1, 0)` and `Σ̂ = I/2` every unit vector of
the plane is an admissible `v̂₁`, and the corollary bounds the angle for each of
them.  A formulation that pinned `v̂₁` to a chosen eigenbasis of `Σ̂` would say
nothing about all but one of them.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace RealInnerProductSpace BigOperators

section General

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Corollary 1, first display, exactly as printed.**

`sin Θ(v̂ⱼ, vⱼ) ≤ 2 ‖Σ̂ − Σ‖_op / Δⱼ` for arbitrary unit eigenvectors of `Σ` and
`Σ̂` at the `j`-th sorted eigenvalue, assuming only the population separation
`Δⱼ ≤ min(λ_{j-1} − λⱼ, λⱼ − λ_{j+1})` — and nothing whatever about `Σ̂`'s
spectrum, so `λ̂ⱼ` may be repeated. -/
theorem yuWangSamworth_corollary1_sinTheta_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {j : Fin n} {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hAu : A u = (hA.eigenvalues hn j : 𝕜) • u)
    (hBv : B v = (hB.eigenvalues hn j : 𝕜) • v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn (j : ℕ) (j : ℕ) Δ) :
    sinThetaFrobenius (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}) ≤
      2 * ‖(B - A).toContinuousLinearMap‖ / Δ :=
  yuWangSamworth_eigenvector_frame_sinTheta_le hu hv hAu hBv hΔ
    fun k hk => hgap.gap_of_singleton k hk

end General

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Corollary 1, second display, exactly as printed.**

Real symmetric `Σ`, `Σ̂`; unit eigenvectors `v`, `v̂` at the `j`-th sorted
eigenvalues; the orientation `v̂ᵀ v ≥ 0`; the population separation
`Δⱼ ≤ min(λ_{j-1} − λⱼ, λⱼ − λ_{j+1})`; and no sample separation.  Then

`‖v̂ − v‖ ≤ 2^{3/2} ‖Σ̂ − Σ‖_op / Δⱼ`. -/
theorem yuWangSamworth_corollary1_real_le
    {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank ℝ F = n} {j : Fin n} {u v : F}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hAu : A u = (hA.eigenvalues hn j : ℝ) • u)
    (hBv : B v = (hB.eigenvalues hn j : ℝ) • v)
    (hsign : 0 ≤ ⟪v, u⟫)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn (j : ℕ) (j : ℕ) Δ) :
    ‖v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ :=
  yuWangSamworth_eigenvector_real_le hu hv hAu hBv hsign hΔ
    fun k hk => hgap.gap_of_singleton k hk

end Real

/-! ## The sample-degeneracy witness -/

section Degenerate

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- `Σ = diag(1, 0)`: a population covariance with a simple leading
eigenvalue. -/
def scalarSamplePopulationData : Fin 2 → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

omit [FiniteDimensional 𝕜 E] in
private theorem finrank_eq_two (bb : OrthonormalBasis (Fin 2) 𝕜 E) :
    finrank 𝕜 E = 2 := by
  rw [Module.finrank_eq_card_basis bb.toBasis, Fintype.card_fin]

variable (b : OrthonormalBasis (Fin 2) 𝕜 E)

/-- The population operator of the degeneracy witness. -/
noncomputable def scalarSamplePopulation : E →ₗ[𝕜] E :=
  basisDiagonal b scalarSamplePopulationData

/-- `Σ̂ = I/2`: a sample covariance whose spectrum is a single eigenvalue of full
multiplicity, so no sample eigenvector is determined. -/
noncomputable def scalarSampleSample : E →ₗ[𝕜] E :=
  basisDiagonal b (fun _ : Fin 2 => (1 / 2 : ℝ))

open scoped Classical in
private theorem card_scalarSamplePopulation_gt_one :
    ({j | (1 : ℝ) < scalarSamplePopulationData j} : Finset (Fin 2)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  fin_cases i <;> norm_num [scalarSamplePopulationData]

open scoped Classical in
private theorem card_scalarSamplePopulation_level_one :
    ({j | ((scalarSamplePopulationData j : ℝ) : 𝕜) = ((1 : ℝ) : 𝕜)} :
      Finset (Fin 2)).card = 1 := by
  classical
  have hset : ({j | ((scalarSamplePopulationData j : ℝ) : 𝕜) = ((1 : ℝ) : 𝕜)} :
      Finset (Fin 2)) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      RCLike.ofReal_inj]
    fin_cases i <;> norm_num [scalarSamplePopulationData]
  rw [hset, Finset.card_singleton]

/-- **The leading sorted eigenvalue of `diag(1, 0)` is `1`.** -/
theorem eigenvalues_scalarSamplePopulation_zero :
    (isSymmetric_basisDiagonal b scalarSamplePopulationData).eigenvalues
      (finrank_eq_two b) 0 = 1 := by
  classical
  refine eigenvalues_basisDiagonal_eq_of_card b _ (finrank_eq_two b) 1 0 ?_ ?_
  · rw [card_scalarSamplePopulation_gt_one]
    exact Nat.zero_le _
  · rw [card_scalarSamplePopulation_gt_one,
      card_scalarSamplePopulation_level_one (𝕜 := 𝕜)]
    norm_num

/-- **Every sorted eigenvalue of `I/2` is `1/2`**, so every unit vector is an
eigenvector at the sample index the corollary selects. -/
theorem eigenvalues_scalarSampleSample (i : Fin 2) :
    (isSymmetric_basisDiagonal b fun _ : Fin 2 => (1 / 2 : ℝ)).eigenvalues
      (finrank_eq_two b) i = 1 / 2 :=
  eigenvalues_basisDiagonal_const b _ (finrank_eq_two b) i

/-- The perturbation `Σ̂ − Σ = diag(-1/2, 1/2)` has operator norm `1/2`. -/
theorem opNorm_scalarSample_perturbation :
    ‖(scalarSampleSample b - scalarSamplePopulation b).toContinuousLinearMap‖
      = 1 / 2 := by
  rw [scalarSampleSample, scalarSamplePopulation, basisDiagonal_sub]
  refine norm_basisDiagonal_eq b _ (by norm_num) ?_ (i₀ := 1) ?_
  · intro i
    fin_cases i <;> norm_num [scalarSamplePopulationData]
  · norm_num [scalarSamplePopulationData]

/-- **Corollary 1 applies to an arbitrary unit sample eigenvector.**

`Σ = diag(1, 0)` has population gap `Δ₁ = λ₁ − λ₂ = 1` (the upper boundary gap
is `λ₀ = +∞`, so it imposes nothing), and `Σ̂ = I/2` is totally degenerate: *every*
unit `w` satisfies `Σ̂ w = λ̂₁ w`.  The corollary bounds the angle between the
population eigenvector and each of them by
`2 ‖Σ̂ − Σ‖_op / Δ₁ = 1`.

This is the case a formulation pinning `v̂` to a chosen eigenbasis of `Σ̂` cannot
express, and it is why the sample side must be an arbitrary ordered eigenframe
rather than `spanIndices` of a fixed basis. -/
theorem yuWangSamworth_corollary1_scalarSample (w : E) (hw : ‖w‖ = 1) :
    sinThetaFrobenius (Submodule.span 𝕜 {b 0}) (Submodule.span 𝕜 {w}) ≤ 1 := by
  classical
  have hn : finrank 𝕜 E = 2 := finrank_eq_two b
  have hb0 : ‖b 0‖ = 1 := b.orthonormal.norm_eq_one 0
  have hAu : scalarSamplePopulation b (b 0) =
      ((isSymmetric_basisDiagonal b scalarSamplePopulationData).eigenvalues hn 0 : 𝕜)
        • b 0 := by
    rw [scalarSamplePopulation, basisDiagonal_apply_basis,
      eigenvalues_scalarSamplePopulation_zero b]
    norm_num [scalarSamplePopulationData]
  have hBv : scalarSampleSample b w =
      ((isSymmetric_basisDiagonal b fun _ : Fin 2 => (1 / 2 : ℝ)).eigenvalues hn 0 : 𝕜)
        • w := by
    rw [scalarSampleSample, basisDiagonal_const, eigenvalues_scalarSampleSample b]
  -- The population boundary gap at `j = 0` is `λ₁ − λ₂ = 1`.
  have hgap : OrderedBlockBoundaryGap
      (isSymmetric_basisDiagonal b scalarSamplePopulationData) hn 0 0 1 := by
    refine orderedBlockBoundaryGap_iff.mpr ⟨fun q p hq _ => absurd hq (by omega), ?_⟩
    intro q p hq hp
    have hq0 : q = 0 := Fin.ext (by omega)
    have hp1 : p = 1 := Fin.ext (by omega)
    rw [hq0, hp1, eigenvalues_scalarSamplePopulation_zero b]
    have hp1' : (isSymmetric_basisDiagonal b scalarSamplePopulationData).eigenvalues hn 1
        = 0 := by
      refine eigenvalues_basisDiagonal_eq_of_card b _ hn 0 1 ?_ ?_
      · have hcard : ({j | (0 : ℝ) < scalarSamplePopulationData j} : Finset (Fin 2))
            = {0} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          fin_cases i <;> norm_num [scalarSamplePopulationData]
        rw [hcard, Finset.card_singleton]
        simp
      · have hcard : ({j | (0 : ℝ) < scalarSamplePopulationData j} : Finset (Fin 2))
            = {0} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          fin_cases i <;> norm_num [scalarSamplePopulationData]
        have hlevel : ({j | ((scalarSamplePopulationData j : ℝ) : 𝕜) = ((0 : ℝ) : 𝕜)} :
            Finset (Fin 2)) = {1} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            RCLike.ofReal_inj]
          fin_cases i <;> norm_num [scalarSamplePopulationData]
        rw [hcard, hlevel, Finset.card_singleton, Finset.card_singleton]
        norm_num
    rw [hp1']
    norm_num
  have hkey := yuWangSamworth_corollary1_sinTheta_le (hn := hn) (j := 0)
    hb0 hw hAu hBv (by norm_num) hgap
  rw [opNorm_scalarSample_perturbation b] at hkey
  refine hkey.trans ?_
  norm_num

end Degenerate

end DavisKahanTheory
end YuWangSamworth2015
