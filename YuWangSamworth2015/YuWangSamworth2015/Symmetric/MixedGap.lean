/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.GroundedImports

/-!
# The mixed separation: Theorem 1's denominator, and why the paper replaces it

Two pieces of the published article that are about the *hypotheses* of the
statistical Davis--Kahan theorem rather than about a new inequality.

## Section 1, the numerical illustration

Immediately after Theorem 1 the article exhibits

`Σ = diag(50,40,30,20,10)`, `Σ̂ = diag(54,37,32,23,21)`,

whose point is that Theorem 1's mixed separation

`δ = inf{|λ̂ − λ| : λ ∈ [λ_s, λ_r], λ̂ ∈ (−∞, λ̂_{s+1}] ∪ [λ̂_{r-1}, ∞)}`

can vanish while the population eigenvalues are as well separated as one likes.

The article takes the eigenvectors for the second, third and fourth largest
eigenvalues, so `r = 2` and `s = 4` in its one-based indexing — the zero-based
Lean block `1, 2, 3`.  The population block interval is then `[λ₄, λ₂] = [20, 40]`
and the exterior rays are `(−∞, λ̂₅] = (−∞, 21]` and `[λ̂₁, ∞) = [54, ∞)`.  Since
`λ₄ = 20` lies inside the lower ray, `δ = 0` and Theorem 1 says nothing at all —
while the population gap is `min(λ₁ − λ₂, λ₄ − λ₅) = 10` and Theorem 2 applies
unconditionally.

Note that `δ` ranges over the two exterior *rays*, not over the sample
eigenvalues, so a single population eigenvalue reaching a ray endpoint is enough
to collapse it.

## Section 3, the audit of statistical applications

The article's diagnosis of the literature is that authors apply a mixed-gap
theorem and then invoke Weyl's inequality to recover a population-gap
denominator, and that variants which appear to assume only a population gap can
hide a requirement that the two matrices have the same number of eigenvalues in
the selected interval.  Those are claims about other papers, and as such are not
formalizable; their deterministic mathematical content is, and is proved here:

* `YuWangSamworth2015.mixedGap_of_populationGap_weyl` is the recovery step, and it costs the
  side condition `ε < Δ`;
* `yuWangSamworth_weylRecovered_le_populationGap_bound` shows that on the event
  `2ε ≤ Δ` the recovered route lands exactly on Theorem 2's constant, so the
  difference between the two routes is the event, not the bound;
* the Section 1 model is a witness that the event is not automatic — there
  `ε = 11 > 10 = Δ`, so the recovery yields nothing;
* and in that same model the fifth sample eigenvalue has crossed into the
  interval spanned by the article's population block while its population
  counterpart has not, so the hidden interval-counting requirement fails there
  too.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace BigOperators

/-! ## The mixed separation of Theorem 1 -/

/-- The set of distances whose infimum is Theorem 1's mixed separation `δ`.

`a` and `b` bound the population block, `[λ_s, λ_r]`; `lo` is `λ̂_{s+1}` and `hi`
is `λ̂_{r-1}`, so the sample side ranges over the two *rays* outside the block.
Ranging over rays rather than over the sample eigenvalues themselves is what
makes `δ` fragile: a single population eigenvalue that fails to separate from a
ray endpoint sets it to zero. -/
def mixedSeparationSet (a b lo hi : ℝ) : Set ℝ :=
  {t | ∃ lam ∈ Set.Icc a b, ∃ hat ∈ Set.Iic lo ∪ Set.Ici hi, t = |hat - lam|}

/-- Theorem 1's mixed population/sample separation `δ`. -/
noncomputable def mixedSeparation (a b lo hi : ℝ) : ℝ :=
  sInf (mixedSeparationSet a b lo hi)

/-- **The mixed separation vanishes as soon as the block reaches the lower ray.**
If the bottom of the population block is at or below `λ̂_{s+1}` then the
infimum is attained at distance zero. -/
theorem mixedSeparation_eq_zero_of_le {a b lo hi : ℝ} (hab : a ≤ b) (h : a ≤ lo) :
    mixedSeparation a b lo hi = 0 := by
  have hmem : (0 : ℝ) ∈ mixedSeparationSet a b lo hi :=
    ⟨a, ⟨le_rfl, hab⟩, a, Or.inl h, by simp⟩
  have hlb : ∀ t ∈ mixedSeparationSet a b lo hi, (0 : ℝ) ≤ t := by
    rintro t ⟨lam, -, hat, -, rfl⟩
    exact abs_nonneg _
  exact le_antisymm (csInf_le ⟨0, fun t ht => hlb t ht⟩ hmem)
    (le_csInf ⟨0, hmem⟩ hlb)

/-! ## Section 3: what the two-step route costs -/

/-- **On the event the Weyl step needs, the recovered bound is Theorem 2's.**

`c/(Δ − ε) ≤ 2c/Δ` whenever `2ε ≤ Δ`.  Reading it with `c = ‖Σ̂ − Σ‖_F`: the
literature's mixed-gap-then-Weyl route reaches, on the event `‖E‖_op ≤ Δ/2`,
the very bound `2‖E‖_F/Δ` that `YuWangSamworth2015.yuWangSamworth_sinTheta_frame_le`
proves with no event at all.  What Theorem 2 removes is the hypothesis, not the
constant. -/
theorem yuWangSamworth_weylRecovered_le_populationGap_bound {c Δ ε : ℝ}
    (hc : 0 ≤ c) (hΔ : 0 < Δ) (h : 2 * ε ≤ Δ) :
    c / (Δ - ε) ≤ 2 * c / Δ := by
  have hpos : 0 < Δ - ε := by linarith
  rw [div_le_div_iff₀ hpos hΔ]
  nlinarith

/-! ## The Section 1 model -/

/-- `Σ = diag(50,40,30,20,10)`, the population covariance of the published
Section 1 illustration. -/
def section1PopulationData : Fin 5 → ℝ := fun i => 50 - 10 * (i : ℕ)

/-- `Σ̂ = diag(54,37,32,23,21)`, the perturbed covariance of that illustration.
Its fifth eigenvalue `21` exceeds the population's fourth, `20`, which is what
destroys Theorem 1's separation. -/
def section1SampleData : Fin 5 → ℝ := fun i =>
  if (i : ℕ) = 0 then 54 else if (i : ℕ) = 1 then 37 else
    if (i : ℕ) = 2 then 32 else if (i : ℕ) = 3 then 23 else 21

/-- **Theorem 1's separation vanishes at the article's block `r = 2`, `s = 4`.**

The block interval is `[λ₄, λ₂] = [20, 40]` and the lower exterior ray is
`(−∞, λ̂₅] = (−∞, 21]`; the two meet, so the infimum defining `δ` is `0` and
Theorem 1 has no content there, however large the population gaps are.  The
arguments are the zero-based Lean indices of the one-based `λ₄`, `λ₂`, `λ̂₅` and
`λ̂₁`. -/
theorem section1_mixedSeparation_eq_zero :
    mixedSeparation (section1PopulationData 3) (section1PopulationData 1)
      (section1SampleData 4) (section1SampleData 0) = 0 :=
  mixedSeparation_eq_zero_of_le
    (by norm_num [section1PopulationData])
    (by norm_num [section1PopulationData, section1SampleData])

/-- **The population gap at the same block is `10`.**  `min(λ₁ − λ₂, λ₄ − λ₅) =
min(50 − 40, 20 − 10)`: the population eigenvalues are well separated, which is
the contrast the illustration is making. -/
theorem section1_populationGap :
    min (section1PopulationData 0 - section1PopulationData 1)
      (section1PopulationData 3 - section1PopulationData 4) = 10 := by
  norm_num [section1PopulationData]

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable (b : OrthonormalBasis (Fin 5) 𝕜 E)

/-- The population operator of the Section 1 illustration. -/
noncomputable def section1Population : E →ₗ[𝕜] E :=
  basisDiagonal b section1PopulationData

/-- The perturbed operator of the Section 1 illustration. -/
noncomputable def section1Sample : E →ₗ[𝕜] E :=
  basisDiagonal b section1SampleData

omit [FiniteDimensional 𝕜 E] in
/-- The fourth coordinate is the eigenspace at `20`.  This is the singleton block
`r = s = 4`, which is not the block the article selects; it is recorded because
the two operator-level facts below are stated at it. -/
theorem eigenspace_section1Population :
    eigenspace (section1Population b) ((20 : ℝ) : 𝕜) =
      b.spanIndices {i : Fin 5 | (i : ℕ) = 3} := by
  rw [section1Population, eigenspace_basisDiagonal]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, RCLike.ofReal_inj]
  fin_cases i <;> norm_num [section1PopulationData]

omit [FiniteDimensional 𝕜 E] in
/-- **The population gap of the singleton block `r = s = 4` is `10`, at the
operator level.**  The block carries only `20`, and its complement carries `50`,
`40`, `30` and `10`, each at distance at least `10`.  So
`YuWangSamworth2015.yuWangSamworth_alignedBasis_le` applies to this pair while
Theorem 1 does not.  `internalGap_section1_paperBlock` is the same fact at the
block the article actually selects. -/
theorem internalGap_section1 :
    InternalGap (section1Population b)
      (eigenspace (section1Population b) ((20 : ℝ) : 𝕜)) 10 := by
  intro lam μ hlam hμ
  rw [eigenspace_section1Population] at hlam hμ
  have h20 : lam = 20 := by
    obtain ⟨i, hi, rfl⟩ := restrictedSpectrum_basisDiagonal_subset b _ _ hlam
    simp only [Set.mem_ofPred_eq] at hi
    fin_cases i <;> simp_all [section1PopulationData]
    norm_num
  rw [OrthonormalBasis.orthogonal_spanIndices] at hμ
  obtain ⟨i, hi, rfl⟩ := restrictedSpectrum_basisDiagonal_subset b _ _ hμ
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hi
  rw [h20]
  fin_cases i <;> simp_all [section1PopulationData] <;> norm_num

omit [FiniteDimensional 𝕜 E] in
/-- **The population gap of the article's block `r = 2`, `s = 4` is `10`, at the
operator level.**

The block carries `40`, `30` and `20`; its complement carries `50` and `10`; the
closest pair is at distance `10`.  So the population-gap theorems apply to this
pair at the article's own block, while Theorem 1 does not. -/
theorem internalGap_section1_paperBlock :
    InternalGap (section1Population b)
      (b.spanIndices {i : Fin 5 | 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 3}) 10 := by
  intro lam μ hlam hμ
  rw [section1Population] at hlam hμ
  obtain ⟨i, hi, rfl⟩ := restrictedSpectrum_basisDiagonal_subset b _ _ hlam
  rw [OrthonormalBasis.orthogonal_spanIndices] at hμ
  obtain ⟨j, hj, rfl⟩ := restrictedSpectrum_basisDiagonal_subset b _ _ hμ
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all [section1PopulationData] <;> norm_num

/-- **The perturbation has operator norm `11`.**  The largest displacement is at
the fifth coordinate, where `Σ̂` reads `21` against `Σ`'s `10`. -/
theorem opNorm_section1_perturbation :
    ‖(section1Sample b - section1Population b).toContinuousLinearMap‖ = 11 := by
  rw [section1Sample, section1Population, basisDiagonal_sub]
  refine norm_basisDiagonal_eq b _ (by norm_num) ?_ (i₀ := 4) ?_
  · intro i
    fin_cases i <;>
      norm_num [section1SampleData, section1PopulationData]
  · norm_num [section1SampleData, section1PopulationData]

/-- **The Weyl recovery fails on the paper's own example.**

`YuWangSamworth2015.mixedGap_of_populationGap_weyl` turns the population gap `Δ = 10` into a
mixed gap `Δ − ε`, and here `ε = 11`: the recovered separation is negative, so
the two-step route yields nothing whatever.  Theorem 2 is unaffected, by
`internalGap_section1`. -/
theorem section1_weylRecovery_fails :
    (10 : ℝ) - ‖(section1Sample b - section1Population b).toContinuousLinearMap‖ < 0 := by
  rw [opNorm_section1_perturbation]
  norm_num

/-- **The hidden interval-counting requirement fails at the article's block.**

The article's block is `r = 2`, `s = 4`, spanning the interval `[λ₄, λ₂] =
[20, 40]`, which contains exactly the three population eigenvalues `40`, `30`,
`20`.  The fifth sample eigenvalue `λ̂₅ = 21` has crossed into that interval while
its population counterpart `λ₅ = 10` lies outside it, so `Σ̂` has one more
eigenvalue there than `Σ`.  A spectral-clustering-style statement that assumes a
population gap *and* equal interval counts is therefore assuming something this
example violates, which is the article's Section 3 point. -/
theorem section1_sample_crosses_into_paperBlock :
    section1SampleData 4 ∈
        Set.Icc (section1PopulationData 3) (section1PopulationData 1) ∧
      section1PopulationData 4 ∉
        Set.Icc (section1PopulationData 3) (section1PopulationData 1) := by
  constructor
  · simp only [Set.mem_Icc]
    norm_num [section1SampleData, section1PopulationData]
  · simp only [Set.mem_Icc, not_and]
    norm_num [section1PopulationData]

/-- **No sample eigenvalue lies in the singleton block `[λ₄, λ₄]`.**  An
auxiliary observation on the same data, at the block `r = s = 4` rather than the
article's `r = 2`, `s = 4`. -/
theorem section1_no_sample_eigenvalue_in_block (i : Fin 5) :
    section1SampleData i ∉ Set.Icc (section1PopulationData 3) (section1PopulationData 3) := by
  simp only [Set.mem_Icc, not_and]
  fin_cases i <;> norm_num [section1SampleData, section1PopulationData]

end DavisKahanTheory
end YuWangSamworth2015
