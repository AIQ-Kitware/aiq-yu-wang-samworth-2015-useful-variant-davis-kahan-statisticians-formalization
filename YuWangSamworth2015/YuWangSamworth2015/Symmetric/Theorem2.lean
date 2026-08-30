/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import YuWangSamworth2015.Core.ConsecutiveBlock
public import YuWangSamworth2015.Core.Procrustes

/-! # Yu--Wang--Samworth Theorem 2

This module is the source-facing surface for the paper's headline population-gap
result.  The reusable sine-distance notion remains in `ForTauCeti`; the
population-gap residual argument, source indexing, and alignment statement are
owned by the application package.
-/

public section

namespace YuWangSamworth2015
open TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ## Theorem 2 with the source's indexing

The four statements below fix `r ≤ s` and `d = s − r + 1`, written `r + d = s + 1`
to avoid truncated subtraction, and take the gap in the printed form
`Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`.  The paper's `r ≤ s` is exactly `1 ≤ d`
here and is not needed for the conclusion: at `d = 0` the frames are empty and
the bound is trivial, so it is not imposed. -/

/-- **Yu--Wang--Samworth Theorem 2, first conclusion, as printed.**

`r ≤ s`, `d = s − r + 1`, `V` and `V̂` arbitrary orthonormal eigenframes at the
indices `r, …, s`, no sample separation whatever, and only the two-sided
*population* boundary gap `Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`.  Then

`‖sin Θ(V̂, V)‖_F ≤ 2 min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`.

Indices are `0`-based, so `s + 1 ≤ n` is the paper's `s ≤ p`. -/
theorem yuWangSamworth_sinTheta_block_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ :=
  yuWangSamworth_sinTheta_frame_le hu hv hΔ (hgap.indexGap _ hd)

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, as printed.**
With the same hypotheses there is an orthogonal `Ô` on the block's coordinate
space with `‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`. -/
theorem yuWangSamworth_alignedFrame_block_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
              (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ :=
  yuWangSamworth_alignedFrame_le hu hv hΔ (hgap.indexGap _ hd)

/-- **The residual form of Theorem 2 with the source's indexing.**
`Δ ‖sin Θ(V̂, V)‖_F ≤ ‖V̂ Λ − Σ V̂‖_F`, with `Λ = diag(λ_r, …, λ_s)` the
*population* eigenvalues of the block. -/
theorem yuWangSamworth_sinTheta_block_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ≤
      Real.sqrt (∑ i,
        ‖(hA.eigenvalues hn (consecutiveEmb (hd.trans_le hsn) i) : 𝕜) • v i - A (v i)‖ ^ 2)
        / Δ :=
  yuWangSamworth_sinTheta_le_residual hu hv hΔ (hgap.indexGap _ hd)

/-- **The residual form of the aligned conclusion with the source's indexing.**
`‖V̂ Ô − V‖_F ≤ 2^{1/2} ‖V̂ Λ − Σ V̂‖_F / Δ`. -/
theorem yuWangSamworth_alignedFrame_block_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          Real.sqrt 2 *
            Real.sqrt (∑ i,
              ‖(hA.eigenvalues hn (consecutiveEmb (hd.trans_le hsn) i) : 𝕜) • v i
                - A (v i)‖ ^ 2) / Δ :=
  yuWangSamworth_alignedFrame_le_residual hu hv hΔ (hgap.indexGap _ hd)

/-! ## The fully literal real statement -/

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, exactly as printed.**

Real symmetric `Σ`, `Σ̂`; a block `r, …, s` with `d = s − r + 1`; arbitrary
orthonormal eigenframes `V`, `V̂` at those indices with no sample separation; and
the two-sided population boundary gap `Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`.
Then there is an orthogonal matrix `Ô ∈ O(d)` with

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`,

the `i`-th column of `V̂ Ô` being `∑ⱼ Ôⱼᵢ v̂ⱼ`.  Every symbol of the printed
conclusion appears here; the `RCLike` forms above are its generalizations. -/
theorem yuWangSamworth_alignedFrame_block_real_le
    {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank ℝ F = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → F}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • v j) - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius ℝ F (B - A)) / Δ :=
  yuWangSamworth_alignedFrame_real_le hu hv hΔ (hgap.indexGap _ hd)

end Real

/-! ## Paper-facing Theorem 2 surface

The declarations in this section are intentionally written for semantic review.
They specialize the source theorem to `Real^p`, use the source variable names,
and state the block conditions as `r ≤ s`, `s < p`, and `d = s - r + 1`.
The two small predicates below hide only representation details: their definitions
are meant to be printed next to the theorem by the semantic-alignment review.
-/

section PaperFacing

/-- A source-shaped eigenvector block for Theorem 2.

`V` has orthonormal columns, and column `i` is an eigenvector of `Sigma` for the
`(r+i)`-th eigenvalue in nonincreasing order.  Lean indices are zero-based, so
this is the paper's block `r,...,s` after subtracting one from its indices. -/
def IsEigenvectorBlock
    {p d r s : Nat}
    (Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V : Fin d → EuclideanSpace Real (Fin p)) : Prop :=
  Orthonormal Real V ∧
    ∀ i, Sigma (V i) =
      hSigma.eigenvalues
        (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp)
        (Fin.mk (r + (i : Nat)) (by omega)) • V i

/-- Characteristic form of the paper-facing eigenvector-block predicate. -/
theorem isEigenvectorBlock_iff
    {p d r s : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric}
    {hr : r ≤ s} {hs : s < p} {hd : d = s - r + 1}
    {V : Fin d → EuclideanSpace Real (Fin p)} :
    IsEigenvectorBlock Sigma hSigma hr hs hd V ↔
      Orthonormal Real V ∧
        ∀ i, Sigma (V i) =
          hSigma.eigenvalues
            (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp)
            (Fin.mk (r + (i : Nat)) (by omega)) • V i :=
  Iff.rfl

namespace IsEigenvectorBlock

/-- Bridge from the paper-facing eigenvector-block predicate to the general
ordered-eigenframe interface used by the proof. -/
theorem toIsOrderedEigenframe
    {p d r s : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric}
    {hr : r ≤ s} {hs : s < p} {hd : d = s - r + 1}
    {V : Fin d → EuclideanSpace Real (Fin p)}
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V) :
    IsOrderedEigenframe hSigma
      (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp)
      (consecutiveEmb (show r + d ≤ p by omega)) V := by
  simp only [IsEigenvectorBlock] at hV
  apply isOrderedEigenframe_iff.mpr
  refine { orthonormal := hV.1, apply_eq := ?_ }
  intro i
  have hidx :
      consecutiveEmb (show r + d ≤ p by omega) i =
        Fin.mk (r + (i : Nat)) (by omega) := by
    apply Fin.ext
    rfl
  rw [hidx]
  exact hV.2 i

end IsEigenvectorBlock

/-- The source's population-only boundary gap around `r,...,s`.

At an interior boundary this says
`Delta ≤ lambda_(r-1) - lambda_r` and
`Delta ≤ lambda_s - lambda_(s+1)`.  At the first or last index the
corresponding quantified clause is vacuous, implementing the paper's
`lambda_0 = +infinity` and `lambda_(p+1) = -infinity` conventions.  Only the
population operator `Sigma` occurs here; there is no sample eigengap. -/
def PopulationBoundaryGap
    {p : Nat}
    (Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (r s : Nat) (Delta : Real) : Prop :=
  (∀ q j : Fin p, (q : Nat) + 1 = r → (j : Nat) = r →
      Delta ≤
        hSigma.eigenvalues
            (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q -
          hSigma.eigenvalues
            (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j) ∧
    (∀ j q : Fin p, (j : Nat) = s → (q : Nat) = s + 1 →
      Delta ≤
        hSigma.eigenvalues
            (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j -
          hSigma.eigenvalues
            (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q)

/-- Characteristic form of the paper-facing population boundary gap. -/
theorem populationBoundaryGap_iff
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real} :
    PopulationBoundaryGap Sigma hSigma r s Delta ↔
      ((∀ q j : Fin p, (q : Nat) + 1 = r → (j : Nat) = r →
          Delta ≤
            hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q -
              hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j) ∧
        (∀ j q : Fin p, (j : Nat) = s → (q : Nat) = s + 1 →
          Delta ≤
            hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j -
              hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q)) :=
  Iff.rfl

namespace PopulationBoundaryGap

/-- Bridge from the paper-facing gap predicate to the implementation predicate. -/
theorem toOrderedBlockBoundaryGap
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real}
    (hgap : PopulationBoundaryGap Sigma hSigma r s Delta) :
    OrderedBlockBoundaryGap hSigma
      (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) r s Delta := by
  apply orderedBlockBoundaryGap_iff.mpr
  simpa only [PopulationBoundaryGap] using hgap

end PopulationBoundaryGap

/-- The source's population gap `Delta` for Theorem 2.

For every non-full block the second disjunct says that `Delta` is the greatest
real number satisfying the two population boundary inequalities, hence exactly
`min (lambda_(r-1) - lambda_r) (lambda_s - lambda_(s+1))` with a missing endpoint
omitted.  There `Delta` IS the source denominator, not a lower bound for it.

The full block `r = 0`, `s + 1 = p` is the first disjunct, and is different in
kind.  There are no exterior eigenvalues, the source conventions make both
exterior gaps `+infinity`, and no greatest finite real satisfies the two vacuous
clauses, so the second disjunct is unsatisfiable there.  In that case the
selected frame spans the whole space and the sine distance is zero, so every
positive finite `Delta` is an admissible surrogate for the infinite source
denominator and the headline theorems hold for each of them.  The branch does not
claim that a finite `Delta` is the source's `+infinity`. -/
def SourcePopulationGap
    {p : Nat}
    (Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (r s : Nat) (Delta : Real) : Prop :=
  (r = 0 ∧ s + 1 = p) ∨
    (PopulationBoundaryGap Sigma hSigma r s Delta ∧
      ∀ delta : Real,
        PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta)

/-- Characteristic form of the source-gap predicate.

Outside the full-space endpoint case, this says precisely that `Delta` is the
largest common lower bound of the finite population boundary gaps, which is the
printed minimum.  In that endpoint case it says the block is the whole spectrum,
where the printed gaps are both infinite. -/
theorem sourcePopulationGap_iff
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real} :
    SourcePopulationGap Sigma hSigma r s Delta ↔
      (r = 0 ∧ s + 1 = p) ∨
        (PopulationBoundaryGap Sigma hSigma r s Delta ∧
          ∀ delta : Real,
            PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta) :=
  Iff.rfl

namespace SourcePopulationGap

/-- Forget exactness and retain the lower-bound form consumed by the proof. -/
theorem toPopulationBoundaryGap
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real}
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    PopulationBoundaryGap Sigma hSigma r s Delta := by
  rcases hgap with hfull | hfinite
  · rcases hfull with ⟨hr, hs⟩
    rw [populationBoundaryGap_iff]
    constructor
    · intro q j hq _
      omega
    · intro j q _ hq
      have hq_lt : (q : Nat) < p := q.isLt
      omega
  · exact hfinite.1

end SourcePopulationGap

/-- Frobenius norm spelling used by the paper-facing Theorem 2 statements.

This is a reducible abbreviation for the existing unitarily invariant Frobenius
seminorm, so the source notation can appear directly in the theorem statement
without introducing an opaque application-specific quantity. -/
noncomputable abbrev frobeniusNorm {p : Nat}
    (A : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)) : Real :=
  UnitarilyInvariantSeminorm.frobenius Real (EuclideanSpace Real (Fin p)) A

/-- Source-facing operator norm notation for the YWS headline statements. -/
local notation "‖" A "‖_op" => ‖LinearMap.toContinuousLinearMap A‖

/-- Source-facing Frobenius norm notation for the YWS headline statements. -/
local notation "‖" A "‖_F" => frobeniusNorm A

/-- **Yu--Wang--Samworth 2015, Theorem 2, first conclusion.**

This is the paper-facing and semantic-review statement.  `Sigma` and `SigmaHat`
are real symmetric operators on `Real^p`; `V` and `Vhat` are arbitrary
orthonormal eigenvector blocks at the ordered indices `r,...,s`; and `Delta` is
the source's exact population gap, not merely a chosen lower bound.  No sample
eigengap is assumed.

The sine norm is an explicit theorem parameter whose equality hypothesis identifies
it with the concrete Lean realization in the same signature.  The perturbation
norms use local source-facing notation, with `‖A‖_op` expanding to the operator
norm of `A.toContinuousLinearMap` and `‖A‖_F` expanding through the reducible
abbreviation `frobeniusNorm`.  Thus the claim after the colon reads like the
printed inequality without extra scalar naming hypotheses. -/
theorem theorem2_sinTheta
    {p d r s : Nat}
    (Sigma SigmaHat :
      EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace Real (Fin p))
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (sinThetaNorm : Real)
    (hSinThetaNorm :
      sinThetaNorm =
        sinThetaFrobenius (Submodule.span Real (Set.range V))
          (Submodule.span Real (Set.range Vhat)))
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    sinThetaNorm ≤
      2 * min
        (Real.sqrt d * ‖SigmaHat - Sigma‖_op)
        ‖SigmaHat - Sigma‖_F / Delta := by
  rw [hSinThetaNorm]
  have hsn : s + 1 ≤ p := by omega
  have hrd : r + d = s + 1 := by omega
  exact yuWangSamworth_sinTheta_block_le
    (A := Sigma) (B := SigmaHat) (hA := hSigma) (hB := hSigmaHat)
    (n := p) (d := d) (r := r) (s := s)
    (hn := show finrank Real (EuclideanSpace Real (Fin p)) = p by simp)
    hsn hrd
    (IsEigenvectorBlock.toIsOrderedEigenframe hV)
    (IsEigenvectorBlock.toIsOrderedEigenframe hVhat) hDelta
    (PopulationBoundaryGap.toOrderedBlockBoundaryGap
      (SourcePopulationGap.toPopulationBoundaryGap hgap))

/-- **Yu--Wang--Samworth 2015, Theorem 2, second conclusion.**

Under the same mathematical source hypotheses, an orthogonal matrix aligns the
supplied sample frame `Vhat` to the supplied population frame `V` with the
printed `2^(3/2)` Frobenius bound.  As in the first conclusion, the perturbation
operator and Frobenius norms use the local source-facing `‖A‖_op` and `‖A‖_F`
notations. -/
theorem theorem2_alignedFrame
    {p d r s : Nat}
    (Sigma SigmaHat :
      EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace Real (Fin p))
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    ∃ O : Matrix (Fin d) (Fin d) Real,
      O ∈ Matrix.orthogonalGroup (Fin d) Real ∧
        Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min
              (Real.sqrt d * ‖SigmaHat - Sigma‖_op)
              ‖SigmaHat - Sigma‖_F / Delta := by
  have hsn : s + 1 ≤ p := by omega
  have hrd : r + d = s + 1 := by omega
  exact yuWangSamworth_alignedFrame_block_real_le
    (A := Sigma) (B := SigmaHat) (hA := hSigma) (hB := hSigmaHat)
    (n := p) (d := d) (r := r) (s := s)
    (hn := show finrank Real (EuclideanSpace Real (Fin p)) = p by simp)
    hsn hrd
    (IsEigenvectorBlock.toIsOrderedEigenframe hV)
    (IsEigenvectorBlock.toIsOrderedEigenframe hVhat) hDelta
    (PopulationBoundaryGap.toOrderedBlockBoundaryGap
      (SourcePopulationGap.toPopulationBoundaryGap hgap))

end PaperFacing


end YuWangSamworth2015
