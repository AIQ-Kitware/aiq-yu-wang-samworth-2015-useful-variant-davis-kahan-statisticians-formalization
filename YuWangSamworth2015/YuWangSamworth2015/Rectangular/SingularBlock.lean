/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.Rectangular.RankBoundary

/-!
# Theorem 3 in singular-value notation, with the corrected boundary convention

`YuWangSamworth2015/Rectangular/Theorem4.lean` proves the singular-subspace
theorem with the gap hypothesis phrased as the intrinsic separation of the sorted
spectrum of `A⋆A`.  That is the mathematically correct hypothesis, and it is not
the paper's notation.  This module states the same theorems in the notation the
paper uses — consecutive singular-value indices `r, …, s` and the squared
boundary gap

`Δ_sv ≤ min(σ_{r-1}² − σ_r², σ_s² − σ_{s+1}²)` —

so that a reader can see exactly which part of the printed theorem is true.

## What changes, and why

The printed conventions are `σ_0² := +∞` and `σ_{rank(A)+1}² := −∞`.  The first
is fine and is modelled here, as in `YuWangSamworth2015.OrderedBlockBoundaryGap`, by vacuous
quantification.  **The second is false**, and
`YuWangSamworth2015/Rectangular/RankBoundary.lean` refutes it: it makes the
denominator infinite at `s = rank(A)`, so the printed bound asserts that the
sample and population right singular subspaces coincide when they can be
orthogonal.

The correction is to read the convention at the *ambient* index, `σ_{q+1}² := −∞`
for the right blocks and `σ_{p+1}² := −∞` for the left, with `σ_j := 0` for
`j` past the rank.  That is what the paper's own proof requires, since it applies
Theorem 2 to `A⋆A ∈ ℝ^{q×q}`.  The statements below are stated in exactly that
reading:

* `sq_singularValues_eq_eigenvalues_rightGram` is the bridge, and it is where the
  zero continuation enters — `LinearMap.singularValues` is zero past the rank by
  construction, so `σ_j² ` and the sorted spectrum of `A⋆A` agree at *every*
  ambient index, zeros included;
* `singularBoundaryGap_of_rank_le` is the rank-boundary case made explicit: when
  the block ends at or past `rank(A)` the lower boundary gap is `σ_s² − 0`, a
  finite positive number, not the printed `σ_s² − (−∞)`.

The statements below use the source's own variables: the block is `r, …, s` and
the frame size `d` is tied to them by `r + d = s + 1`.

So the theorems below are the **corrected** Theorem 3, not the printed one; the
printed one is false exactly where these two differ.

## Main results

* `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularSubspace_block_le` and
  `..._leftSingularSubspace_block_le`: the sine bound with consecutive singular
  indices and the squared boundary gap.
* `YuWangSamworth2015.DavisKahanTheory.yuWangSamworth_rightSingularAlignedBasis_block_le`
  and `..._leftSingularAlignedBasis_block_le`: the aligned-frame conclusions.
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

/-! ## The squared-singular-value bridge -/

/-- **The sorted spectrum of `A⋆A` is the squared singular values, zeros
included.**  `LinearMap.singularValues` vanishes past `rank(A)`, so this identity
holds at *every* ambient index — which is precisely the corrected reading of the
paper's boundary convention. -/
theorem sq_singularValues_eq_eigenvalues_rightGram (A : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 E = n) (i : Fin n) :
    A.singularValues (i : ℕ) ^ 2 = (isSymmetric_rightGram A).eigenvalues hn i :=
  A.sq_singularValues_fin hn i

/-- The same for `A A⋆` and the left singular vectors. -/
theorem sq_singularValues_eq_eigenvalues_leftGram (A : E →ₗ[𝕜] F) {m : ℕ}
    (hm : finrank 𝕜 F = m) (i : Fin m) :
    A.singularValues (i : ℕ) ^ 2 = (isSymmetric_leftGram A).eigenvalues hm i :=
  sq_singularValues_selfCompAdjoint A hm i

/-- **The paper's boundary gap, translated.**  Squared-singular-value boundary
gaps at the ends of the block `r, …, s` are exactly the boundary gap of the
sorted spectrum of `A⋆A`. -/
theorem orderedBlockBoundaryGap_rightGram {A : E →ₗ[𝕜] F} {n r s : ℕ}
    (hn : finrank 𝕜 E = n) {Δ : ℝ}
    (hlo : ∀ q p : Fin n, (q : ℕ) + 1 = r → (p : ℕ) = r →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2)
    (hhi : ∀ q p : Fin n, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2) :
    OrderedBlockBoundaryGap (isSymmetric_rightGram A) hn r s Δ := by
  refine orderedBlockBoundaryGap_iff.mpr ⟨fun q p hq hp => ?_, fun q p hq hp => ?_⟩ <;>
    rw [← sq_singularValues_eq_eigenvalues_rightGram A hn,
      ← sq_singularValues_eq_eigenvalues_rightGram A hn]
  · exact hlo q p hq hp
  · exact hhi q p hq hp

/-- The left-hand counterpart of `orderedBlockBoundaryGap_rightGram`. -/
theorem orderedBlockBoundaryGap_leftGram {A : E →ₗ[𝕜] F} {m r s : ℕ}
    (hm : finrank 𝕜 F = m) {Δ : ℝ}
    (hlo : ∀ q p : Fin m, (q : ℕ) + 1 = r → (p : ℕ) = r →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2)
    (hhi : ∀ q p : Fin m, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2) :
    OrderedBlockBoundaryGap (isSymmetric_leftGram A) hm r s Δ := by
  refine orderedBlockBoundaryGap_iff.mpr ⟨fun q p hq hp => ?_, fun q p hq hp => ?_⟩ <;>
    rw [← sq_singularValues_eq_eigenvalues_leftGram A hm,
      ← sq_singularValues_eq_eigenvalues_leftGram A hm]
  · exact hlo q p hq hp
  · exact hhi q p hq hp

/-- **The rank boundary, in the corrected reading.**

When the block ends at or past `rank(A)` the paper's printed convention declares
the lower boundary gap infinite; the correct value is `σ_s² − 0 = σ_s²`, because
`σ_{s+1} = 0` rather than `−∞`.  Supplying `Δ ≤ σ_s²` therefore discharges the
lower boundary hypothesis — a finite, checkable requirement where the printed
convention offered a vacuous one.  `yuWangSamworth_theorem3_printed_rankBoundary_refutation`
is what goes wrong without it. -/
theorem singularBoundaryGap_of_rank_le {A : E →ₗ[𝕜] F} {n s : ℕ} {Δ : ℝ}
    (hrank : finrank 𝕜 (LinearMap.range A) ≤ s + 1)
    (hs : ∀ q : Fin n, (q : ℕ) = s → Δ ≤ A.singularValues (q : ℕ) ^ 2) :
    ∀ q p : Fin n, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2 := by
  intro q p hq hp
  have hzero : A.singularValues (p : ℕ) = 0 :=
    A.singularValues_eq_zero_iff_le_finrank_range.mpr (by rw [hp]; exact hrank)
  rw [hzero]
  simpa using hs q hq

/-! ## Theorem 3 with the source's indexing

As in `YuWangSamworth2015/YuWangSamworth2015/Core/ConsecutiveBlock.lean`,
the block is `r, …, s` with `d` tied to them by `r + d = s + 1`, the paper's
`d = s − r + 1`, and `s + 1 ≤ n` is the paper's `s ≤ q` (respectively `s ≤ p` on
the left). -/

/-- **Theorem 3, right singular subspaces, in singular-value notation.**

`V`, `V̂` are arbitrary orthonormal right singular frames of `A`, `Â` at the
indices `r, …, s`, with no separation assumed among the sample singular values,
and the hypothesis is the squared boundary gap
`Δ ≤ min(σ_{r-1}² − σ_r², σ_s² − σ_{s+1}²)` read at the *ambient* dimension, with
`σ_j = 0` past the rank.

This is the corrected theorem.  Under the printed convention
`σ_{rank(A)+1}² := −∞` the statement is false; see
`yuWangSamworth_theorem3_printed_rankBoundary_refutation`. -/
theorem yuWangSamworth_rightSingularSubspace_block_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {n d r s : ℕ} {hn : finrank 𝕜 E = n}
    (hsn : s + 1 ≤ n) (hd : r + d = s + 1) {v vHat : Fin d → E}
    (hv : IsOrderedRightSingularFrame A hn (consecutiveEmb (hd.trans_le hsn)) v)
    (hvHat : IsOrderedRightSingularFrame Â hn (consecutiveEmb (hd.trans_le hsn)) vHat)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hlo : ∀ q p : Fin n, (q : ℕ) + 1 = r → (p : ℕ) = r →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2)
    (hhi : ∀ q p : Fin n, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range v))
        (Submodule.span 𝕜 (Set.range vHat)) ≤
      2 * (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ :=
  yuWangSamworth_rightSingularSubspace_frame_le hv hvHat hΔ
    ((orderedBlockBoundaryGap_rightGram hn hlo hhi).indexGap _ hd)

/-- **Theorem 3, left singular subspaces, in singular-value notation.** -/
theorem yuWangSamworth_leftSingularSubspace_block_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {m d r s : ℕ} {hm : finrank 𝕜 F = m}
    (hsm : s + 1 ≤ m) (hd : r + d = s + 1) {u û : Fin d → F}
    (hu : IsOrderedLeftSingularFrame A hm (consecutiveEmb (hd.trans_le hsm)) u)
    (hû : IsOrderedLeftSingularFrame Â hm (consecutiveEmb (hd.trans_le hsm)) û)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hlo : ∀ q p : Fin m, (q : ℕ) + 1 = r → (p : ℕ) = r →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2)
    (hhi : ∀ q p : Fin m, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range û)) ≤
      2 * (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ :=
  yuWangSamworth_leftSingularSubspace_frame_le hu hû hΔ
    ((orderedBlockBoundaryGap_leftGram hm hlo hhi).indexGap _ hd)

/-- **Theorem 3, right aligned-frame conclusion, in singular-value notation.** -/
theorem yuWangSamworth_rightSingularAlignedBasis_block_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {n d r s : ℕ} {hn : finrank 𝕜 E = n}
    (hsn : s + 1 ≤ n) (hd : r + d = s + 1) {v vHat : Fin d → E}
    (hv : IsOrderedRightSingularFrame A hn (consecutiveEmb (hd.trans_le hsn)) v)
    (hvHat : IsOrderedRightSingularFrame Â hn (consecutiveEmb (hd.trans_le hsn)) vHat)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hlo : ∀ q p : Fin n, (q : ℕ) + 1 = r → (p : ℕ) = r →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2)
    (hhi : ∀ q p : Fin n, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2) :
    ∃ (w ŵ : Fin d → E), Orthonormal 𝕜 w ∧ Orthonormal 𝕜 ŵ ∧
      Submodule.span 𝕜 (Set.range w) = Submodule.span 𝕜 (Set.range v) ∧
      Submodule.span 𝕜 (Set.range ŵ) = Submodule.span 𝕜 (Set.range vHat) ∧
      Real.sqrt (∑ i, ‖ŵ i - w i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ :=
  yuWangSamworth_rightSingularAlignedBasis_frame_le hv hvHat hΔ
    ((orderedBlockBoundaryGap_rightGram hn hlo hhi).indexGap _ hd)

/-- **Theorem 3, left aligned-frame conclusion, in singular-value notation.** -/
theorem yuWangSamworth_leftSingularAlignedBasis_block_le
    {A Â : E →ₗ[𝕜] F} [Nontrivial E] {m d r s : ℕ} {hm : finrank 𝕜 F = m}
    (hsm : s + 1 ≤ m) (hd : r + d = s + 1) {u û : Fin d → F}
    (hu : IsOrderedLeftSingularFrame A hm (consecutiveEmb (hd.trans_le hsm)) u)
    (hû : IsOrderedLeftSingularFrame Â hm (consecutiveEmb (hd.trans_le hsm)) û)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hlo : ∀ q p : Fin m, (q : ℕ) + 1 = r → (p : ℕ) = r →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2)
    (hhi : ∀ q p : Fin m, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ A.singularValues (q : ℕ) ^ 2 - A.singularValues (p : ℕ) ^ 2) :
    ∃ (w ŵ : Fin d → F), Orthonormal 𝕜 w ∧ Orthonormal 𝕜 ŵ ∧
      Submodule.span 𝕜 (Set.range w) = Submodule.span 𝕜 (Set.range u) ∧
      Submodule.span 𝕜 (Set.range ŵ) = Submodule.span 𝕜 (Set.range û) ∧
      Real.sqrt (∑ i, ‖ŵ i - w i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 + ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Â - A)) / Δ :=
  yuWangSamworth_leftSingularAlignedBasis_frame_le hu hû hΔ
    ((orderedBlockBoundaryGap_leftGram hm hlo hhi).indexGap _ hd)

end DavisKahanTheory
end YuWangSamworth2015
