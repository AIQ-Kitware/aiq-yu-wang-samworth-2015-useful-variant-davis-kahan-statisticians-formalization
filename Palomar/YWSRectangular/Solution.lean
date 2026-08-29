/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import YuWangSamworth2015.Rectangular.SingularBlock

/-!
# Solution: Yu--Wang--Samworth Theorem 3

The vocabulary is repeated verbatim from the challenge module; the proofs bridge
it to the development's Theorem 3 and restate none of the argument.

The bridges are: a right (left) singular block is an ordered eigenframe of the
right (left) Gram operator, by `sq_singularValues_eq_eigenvalues_rightGram`, which
is where the rank-boundary correction lives -- `LinearMap.singularValues` is zero
past the rank, so squared singular values and the sorted spectrum of `A*A` agree
at every ambient index; the challenge's Frobenius norm and sine distance are the
development's, at the standard basis; and the aligned conclusions come from
`exists_orthogonal_sqrt_sum_sq_norm_sub_le`, the Procrustes step, applied to the
corresponding sine bound.
-/

open TauCeti YuWangSamworth2015 YuWangSamworth2015.DavisKahanTheory

namespace YWSRectangular

open scoped InnerProductSpace BigOperators
open Module (finrank)

/-- Real `n`-dimensional Euclidean space. A real `p × q` matrix is a linear map
`Rn q →ₗ[ℝ] Rn p`. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- `finrank ℝ (Rn n) = n`. -/
theorem finrank_Rn (n : ℕ) : finrank ℝ (Rn n) = n := by simp

/-- **A right singular block at the indices `r, …, s`.**

`V` has orthonormal columns and `AᵀA vᵢ = σ²_{r+i} vᵢ`, which is the paper's
`A v_j = σ_j u_j` written without naming the left vectors. Zero-based indices.

Nothing is assumed about multiplicity, so at a repeated singular value every
orthonormal choice inside the singular subspace satisfies this. -/
def IsRightSingularBlock {p q d r s : ℕ} (A : Rn q →ₗ[ℝ] Rn p)
    (_hr : r ≤ s) (_hs : s < q) (_hd : d = s - r + 1) (V : Fin d → Rn q) : Prop :=
  Orthonormal ℝ V ∧
    ∀ i, (LinearMap.adjoint A ∘ₗ A) (V i) = A.singularValues (r + (i : ℕ)) ^ 2 • V i

/-- **A left singular block at the indices `r, …, s`**: `A Aᵀ uᵢ = σ²_{r+i} uᵢ`. -/
def IsLeftSingularBlock {p q d r s : ℕ} (A : Rn q →ₗ[ℝ] Rn p)
    (_hr : r ≤ s) (_hs : s < p) (_hd : d = s - r + 1) (U : Fin d → Rn p) : Prop :=
  Orthonormal ℝ U ∧
    ∀ i, (A ∘ₗ LinearMap.adjoint A) (U i) = A.singularValues (r + (i : ℕ)) ^ 2 • U i

/-- **The squared population singular boundary gap of the block `r, …, s`**,
read at the ambient index — the corrected convention.

`Delta ≤ σ²_{r−1} − σ²_r` and `Delta ≤ σ²_s − σ²_{s+1}`, with the clause vacuous
when the block reaches the corresponding end of the ambient range. `n` is the
ambient dimension: `q` for right blocks, `p` for left ones. Because
`LinearMap.singularValues` is zero past the rank, `σ²_s − σ²_{s+1}` at a block
ending at `rank(A)` is the finite `σ²_s − 0`, not the printed `σ²_s − (−∞)`.

Only the singular values of `A` occur. There is no sample singular gap. -/
def SingularBoundaryGap {p q : ℕ} (n : ℕ) (A : Rn q →ₗ[ℝ] Rn p) (r s : ℕ)
    (Delta : ℝ) : Prop :=
  (∀ a b : Fin n, (a : ℕ) + 1 = r → (b : ℕ) = r →
      Delta ≤ A.singularValues (a : ℕ) ^ 2 - A.singularValues (b : ℕ) ^ 2) ∧
    (∀ a b : Fin n, (a : ℕ) = s → (b : ℕ) = s + 1 →
      Delta ≤ A.singularValues (a : ℕ) ^ 2 - A.singularValues (b : ℕ) ^ 2)

/-- **The Frobenius norm of a rectangular map**, `√(∑ᵢ ‖D eᵢ‖²)` over the
standard basis of the domain. -/
noncomputable def frobeniusNorm {p q : ℕ} (D : Rn q →ₗ[ℝ] Rn p) : ℝ :=
  Real.sqrt (∑ i, ‖D (EuclideanSpace.basisFun (Fin q) ℝ i)‖ ^ 2)

/-- The operator norm. -/
noncomputable abbrev opNorm {p q : ℕ} (D : Rn q →ₗ[ℝ] Rn p) : ℝ :=
  ‖LinearMap.toContinuousLinearMap D‖

/-- **The Frobenius `sin Θ` distance between the spans of two orthonormal
frames**, `√(∑ⱼ ‖P_{span(V)^⊥} V̂ⱼ‖²)`. -/
noncomputable def sinThetaDist {n d : ℕ} (V Vhat : Fin d → Rn n) : ℝ :=
  Real.sqrt (∑ j, ‖(Submodule.span ℝ (Set.range V))ᗮ.starProjection (Vhat j)‖ ^ 2)

/-- The paper's numerator `(2σ₁ + ‖D‖_op) min(√d ‖D‖_op, ‖D‖_F)`. -/
noncomputable abbrev coefficient {p q : ℕ} (d : ℕ) (A D : Rn q →ₗ[ℝ] Rn p) : ℝ :=
  (2 * A.singularValues 0 + opNorm D) * min (Real.sqrt d * opNorm D) (frobeniusNorm D)

section Bridges

variable {p q n d : ℕ}

/-- Positivity of the ambient dimension, from the block sitting inside it. -/
theorem nontrivial_Rn {s : ℕ} (hs : s < n) : Nontrivial (Rn n) := by
  have : Nonempty (Fin n) := ⟨⟨s, hs⟩⟩
  infer_instance

/-- The challenge's Frobenius norm is the development's rectangular Frobenius
seminorm. -/
theorem frobeniusNorm_eq (D : Rn q →ₗ[ℝ] Rn p) :
    frobeniusNorm D = RectangularUnitarilyInvariantSeminorm.frobenius.toFun D := by
  classical
  rw [RectangularUnitarilyInvariantSeminorm.frobenius_apply D
    ((EuclideanSpace.basisFun (Fin q) ℝ).reindex (finCongr (finrank_Rn q).symm))]
  refine congrArg Real.sqrt ?_
  refine (Fintype.sum_equiv (finCongr (finrank_Rn q)) _ _ fun i => ?_).symm
  simp

/-- The challenge's sine distance is the Frobenius sine distance between spans. -/
theorem sinThetaDist_eq {V Vhat : Fin d → Rn n}
    (hV : Orthonormal ℝ V) (hVhat : Orthonormal ℝ Vhat) :
    sinThetaDist V Vhat =
      sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)) := by
  simp only [sinThetaDist]
  rw [← sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal hV hVhat]
  exact Real.sqrt_sq (sinThetaFrobenius_nonneg _ _)

/-- A challenge right singular block is an ordered right singular frame. -/
theorem IsRightSingularBlock.toFrame {r s : ℕ} {A : Rn q →ₗ[ℝ] Rn p}
    {hr : r ≤ s} {hs : s < q} {hd : d = s - r + 1} {V : Fin d → Rn q}
    (hV : IsRightSingularBlock A hr hs hd V) (hrd : r + d = s + 1) :
    IsOrderedRightSingularFrame A (finrank_Rn q)
      (consecutiveEmb (hrd.trans_le (by omega))) V := by
  refine isOrderedEigenframe_iff.mpr { orthonormal := hV.1, apply_eq := ?_ }
  intro i
  have hidx : (consecutiveEmb (hrd.trans_le (by omega : s + 1 ≤ q)) i : ℕ)
      = r + (i : ℕ) := rfl
  rw [show (isSymmetric_rightGram A).eigenvalues (finrank_Rn q)
        (consecutiveEmb (hrd.trans_le (by omega : s + 1 ≤ q)) i)
      = A.singularValues (r + (i : ℕ)) ^ 2 from by
        rw [← sq_singularValues_eq_eigenvalues_rightGram, hidx]]
  exact hV.2 i

/-- A challenge left singular block is an ordered left singular frame. -/
theorem IsLeftSingularBlock.toFrame {r s : ℕ} {A : Rn q →ₗ[ℝ] Rn p}
    {hr : r ≤ s} {hs : s < p} {hd : d = s - r + 1} {U : Fin d → Rn p}
    (hU : IsLeftSingularBlock A hr hs hd U) (hrd : r + d = s + 1) :
    IsOrderedLeftSingularFrame A (finrank_Rn p)
      (consecutiveEmb (hrd.trans_le (by omega))) U := by
  refine isOrderedEigenframe_iff.mpr { orthonormal := hU.1, apply_eq := ?_ }
  intro i
  have hidx : (consecutiveEmb (hrd.trans_le (by omega : s + 1 ≤ p)) i : ℕ)
      = r + (i : ℕ) := rfl
  rw [show (isSymmetric_leftGram A).eigenvalues (finrank_Rn p)
        (consecutiveEmb (hrd.trans_le (by omega : s + 1 ≤ p)) i)
      = A.singularValues (r + (i : ℕ)) ^ 2 from by
        rw [← sq_singularValues_eq_eigenvalues_leftGram, hidx]]
  exact hU.2 i

end Bridges

theorem theorem3_rightSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s) (hs : s < q) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hs hd V)
    (hVhat : IsRightSingularBlock Ahat hr hs hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SingularBoundaryGap q A r s Delta) :
    sinThetaDist V Vhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  haveI := nontrivial_Rn (s := s) hs
  have hrd : r + d = s + 1 := by omega
  rw [sinThetaDist_eq hV.1 hVhat.1, coefficient, opNorm, frobeniusNorm_eq]
  exact (yuWangSamworth_rightSingularSubspace_block_le (by omega) hrd
    (hV.toFrame hrd) (hVhat.toFrame hrd) hDelta hgap.1 hgap.2).trans_eq (by ring)

theorem theorem3_rightAlignedFrame {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s) (hs : s < q) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hs hd V)
    (hVhat : IsRightSingularBlock Ahat hr hs hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SingularBoundaryGap q A r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
        2 * Real.sqrt 2 * coefficient d A (Ahat - A) / Delta := by
  obtain ⟨O, hO, hbound⟩ := exists_orthogonal_sqrt_sum_sq_norm_sub_le hV.1 hVhat.1
    ((sinThetaDist_eq hV.1 hVhat.1) ▸
      theorem3_rightSinTheta A Ahat hr hs hd V Vhat hV hVhat Delta hDelta hgap)
  exact ⟨O, hO, hbound.trans_eq (by ring)⟩

theorem theorem3_leftSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hq : 0 < q) (hr : r ≤ s) (hs : s < p)
    (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hs hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hs hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SingularBoundaryGap p A r s Delta) :
    sinThetaDist U Uhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  haveI := nontrivial_Rn (n := q) (s := 0) hq
  have hrd : r + d = s + 1 := by omega
  rw [sinThetaDist_eq hU.1 hUhat.1, coefficient, opNorm, frobeniusNorm_eq]
  exact (yuWangSamworth_leftSingularSubspace_block_le (by omega) hrd
    (hU.toFrame hrd) (hUhat.toFrame hrd) hDelta hgap.1 hgap.2).trans_eq (by ring)

theorem theorem3_leftAlignedFrame {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hq : 0 < q) (hr : r ≤ s) (hs : s < p)
    (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hs hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hs hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SingularBoundaryGap p A r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖∑ j, O j i • Uhat j - U i‖ ^ 2) ≤
        2 * Real.sqrt 2 * coefficient d A (Ahat - A) / Delta := by
  obtain ⟨O, hO, hbound⟩ := exists_orthogonal_sqrt_sum_sq_norm_sub_le hU.1 hUhat.1
    ((sinThetaDist_eq hU.1 hUhat.1) ▸
      theorem3_leftSinTheta A Ahat hq hr hs hd U Uhat hU hUhat Delta hDelta hgap)
  exact ⟨O, hO, hbound.trans_eq (by ring)⟩

end YWSRectangular
