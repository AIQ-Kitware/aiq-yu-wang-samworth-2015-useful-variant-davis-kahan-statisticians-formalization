/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import YuWangSamworth2015.Rectangular.SourceTheorem3

/-!
# Solution: Yu--Wang--Samworth Theorem 3

The vocabulary is repeated verbatim from the challenge module; the proofs bridge
it to the development's paper-facing Theorem 3 and restate none of the argument.

The bridges are: the challenge's singular-block, boundary-gap and exact-gap
predicates are the development's own paper-facing predicates, so they need no
translation; the challenge's Frobenius norm and sine distance are the
development's, at the standard basis; and the four headline statements are
`YuWangSamworth2015.theorem3_*`, which carry the source rank condition
`s < rank(A)` and the exact `SourceSingularGap` denominator, with the corrected
ambient endpoint convention living in
`sq_singularValues_eq_eigenvalues_rightGram` -- `LinearMap.singularValues` is
zero past the rank, so squared singular values and the sorted spectrum of `A*A`
agree at every ambient index.
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

`V` has orthonormal columns and `AᵀA vᵢ = σ²_{r+i} vᵢ`, the Gram form the paper's
own proof uses; `isRightSingularBlock_iff_pairedSingularVectors` below proves
that at the indices `s < rank(A)` selects this is exactly the paper's printed
`A v_j = σ_j u_j`, `Aᵀ u_j = σ_j v_j`. Zero-based indices.

Nothing is assumed about multiplicity, so at a repeated singular value every
orthonormal choice inside the singular subspace satisfies this. -/
def IsRightSingularBlock {p q d r s : ℕ} (A : Rn q →ₗ[ℝ] Rn p)
    (_hr : r ≤ s) (_hd : d = s - r + 1) (V : Fin d → Rn q) : Prop :=
  Orthonormal ℝ V ∧
    ∀ i, (LinearMap.adjoint A ∘ₗ A) (V i) = A.singularValues (r + (i : ℕ)) ^ 2 • V i

/-- **A left singular block at the indices `r, …, s`**: `A Aᵀ uᵢ = σ²_{r+i} uᵢ`. -/
def IsLeftSingularBlock {p q d r s : ℕ} (A : Rn q →ₗ[ℝ] Rn p)
    (_hr : r ≤ s) (_hd : d = s - r + 1) (U : Fin d → Rn p) : Prop :=
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

/-- **The paper's denominator `Δ = min(σ²_{r−1} − σ²_r, σ²_s − σ²_{s+1})`,
exactly**, under the corrected ambient endpoint convention.

Outside the full-ambient-block case the second disjunct says that `Delta` is the
*greatest* real satisfying both boundary inequalities, which is that minimum with
a missing endpoint omitted: it identifies `Delta` rather than bounding it below.

The first disjunct is the full-ambient-block case `r = 0`, `s + 1 = n`. There are
then no exterior singular values, the source conventions make both exterior gaps
`+∞`, and no greatest finite real satisfies the two vacuous clauses. Under the
source rank condition the selected frame spans the whole ambient space in that
case, so the sine distance is `0` and the conclusions hold for every positive
`Delta`. The disjunct records that; it does not claim a finite `Delta` is
infinite. -/
def SourceSingularGap {p q : ℕ} (n : ℕ) (A : Rn q →ₗ[ℝ] Rn p) (r s : ℕ)
    (Delta : ℝ) : Prop :=
  (r = 0 ∧ s + 1 = n) ∨
    (SingularBoundaryGap n A r s Delta ∧
      ∀ delta : ℝ, SingularBoundaryGap n A r s delta → delta ≤ Delta)

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

end Bridges

theorem isRightSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : Rn q →ₗ[ℝ] Rn p} {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A)) (V : Fin d → Rn q) :
    IsRightSingularBlock A hr hd V ↔
      Orthonormal ℝ V ∧
        ∃ U : Fin d → Rn p, Orthonormal ℝ U ∧
          ∀ i, A (V i) = A.singularValues (r + (i : ℕ)) • U i ∧
            LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i :=
  YuWangSamworth2015.isRightSingularBlock_iff_pairedSingularVectors
    (hr := hr) (hd := hd) hrank V

theorem isLeftSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : Rn q →ₗ[ℝ] Rn p} {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A)) (U : Fin d → Rn p) :
    IsLeftSingularBlock A hr hd U ↔
      Orthonormal ℝ U ∧
        ∃ V : Fin d → Rn q, Orthonormal ℝ V ∧
          ∀ i, LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i ∧
            A (V i) = A.singularValues (r + (i : ℕ)) • U i :=
  YuWangSamworth2015.isLeftSingularBlock_iff_pairedSingularVectors
    (hr := hr) (hd := hd) hrank U

theorem theorem3_rightSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    sinThetaDist V Vhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  rw [sinThetaDist_eq hV.1 hVhat.1, coefficient, opNorm, frobeniusNorm_eq]
  exact (YuWangSamworth2015.theorem3_rightSinTheta A Ahat hr hrank hd V Vhat hV hVhat
    Delta hDelta hgap).trans_eq (by ring)

theorem theorem3_rightAlignedFrame {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
        2 * Real.sqrt 2 * coefficient d A (Ahat - A) / Delta := by
  obtain ⟨O, hO, hbound⟩ := YuWangSamworth2015.theorem3_rightAlignedFrame A Ahat hr hrank hd
    V Vhat hV hVhat Delta hDelta hgap
  refine ⟨O, hO, hbound.trans_eq ?_⟩
  rw [coefficient, opNorm, frobeniusNorm_eq]
  ring

theorem theorem3_leftSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    sinThetaDist U Uhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  rw [sinThetaDist_eq hU.1 hUhat.1, coefficient, opNorm, frobeniusNorm_eq]
  exact (YuWangSamworth2015.theorem3_leftSinTheta A Ahat hr hrank hd U Uhat hU hUhat
    Delta hDelta hgap).trans_eq (by ring)

theorem theorem3_leftAlignedFrame {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s)
    (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖∑ j, O j i • Uhat j - U i‖ ^ 2) ≤
        2 * Real.sqrt 2 * coefficient d A (Ahat - A) / Delta := by
  obtain ⟨O, hO, hbound⟩ := YuWangSamworth2015.theorem3_leftAlignedFrame A Ahat hr hrank hd
    U Uhat hU hUhat Delta hDelta hgap
  refine ⟨O, hO, hbound.trans_eq ?_⟩
  rw [coefficient, opNorm, frobeniusNorm_eq]
  ring

end YWSRectangular
