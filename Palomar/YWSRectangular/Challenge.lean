/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Mathlib

/-!
# Yu–Wang–Samworth 2015, Theorem 3: singular subspaces of rectangular matrices

Yi Yu, Tengyao Wang and Richard J. Samworth, *A useful variant of the Davis–Kahan
theorem for statisticians*, Biometrika **102** (2015) 315–323,
<https://doi.org/10.1093/biomet/asv008>. Published numbering.

## The result

Let `A, Â` be real `p × q` matrices, `D = Â − A`, with singular values
`σ₁ ≥ σ₂ ≥ ⋯` and `σ̂₁ ≥ σ̂₂ ≥ ⋯`. Fix a block `r, …, s` of singular indices,
`d = s − r + 1`, and let `V, V̂` hold corresponding orthonormal right singular
vectors. With the squared population singular gap
`Δ = min(σ²_{r−1} − σ²_r, σ²_s − σ²_{s+1})`,

* `‖sin Θ(V̂, V)‖_F ≤ 2 (2σ₁ + ‖D‖_op) min(√d ‖D‖_op, ‖D‖_F) / Δ`, and
* some `Ô ∈ O(d)` has `‖V̂Ô − V‖_F ≤ 2^{3/2} (2σ₁ + ‖D‖_op) min(√d ‖D‖_op, ‖D‖_F) / Δ`,

and the identical statements hold for the corresponding left singular blocks. As
in Theorem 2 the separation involves only the population object `A`; nothing is
assumed about the singular values of `Â`, so `V̂` ranges over every admissible
orthonormal singular frame. This is the population-gap counterpart of Wedin's
generalized `sin θ` theorem.

## Source correction — read this before comparing

**The statements below are the corrected theorem, not the printed one.** Yu, Wang
and Samworth print the conventions `σ²₀ := +∞` and `σ²_{rank(A)+1} := −∞`, and the
second is false. With `s = rank(A)` it makes `Δ = ∞`, so the printed bound asserts
that the sample and population singular subspaces coincide — and they need not.
Take `A` and `Â` to be the orthogonal projections of `ℝ²` onto the two coordinate
axes: both have rank one, so `r = s = 1 = rank(A)` is admissible and the printed
hypothesis holds, yet the two right singular subspaces are orthogonal and
`‖sin Θ‖_F = 1`. The accompanying development carries that as a machine-checked
refutation.

The defect is a mis-stated index and the paper's own proof shows the intended one:
that proof passes to `AᵀA` with eigenvalues `σ²₁ ≥ ⋯ ≥ σ²_q` and applies
Theorem 2, whose convention is `λ_{q+1} := −∞` at the **ambient** index `q`, not
at `rank(A)`. So the corrected conventions are `σ²₀ := +∞`, `σ²_{q+1} := −∞` and
`σ_j := 0` for `min(p, q) < j ≤ q` on the right, and `σ²_{p+1} := −∞` on the left.
The gap predicate below quantifies over the ambient index range and
`LinearMap.singularValues` vanishes past the rank, so that is the reading proved
here. Where the block ends at or past `rank(A)` the correct lower boundary gap is
the finite `σ²_s − 0`, which the caller must supply, in place of the vacuous one
the printed convention offered.

The other known defect in this paper, the missing square in printed Equation (4),
is formalized and refuted in the accompanying development and is not part of this
entry.

## Note on the proofs

Every proof below is a deliberate statement-side hole. The solution module
supplies the same declarations from the ordinary development.
-/

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

/-- **Theorem 3, right singular subspaces, sine conclusion** (corrected
rank-boundary convention; see the module docstring). -/
theorem theorem3_rightSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hr : r ≤ s) (hs : s < q) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rn q)
    (hV : IsRightSingularBlock A hr hs hd V)
    (hVhat : IsRightSingularBlock Ahat hr hs hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SingularBoundaryGap q A r s Delta) :
    sinThetaDist V Vhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  sorry

/-- **Theorem 3, right singular subspaces, aligned-frame conclusion.**

An orthogonal `Ô ∈ O(d)` with `‖V̂Ô − V‖_F ≤ 2^{3/2} (2σ₁ + ‖D‖_op) min(…) / Δ`,
compared against the supplied population frame `V`. -/
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
  sorry

/-- **Theorem 3, left singular subspaces, sine conclusion.** -/
theorem theorem3_leftSinTheta {p q d r s : ℕ}
    (A Ahat : Rn q →ₗ[ℝ] Rn p) (hq : 0 < q) (hr : r ≤ s) (hs : s < p)
    (hd : d = s - r + 1)
    (U Uhat : Fin d → Rn p)
    (hU : IsLeftSingularBlock A hr hs hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hs hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SingularBoundaryGap p A r s Delta) :
    sinThetaDist U Uhat ≤ 2 * coefficient d A (Ahat - A) / Delta := by
  sorry

/-- **Theorem 3, left singular subspaces, aligned-frame conclusion.** -/
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
  sorry

end YWSRectangular
