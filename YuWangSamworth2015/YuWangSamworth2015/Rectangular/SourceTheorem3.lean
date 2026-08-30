/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import YuWangSamworth2015.Rectangular.SingularBlock

/-!
# Theorem 3 at the printed scope: the source rank condition and the exact gap

`YuWangSamworth2015/Rectangular/SingularBlock.lean` states the corrected Theorem 3
for an arbitrary block of ambient singular indices with the boundary gap supplied
as a *lower bound*.  That is a valid generalization, and it is kept.  It is not
the printed theorem, which restricts the block by

`1 <= r <= s <= rank(A)`

and which names its denominator exactly:

`Delta_sv = min(sigma_(r-1)^2 - sigma_r^2, sigma_s^2 - sigma_(s+1)^2)`.

This module adds the paper-facing wrappers that carry both, mirroring what
`YuWangSamworth2015/Symmetric/Theorem2.lean` does for Theorem 2 with
`SourcePopulationGap`.

## The two things this module fixes, which are independent

**The source rank condition.**  Lean indices are zero-based, so the printed
`1 <= r <= s <= rank(A)` is `r <= s` together with `s < finrank (range A)`.  Every
selected index then carries a strictly positive singular value, and the ambient
bounds the general theorems ask for are consequences rather than hypotheses:
`rank(A) <= q` gives `s < q`, `rank(A) <= p` gives `s < p`, and both give
`0 < q` and `0 < p`.  Nothing below asks the caller for those.

**The exact denominator.**  `SourceSingularGap` identifies `Delta` with the
printed minimum instead of merely bounding it below, exactly as
`SourcePopulationGap` does for Theorem 2, and `SingularBoundaryGap` remains
available as the lower-bound predicate the perturbation argument consumes.

## The endpoint convention, which is where the paper is wrong

The printed conventions are `sigma_0^2 := +infinity` and
`sigma_(rank(A)+1)^2 := -infinity`.  The first is fine.  **The second is false**,
and `YuWangSamworth2015/Rectangular/RankBoundary.lean` refutes it.  The corrected
convention is the *ambient* one the paper's own proof uses -- it passes to
`A*A` with eigenvalues `sigma_1^2 >= ... >= sigma_q^2` and applies Theorem 2,
whose convention is `lambda_(q+1) := -infinity` at the ambient index -- so the
right blocks read the convention at `q` and the left blocks at `p`, with
`sigma_j = 0` past the rank.  All four wrappers below use that reading; none of
them reintroduces `sigma_(rank(A)+1)^2 := -infinity`.

Concretely, at the ends of a selected block:

* `r = 0` is the paper's first index, so the upper boundary is `+infinity` and
  the upper clause is vacuous;
* a block ending before the ambient index has the ordinary next squared singular
  value below it, possibly `0` when the block ends exactly at the rank -- a
  finite requirement where the printed convention offered a vacuous one;
* a block filling the whole ambient space has both source boundaries infinite.
  With the source rank condition in force that forces `A` to have full column
  rank on the right (full row rank on the left) and the selected frame to span
  everything, so the sine distance is identically zero and the bound holds for
  every positive finite `Delta`.  `SourceSingularGap` records that case as an
  explicit disjunct rather than pretending a finite `Delta` is infinite.

## The frames

`IsRightSingularBlock` asks for `A*A v_i = sigma_(r+i)^2 v_i`, which is the
Gram characterization the paper's proof uses.
`isRightSingularBlock_iff_pairedSingularVectors` proves that at the selected
positive-rank indices this is equivalent to the paper's printed pair of
singular-vector equations `A v_j = sigma_j u_j` and `A* u_j = sigma_j v_j`, so
the choice of presentation is a notational one and is machine-checked.

## Main results

* `YuWangSamworth2015.theorem3_rightSinTheta`, `..._rightAlignedFrame`,
  `..._leftSinTheta`, `..._leftAlignedFrame`.
* `YuWangSamworth2015.SourceSingularGap` and its bridge to
  `YuWangSamworth2015.SingularBoundaryGap`.
* `YuWangSamworth2015.isRightSingularBlock_iff_pairedSingularVectors` and its
  left twin.
-/

namespace YuWangSamworth2015

open TauCeti YuWangSamworth2015.DavisKahanTheory
open scoped InnerProductSpace BigOperators
open Module (finrank)

section PaperFacing

/-! ## Rank arithmetic

The printed block condition is about `rank(A)`; the general theorems are about
the ambient dimension.  These two facts take one to the other. -/

/-- `rank(A)` is at most the dimension of the domain. -/
theorem finrank_range_le_domain {p q : ℕ}
    (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) :
    finrank ℝ (LinearMap.range A) ≤ q := by
  simpa using A.finrank_range_le

/-- `rank(A)` is at most the dimension of the codomain. -/
theorem finrank_range_le_codomain {p q : ℕ}
    (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) :
    finrank ℝ (LinearMap.range A) ≤ p := by
  simpa using (LinearMap.range A).finrank_le

/-! ## The paper's blocks -/

/-- **A right singular block at the zero-based indices `r, ..., s`.**

`V` is orthonormal and `A*A v_i = sigma_(r+i)^2 v_i`.  This is the paper's
`A v_j = sigma_j u_j` after passing to the right Gram operator, which is what its
own proof does; `isRightSingularBlock_iff_pairedSingularVectors` proves the two
readings agree at the indices the source rank condition selects.

Nothing is assumed about multiplicity, so at a repeated singular value every
orthonormal choice inside the singular subspace satisfies this. -/
def IsRightSingularBlock {p q d r s : ℕ}
    (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (_hr : r ≤ s) (_hd : d = s - r + 1)
    (V : Fin d → EuclideanSpace ℝ (Fin q)) : Prop :=
  Orthonormal ℝ V ∧
    ∀ i, (LinearMap.adjoint A ∘ₗ A) (V i) = A.singularValues (r + (i : ℕ)) ^ 2 • V i

/-- **A left singular block at the zero-based indices `r, ..., s`**:
`A A* u_i = sigma_(r+i)^2 u_i`, the paper's `A* u_j = sigma_j v_j` after passing
to the left Gram operator. -/
def IsLeftSingularBlock {p q d r s : ℕ}
    (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (_hr : r ≤ s) (_hd : d = s - r + 1)
    (U : Fin d → EuclideanSpace ℝ (Fin p)) : Prop :=
  Orthonormal ℝ U ∧
    ∀ i, (A ∘ₗ LinearMap.adjoint A) (U i) = A.singularValues (r + (i : ℕ)) ^ 2 • U i

/-! ## The gap predicates -/

/-- **The squared population singular boundary gap of the block `r, ..., s`,
read at the ambient index.**

`Delta <= sigma_(r-1)^2 - sigma_r^2` and `Delta <= sigma_s^2 - sigma_(s+1)^2`,
with a clause vacuous when the block reaches the corresponding end of the
ambient range.  `n` is the ambient dimension: `q` for right blocks and `p` for
left ones.  Because `LinearMap.singularValues` vanishes past the rank, the lower
gap at a block ending at the rank is the finite `sigma_s^2 - 0` and not the
printed `sigma_s^2 - (-infinity)`.

Only the singular values of `A` occur.  There is no sample singular gap. -/
def SingularBoundaryGap {p q : ℕ} (n : ℕ)
    (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (∀ a b : Fin n, (a : ℕ) + 1 = r → (b : ℕ) = r →
      Delta ≤ A.singularValues (a : ℕ) ^ 2 - A.singularValues (b : ℕ) ^ 2) ∧
    (∀ a b : Fin n, (a : ℕ) = s → (b : ℕ) = s + 1 →
      Delta ≤ A.singularValues (a : ℕ) ^ 2 - A.singularValues (b : ℕ) ^ 2)

/-- **The source's exact denominator
`Delta_sv = min(sigma_(r-1)^2 - sigma_r^2, sigma_s^2 - sigma_(s+1)^2)`.**

Outside the full-ambient-block case the second disjunct says that `Delta` is the
*greatest* real satisfying the two boundary inequalities, which is that minimum
with a missing endpoint omitted; this identifies `Delta`, rather than merely
bounding it below.

The first disjunct is the full-ambient-block case `r = 0`, `s + 1 = n`.  There
are then no exterior singular values, the source conventions make both exterior
gaps `+infinity`, and no greatest finite real satisfies the (vacuous) clauses.
Under the source rank condition that case forces the selected frame to span the
whole ambient space, so the sine distance is `0` and the conclusion holds for
every positive finite `Delta`; the disjunct records that, and does not claim a
finite `Delta` is infinite. -/
def SourceSingularGap {p q : ℕ} (n : ℕ)
    (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (r = 0 ∧ s + 1 = n) ∨
    (SingularBoundaryGap n A r s Delta ∧
      ∀ delta : ℝ, SingularBoundaryGap n A r s delta → delta ≤ Delta)

/-- Characteristic form of the exact source-gap predicate. -/
theorem sourceSingularGap_iff {p q n : ℕ}
    {A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    {r s : ℕ} {Delta : ℝ} :
    SourceSingularGap n A r s Delta ↔
      (r = 0 ∧ s + 1 = n) ∨
        (SingularBoundaryGap n A r s Delta ∧
          ∀ delta : ℝ, SingularBoundaryGap n A r s delta → delta ≤ Delta) :=
  Iff.rfl

namespace SourceSingularGap

/-- Forget exactness and retain the lower-bound form the perturbation argument
consumes.  In the full-ambient-block case both clauses are vacuous. -/
theorem toSingularBoundaryGap {p q n : ℕ}
    {A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    {r s : ℕ} {Delta : ℝ} (hgap : SourceSingularGap n A r s Delta) :
    SingularBoundaryGap n A r s Delta := by
  rcases hgap with ⟨hr, hs⟩ | hfinite
  · refine ⟨fun a b ha _ => ?_, fun a b _ hb => ?_⟩
    · omega
    · have : (b : ℕ) < n := b.isLt
      omega
  · exact hfinite.1

end SourceSingularGap

/-! ## The Gram characterization is the paper's paired singular-vector condition

The paper prints `A v_j = sigma_j u_j` on the right and `A* u_j = sigma_j v_j` on
the left, and its proof immediately passes to the Gram operators.  Under the
source rank condition every selected singular value is strictly positive, and
the two readings are then equivalent.  This is proved rather than assumed. -/

/-- Every index of a block satisfying the source rank condition carries a
strictly positive singular value. -/
theorem singularValues_pos_of_source_block {p q d r s : ℕ}
    {A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    (hr : r ≤ s) (hd : d = s - r + 1)
    (hrank : s < finrank ℝ (LinearMap.range A)) (i : Fin d) :
    0 < A.singularValues (r + (i : ℕ)) := by
  have hi : (i : ℕ) < d := i.isLt
  exact A.singularValues_pos_iff_lt_finrank_range.mpr (by omega)

/-- **The right Gram condition is the paper's printed pair of singular-vector
equations.**

At the indices selected by the source rank condition, `V` is a right singular
block of `A` exactly when it is orthonormal and there is an orthonormal family
`U` of corresponding left singular vectors with `A v_j = sigma_j u_j` and
`A* u_j = sigma_j v_j`, which is what Theorem 3 prints. -/
theorem isRightSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A))
    (V : Fin d → EuclideanSpace ℝ (Fin q)) :
    IsRightSingularBlock A hr hd V ↔
      Orthonormal ℝ V ∧
        ∃ U : Fin d → EuclideanSpace ℝ (Fin p), Orthonormal ℝ U ∧
          ∀ i, A (V i) = A.singularValues (r + (i : ℕ)) • U i ∧
            LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i := by
  classical
  constructor
  · rintro ⟨hV, hgram⟩
    have hpos : ∀ i : Fin d, 0 < A.singularValues (r + (i : ℕ)) := fun i =>
      singularValues_pos_of_source_block hr hd hrank i
    have hgram' : ∀ i, LinearMap.adjoint A (A (V i))
        = A.singularValues (r + (i : ℕ)) ^ 2 • V i := by
      intro i; simpa using hgram i
    refine ⟨hV, fun i => (A.singularValues (r + (i : ℕ)))⁻¹ • A (V i), ?_, fun i => ⟨?_, ?_⟩⟩
    · rw [orthonormal_iff_ite]
      intro i j
      have hVij : inner ℝ (V i) (V j) = if i = j then (1 : ℝ) else (0 : ℝ) :=
        (orthonormal_iff_ite.mp hV) i j
      have hij : inner ℝ (A (V i)) (A (V j))
          = A.singularValues (r + (j : ℕ)) ^ 2 * (if i = j then (1 : ℝ) else (0 : ℝ)) := by
        rw [← LinearMap.adjoint_inner_right A (V i) (A (V j)), hgram' j,
          real_inner_smul_right, hVij]
      rw [real_inner_smul_left, real_inner_smul_right, hij]
      by_cases h : i = j
      · subst h
        have hne : A.singularValues (r + (i : ℕ)) ≠ 0 := ne_of_gt (hpos i)
        field_simp
      · simp [h]
    · rw [smul_inv_smul₀ (ne_of_gt (hpos i))]
    · rw [map_smul, hgram' i, smul_smul]
      congr 1
      have hne : A.singularValues (r + (i : ℕ)) ≠ 0 := ne_of_gt (hpos i)
      field_simp
  · rintro ⟨hV, U, -, hpair⟩
    refine ⟨hV, fun i => ?_⟩
    have h1 := (hpair i).1
    have h2 := (hpair i).2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [h1, map_smul, h2, smul_smul]
    congr 1
    ring

/-- **The left Gram condition is the paper's printed pair of singular-vector
equations**, with the roles of the two frames exchanged. -/
theorem isLeftSingularBlock_iff_pairedSingularVectors {p q d r s : ℕ}
    {A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    {hr : r ≤ s} {hd : d = s - r + 1}
    (hrank : s < finrank ℝ (LinearMap.range A))
    (U : Fin d → EuclideanSpace ℝ (Fin p)) :
    IsLeftSingularBlock A hr hd U ↔
      Orthonormal ℝ U ∧
        ∃ V : Fin d → EuclideanSpace ℝ (Fin q), Orthonormal ℝ V ∧
          ∀ i, LinearMap.adjoint A (U i) = A.singularValues (r + (i : ℕ)) • V i ∧
            A (V i) = A.singularValues (r + (i : ℕ)) • U i := by
  classical
  constructor
  · rintro ⟨hU, hgram⟩
    have hpos : ∀ i : Fin d, 0 < A.singularValues (r + (i : ℕ)) := fun i =>
      singularValues_pos_of_source_block hr hd hrank i
    have hgram' : ∀ i, A (LinearMap.adjoint A (U i))
        = A.singularValues (r + (i : ℕ)) ^ 2 • U i := by
      intro i; simpa using hgram i
    refine ⟨hU, fun i => (A.singularValues (r + (i : ℕ)))⁻¹ • LinearMap.adjoint A (U i),
      ?_, fun i => ⟨?_, ?_⟩⟩
    · rw [orthonormal_iff_ite]
      intro i j
      have hUij : inner ℝ (U i) (U j) = if i = j then (1 : ℝ) else (0 : ℝ) :=
        (orthonormal_iff_ite.mp hU) i j
      have hij : inner ℝ (LinearMap.adjoint A (U i)) (LinearMap.adjoint A (U j))
          = A.singularValues (r + (j : ℕ)) ^ 2 * (if i = j then (1 : ℝ) else (0 : ℝ)) := by
        rw [LinearMap.adjoint_inner_left A (LinearMap.adjoint A (U j)) (U i), hgram' j,
          real_inner_smul_right, hUij]
      rw [real_inner_smul_left, real_inner_smul_right, hij]
      by_cases h : i = j
      · subst h
        have hne : A.singularValues (r + (i : ℕ)) ≠ 0 := ne_of_gt (hpos i)
        field_simp
      · simp [h]
    · rw [smul_inv_smul₀ (ne_of_gt (hpos i))]
    · rw [map_smul, hgram' i, smul_smul]
      congr 1
      have hne : A.singularValues (r + (i : ℕ)) ≠ 0 := ne_of_gt (hpos i)
      field_simp
  · rintro ⟨hU, V, -, hpair⟩
    refine ⟨hU, fun i => ?_⟩
    have h1 := (hpair i).1
    have h2 := (hpair i).2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [h1, map_smul, h2, smul_smul]
    congr 1
    ring

/-! ## Theorem 3 at the printed scope

The four wrappers below are the paper's own statements: the block is constrained
by `1 <= r <= s <= rank(A)` in its zero-based form, the denominator is the exact
`SourceSingularGap`, and the endpoint convention is the corrected ambient one.
Each is a specialization of the corresponding
`YuWangSamworth2015.DavisKahanTheory..._block_le` theorem, which stays available
at its larger scope. -/

/-- `finrank R^n = n`. -/
theorem finrank_euclidean (n : ℕ) : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp

/-- A source-scoped right block is an ordered right singular frame. -/
theorem IsRightSingularBlock.toOrderedFrame {p q d r s : ℕ}
    {A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    {hr : r ≤ s} {hd : d = s - r + 1} {V : Fin d → EuclideanSpace ℝ (Fin q)}
    (hV : IsRightSingularBlock A hr hd V)
    (hrd : r + d = s + 1) (hsq : s + 1 ≤ q) :
    IsOrderedRightSingularFrame A (finrank_euclidean q)
      (consecutiveEmb (hrd.trans_le hsq)) V := by
  refine isOrderedEigenframe_iff.mpr { orthonormal := hV.1, apply_eq := ?_ }
  intro i
  rw [show (isSymmetric_rightGram A).eigenvalues (finrank_euclidean q)
        (consecutiveEmb (hrd.trans_le hsq) i)
      = A.singularValues (r + (i : ℕ)) ^ 2 from by
        rw [← sq_singularValues_eq_eigenvalues_rightGram]; rfl]
  exact hV.2 i

/-- A source-scoped left block is an ordered left singular frame. -/
theorem IsLeftSingularBlock.toOrderedFrame {p q d r s : ℕ}
    {A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    {hr : r ≤ s} {hd : d = s - r + 1} {U : Fin d → EuclideanSpace ℝ (Fin p)}
    (hU : IsLeftSingularBlock A hr hd U)
    (hrd : r + d = s + 1) (hsp : s + 1 ≤ p) :
    IsOrderedLeftSingularFrame A (finrank_euclidean p)
      (consecutiveEmb (hrd.trans_le hsp)) U := by
  refine isOrderedEigenframe_iff.mpr { orthonormal := hU.1, apply_eq := ?_ }
  intro i
  rw [show (isSymmetric_leftGram A).eigenvalues (finrank_euclidean p)
        (consecutiveEmb (hrd.trans_le hsp) i)
      = A.singularValues (r + (i : ℕ)) ^ 2 from by
        rw [← sq_singularValues_eq_eigenvalues_leftGram]; rfl]
  exact hU.2 i

/-- **Yu--Wang--Samworth 2015, Theorem 3, right singular subspaces, sine
conclusion, at the printed scope.**

`A` and `Ahat` are real `p x q` maps, the block satisfies the source condition
`1 <= r <= s <= rank(A)` in zero-based form, `V` and `Vhat` are arbitrary
orthonormal right singular blocks -- no separation whatever is assumed among the
singular values of `Ahat` -- and `Delta` is the source's exact squared singular
gap under the corrected ambient endpoint convention. -/
theorem theorem3_rightSinTheta {p q d r s : ℕ}
    (A Ahat : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (hr : r ≤ s) (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace ℝ (Fin q))
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)) ≤
      2 * (2 * A.singularValues 0 + ‖(Ahat - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Ahat - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Ahat - A)) / Delta := by
  have hsq : s < q := lt_of_lt_of_le hrank (finrank_range_le_domain A)
  have : Nonempty (Fin q) := ⟨⟨s, hsq⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin q)) := inferInstance
  have hrd : r + d = s + 1 := by omega
  have hgap' := hgap.toSingularBoundaryGap
  exact yuWangSamworth_rightSingularSubspace_block_le (hn := finrank_euclidean q)
    (by omega) hrd (hV.toOrderedFrame hrd (by omega))
    (hVhat.toOrderedFrame hrd (by omega)) hDelta hgap'.1 hgap'.2

/-- **Yu--Wang--Samworth 2015, Theorem 3, right singular subspaces, aligned-frame
conclusion, at the printed scope.**

An orthogonal `Ohat` in `O(d)` carries `Vhat` onto the supplied `V` within
`2^(3/2) (2 sigma_1 + ||D||_op) min(sqrt d ||D||_op, ||D||_F) / Delta`. -/
theorem theorem3_rightAlignedFrame {p q d r s : ℕ}
    (A Ahat : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (hr : r ≤ s) (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace ℝ (Fin q))
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 + ‖(Ahat - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Ahat - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Ahat - A)) / Delta := by
  obtain ⟨O, hO, hbound⟩ := exists_orthogonal_sqrt_sum_sq_norm_sub_le hV.1 hVhat.1
    (theorem3_rightSinTheta A Ahat hr hrank hd V Vhat hV hVhat Delta hDelta hgap)
  exact ⟨O, hO, hbound.trans_eq (by ring)⟩

/-- **Yu--Wang--Samworth 2015, Theorem 3, left singular subspaces, sine
conclusion, at the printed scope.** -/
theorem theorem3_leftSinTheta {p q d r s : ℕ}
    (A Ahat : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (hr : r ≤ s) (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → EuclideanSpace ℝ (Fin p))
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    sinThetaFrobenius (Submodule.span ℝ (Set.range U))
        (Submodule.span ℝ (Set.range Uhat)) ≤
      2 * (2 * A.singularValues 0 + ‖(Ahat - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Ahat - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantSeminorm.frobenius (Ahat - A)) / Delta := by
  have hsq : s < q := lt_of_lt_of_le hrank (finrank_range_le_domain A)
  have hsp : s < p := lt_of_lt_of_le hrank (finrank_range_le_codomain A)
  have : Nonempty (Fin q) := ⟨⟨s, hsq⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin q)) := inferInstance
  have hrd : r + d = s + 1 := by omega
  have hgap' := hgap.toSingularBoundaryGap
  exact yuWangSamworth_leftSingularSubspace_block_le (hm := finrank_euclidean p)
    (by omega) hrd (hU.toOrderedFrame hrd (by omega))
    (hUhat.toOrderedFrame hrd (by omega)) hDelta hgap'.1 hgap'.2

/-- **Yu--Wang--Samworth 2015, Theorem 3, left singular subspaces, aligned-frame
conclusion, at the printed scope.** -/
theorem theorem3_leftAlignedFrame {p q d r s : ℕ}
    (A Ahat : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (hr : r ≤ s) (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → EuclideanSpace ℝ (Fin p))
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • Uhat j) - U i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 + ‖(Ahat - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Ahat - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantSeminorm.frobenius (Ahat - A)) / Delta := by
  obtain ⟨O, hO, hbound⟩ := exists_orthogonal_sqrt_sum_sq_norm_sub_le hU.1 hUhat.1
    (theorem3_leftSinTheta A Ahat hr hrank hd U Uhat hU hUhat Delta hDelta hgap)
  exact ⟨O, hO, hbound.trans_eq (by ring)⟩

end PaperFacing

end YuWangSamworth2015
