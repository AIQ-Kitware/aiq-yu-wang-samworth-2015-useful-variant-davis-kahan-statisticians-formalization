/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BasisDiagonal
public import ForTauCeti.Analysis.InnerProductSpace.EigenblockSpan
public import YuWangSamworth2015.Core.Statistics

/-! # Constructing the corresponding-eigenblock hypothesis

`YuWangSamworth2015.CorrespondingEigenblock` is the branch-selection datum of the
Yu--Wang--Samworth population-gap theorems: the population block `U` and the
perturbed block `V` are spanned by the *same ordered indices* of the two sorted
eigenvector bases.  Every theorem in
`YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean` consumes
it, and until this file nothing produced one — the hypothesis had no instance
anywhere in the repository, so no concrete pair of covariance operators had ever
been checked against it.

`correspondingEigenblock_topEigenspace` supplies the case the statistical
literature actually uses: `U` and `V` are the *leading eigenspaces* of `A` and
`B`, and they correspond because "leading" is the same initial segment of
indices for both once the eigenvalues are sorted.  The only inputs are spectral
facts a reader can check on a concrete operator — an upper bound attained, and
its multiplicity.

`correspondingEigenblock_eigenvalueLevel` is the general rule behind it: two
eigenspaces correspond exactly when the same number of eigenvalues lies above
each and their multiplicities agree.  The leading case is `m = 0`; the general
case selects a block in the *middle* of the spectrum, which is what the
published Yu--Wang--Samworth sharpness example needs.

## Main results

* `YuWangSamworth2015.correspondingEigenblock_eigenvalueLevel`: eigenspaces at matching
  positions in the two spectra correspond.
* `YuWangSamworth2015.correspondingEigenblock_topEigenspace`: leading eigenspaces of equal
  multiplicity correspond; the case `m = 0`.
* `YuWangSamworth2015.correspondingEigenblock_basisDiagonal` and
  `YuWangSamworth2015.correspondingEigenblock_basisDiagonal_level`: the same for two
  operators presented diagonally, with the hypotheses reduced to arithmetic on
  the data.
-/

public section

open Module (finrank)
open Module.End (eigenspace)

namespace YuWangSamworth2015
open TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

open scoped Classical in
/-- **Eigenspaces at matching positions in the two spectra correspond.**

The general block-selection constructor.  `eigenspace A α` and `eigenspace B β`
occupy the *same* index range of their own sorted eigenbases exactly when the
same number of eigenvalues lies strictly above each and their multiplicities
agree; that common range is `[m, m + d)`.

Only the counts matter, not the values `α` and `β`, which is what the
Yu--Wang--Samworth setting needs: the perturbed block sits at the same ordered
position as the population block while carrying entirely different eigenvalues.
`correspondingEigenblock_topEigenspace` is the special case `m = 0`. -/
theorem correspondingEigenblock_eigenvalueLevel {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n)
    {α β : ℝ} {m d : ℕ}
    (hAcount : ({j | α < hA.eigenvalues hn j} : Finset (Fin n)).card = m)
    (hAmult : finrank 𝕜 (eigenspace A (α : 𝕜)) = d)
    (hBcount : ({j | β < hB.eigenvalues hn j} : Finset (Fin n)).card = m)
    (hBmult : finrank 𝕜 (eigenspace B (β : 𝕜)) = d) :
    CorrespondingEigenblock hA hB (eigenspace A (α : 𝕜)) (eigenspace B (β : 𝕜)) := by
  classical
  refine correspondingEigenblock_of_spanIndices hn
    {i : Fin n | m ≤ (i : ℕ) ∧ (i : ℕ) < m + d} ?_ ?_
  · rw [← hA.spanIndices_Ico_eq_eigenspace hn hAcount hAmult]
    congr 1
    ext i
    simp
  · rw [← hB.spanIndices_Ico_eq_eigenspace hn hBcount hBmult]
    congr 1
    ext i
    simp

/-- **Leading eigenspaces of equal multiplicity are corresponding eigenblocks.**

If `α` bounds every eigenvalue of `A` and `β` bounds every eigenvalue of `B`,
and both attained eigenspaces have dimension `d`, then those eigenspaces are
selected by the same index set `{i | i < d}` in the two sorted eigenvector
bases — which is exactly `CorrespondingEigenblock`.

This is `correspondingEigenblock_eigenvalueLevel` at `m = 0`: a bound that the
spectrum attains has nothing above it, so its block starts at index `0`. -/
theorem correspondingEigenblock_topEigenspace {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n)
    {α β : ℝ} {d : ℕ}
    (hAmax : ∀ i, hA.eigenvalues hn i ≤ α)
    (hAmult : finrank 𝕜 (eigenspace A (α : 𝕜)) = d)
    (hBmax : ∀ i, hB.eigenvalues hn i ≤ β)
    (hBmult : finrank 𝕜 (eigenspace B (β : 𝕜)) = d) :
    CorrespondingEigenblock hA hB (eigenspace A (α : 𝕜))
      (eigenspace B (β : 𝕜)) := by
  classical
  have hzero : ∀ (C : E →ₗ[𝕜] E) (hC : C.IsSymmetric) (γ : ℝ),
      (∀ i, hC.eigenvalues hn i ≤ γ) →
      ({j | γ < hC.eigenvalues hn j} : Finset (Fin n)).card = 0 := by
    intro C hC γ hmax
    refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun {j} _ => ?_)
    exact not_lt.mpr (hmax j)
  exact correspondingEigenblock_eigenvalueLevel hA hB hn (hzero A hA α hAmax) hAmult
    (hzero B hB β hBmax) hBmult

open scoped Classical in
/-- **The diagonal case.**  For operators presented in orthonormal bases the
hypotheses of `correspondingEigenblock_topEigenspace` become arithmetic: `α` and
`β` bound the coefficient lists, and the two level sets have `d` elements. -/
theorem correspondingEigenblock_basisDiagonal {n : ℕ}
    (b b' : OrthonormalBasis (Fin n) 𝕜 E) (c c' : Fin n → ℝ)
    (hn : finrank 𝕜 E = n) {α β : ℝ} {d : ℕ}
    (hc : ∀ i, c i ≤ α) (hc' : ∀ i, c' i ≤ β)
    (hcard : ({i | (c i : 𝕜) = (α : 𝕜)} : Finset (Fin n)).card = d)
    (hcard' : ({i | (c' i : 𝕜) = (β : 𝕜)} : Finset (Fin n)).card = d) :
    CorrespondingEigenblock (isSymmetric_basisDiagonal b c)
      (isSymmetric_basisDiagonal b' c')
      (eigenspace (basisDiagonal b c) (α : 𝕜))
      (eigenspace (basisDiagonal b' c') (β : 𝕜)) :=
  correspondingEigenblock_topEigenspace _ _ hn
    (eigenvalues_basisDiagonal_le b c hc hn)
    (by rw [finrank_eigenspace_basisDiagonal, hcard])
    (eigenvalues_basisDiagonal_le b' c' hc' hn)
    (by rw [finrank_eigenspace_basisDiagonal, hcard'])

open scoped Classical in
/-- **The diagonal case at an arbitrary level.**  The hypotheses of
`correspondingEigenblock_eigenvalueLevel` become arithmetic on the two
coefficient lists: equally many coefficients lie strictly above the two chosen
levels, and equally many lie at them.

Unlike `correspondingEigenblock_basisDiagonal` this places no maximality demand
on `α` and `β`, so it selects a block anywhere in the spectrum. -/
theorem correspondingEigenblock_basisDiagonal_level {n : ℕ}
    (b b' : OrthonormalBasis (Fin n) 𝕜 E) (c c' : Fin n → ℝ)
    (hn : finrank 𝕜 E = n) {α β : ℝ}
    (hcount : ({i | α < c i} : Finset (Fin n)).card
      = ({i | β < c' i} : Finset (Fin n)).card)
    (hmult : ({i | (c i : 𝕜) = (α : 𝕜)} : Finset (Fin n)).card
      = ({i | (c' i : 𝕜) = (β : 𝕜)} : Finset (Fin n)).card) :
    CorrespondingEigenblock (isSymmetric_basisDiagonal b c)
      (isSymmetric_basisDiagonal b' c')
      (eigenspace (basisDiagonal b c) (α : 𝕜))
      (eigenspace (basisDiagonal b' c') (β : 𝕜)) :=
  correspondingEigenblock_eigenvalueLevel _ _ hn
    (card_filter_lt_eigenvalues_basisDiagonal b c hn α)
    (finrank_eigenspace_basisDiagonal b c (α : 𝕜))
    ((card_filter_lt_eigenvalues_basisDiagonal b' c' hn β).trans hcount.symm)
    ((finrank_eigenspace_basisDiagonal b' c' (β : 𝕜)).trans hmult.symm)

end YuWangSamworth2015
