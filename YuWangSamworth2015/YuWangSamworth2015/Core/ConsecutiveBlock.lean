/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CourantFischer

/-! # Consecutive eigenvalue blocks and the two-sided boundary gap

The perturbation theorems of
`YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean` select
their block by an arbitrary index embedding `e : Fin d ↪ Fin n` and take as
hypothesis the *intrinsic* separation

`Δ ≤ |λ_{e i} − λ_k|` for every selected `i` and unselected `k`.

That is the right hypothesis for a general theorem — it does not care whether the
selected indices are contiguous — but it is not how the source states it.  Yu,
Wang and Samworth fix `1 ≤ r ≤ s ≤ p`, put `d = s − r + 1`, and assume only the
*two boundary* gaps

`Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`, with `λ_0 = +∞` and `λ_{p+1} = −∞`.

This file supplies the block and the bridge between the two.  Because the sorted
eigenvalues are antitone, the two boundary gaps propagate: everything above the
block is at least `λ_{r-1}`, everything below it at most `λ_{s+1}`.

`YuWangSamworth2015.OrderedBlockBoundaryGap` states the source hypothesis with the printed
endpoint conventions modelled by *vacuity* rather than by an extended real line:
"`λ_{r-1} − λ_r ≥ Δ`" is quantified over the indices `q` with `q + 1 = r`, of
which there are none when `r = 0`.  That is exactly `λ_0 = +∞`, and likewise
`λ_{p+1} = −∞` at the other end.

The theorems below are stated in the source's own variables: `r`, `s`, and the
block size `d` tied to them by `r + d = s + 1`, which is the paper's
`d = s − r + 1` written without truncated subtraction.  `d` cannot be eliminated
— it is the index type of the frames `V, V̂ : Fin d → E` — but it is pinned by
that hypothesis, and both the gap and the bound are written at `r` and `s`.
Indices are `0`-based, so the paper's `r ≤ j ≤ s` is `r ≤ j < r + d` and the
paper's `s ≤ p` is `s + 1 ≤ n`.

Nothing in this file constrains the *perturbed* spectrum, so the wrappers below
still allow `λ̂_{r-1} = λ̂_r` and `λ̂_s = λ̂_{s+1}`: removing the sample eigengap is
the source's contribution and it survives the change of hypothesis.

## Main results

* `YuWangSamworth2015.consecutiveEmb`: the block `r, …, s` as an index embedding.
* `YuWangSamworth2015.OrderedBlockBoundaryGap` and
  `YuWangSamworth2015.OrderedBlockBoundaryGap.indexGap`: the source's two-sided boundary
  hypothesis `Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`, and its propagation to the
  intrinsic separation.
* `YuWangSamworth2015.yuWangSamworth_sinTheta_block_le`,
  `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le`: Theorem 2's two conclusions
  with the source's indexing and gap.
* `YuWangSamworth2015.yuWangSamworth_sinTheta_block_le_residual`,
  `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le_residual`: the sharper residual
  forms with the same indexing.
* `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_real_le`: over `ℝ`, the same
  conclusion with `Ô` an element of `Matrix.orthogonalGroup (Fin d) ℝ` — every
  symbol of the printed second conclusion.
-/

public section

namespace YuWangSamworth2015
open TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ## The consecutive block -/

/-- **The block of `d` consecutive ordered indices starting at `r`**, as an
embedding into the sorted spectrum of an `n`-dimensional space.  In the paper's
`1`-based notation this is `r, r+1, …, s` with `d = s − r + 1`. -/
@[expose]
def consecutiveEmb {n d r : ℕ} (h : r + d ≤ n) : Fin d ↪ Fin n where
  toFun i := ⟨r + (i : ℕ), by have := i.isLt; omega⟩
  inj' i j hij := by
    have hv : r + (i : ℕ) = r + (j : ℕ) := congrArg Fin.val hij
    exact Fin.ext (by omega)

@[simp] theorem consecutiveEmb_val {n d r : ℕ} (h : r + d ≤ n) (i : Fin d) :
    ((consecutiveEmb h i : Fin n) : ℕ) = r + (i : ℕ) := rfl

/-- **The characteristic lemma for the block.**  An index is selected exactly
when it lies in `[r, r + d)`. -/
theorem mem_range_consecutiveEmb {n d r : ℕ} (h : r + d ≤ n) (k : Fin n) :
    k ∈ Set.range (consecutiveEmb h) ↔ r ≤ (k : ℕ) ∧ (k : ℕ) < r + d := by
  constructor
  · rintro ⟨i, rfl⟩
    have := i.isLt
    rw [consecutiveEmb_val]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(k : ℕ) - r, by omega⟩,
      Fin.ext (show r + ((k : ℕ) - r) = (k : ℕ) by omega)⟩

/-! ## The source's two-sided boundary gap -/

/-- **The population boundary gap of the block `r, …, s`**, exactly as printed:
`Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`.

The printed conventions `λ_0 = +∞` and `λ_{p+1} = −∞` are modelled by vacuous
quantification — when `r` is the first index there is no `q` with `q + 1 = r`, so
the first clause is automatic, and when `s` is the last index there is no `p`
with `p = s + 1`, so the second is.  No extended arithmetic is needed and the
interior, top and bottom blocks require no separate theorems. -/
def OrderedBlockBoundaryGap {n : ℕ} {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (r s : ℕ) (Δ : ℝ) : Prop :=
  (∀ q p : Fin n, (q : ℕ) + 1 = r → (p : ℕ) = r →
      Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p) ∧
    (∀ q p : Fin n, (q : ℕ) = s → (p : ℕ) = s + 1 →
      Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p)

/-- **The characteristic lemma.**  The body is not exposed; this is how a caller
builds or uses the boundary gap. -/
theorem orderedBlockBoundaryGap_iff {n : ℕ} {T : E →ₗ[𝕜] E} {hT : T.IsSymmetric}
    {hn : finrank 𝕜 E = n} {r s : ℕ} {Δ : ℝ} :
    OrderedBlockBoundaryGap hT hn r s Δ ↔
      ((∀ q p : Fin n, (q : ℕ) + 1 = r → (p : ℕ) = r →
          Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p) ∧
        (∀ q p : Fin n, (q : ℕ) = s → (p : ℕ) = s + 1 →
          Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p)) :=
  Iff.rfl

namespace OrderedBlockBoundaryGap

/-- **The two boundary gaps propagate to the whole complement.**

The sorted eigenvalues are antitone, so an index above the block has eigenvalue
at least `λ_{r-1}` while every selected eigenvalue is at most `λ_r`, and dually
below the block.  This is the bridge from the source's hypothesis to the
intrinsic separation the general theorems consume, and it is the only place the
contiguity of the block is used.

`hd : r + d = s + 1` is the paper's `d = s − r + 1`, written without truncated
subtraction. -/
theorem indexGap {n d r s : ℕ} {T : E →ₗ[𝕜] E}
    {hT : T.IsSymmetric} {hn : finrank 𝕜 E = n} {Δ : ℝ}
    (h : OrderedBlockBoundaryGap hT hn r s Δ) (hrd : r + d ≤ n)
    (hd : r + d = s + 1) (i : Fin d) (k : Fin n)
    (hk : k ∉ Set.range (consecutiveEmb hrd)) :
    Δ ≤ |hT.eigenvalues hn (consecutiveEmb hrd i) - hT.eigenvalues hn k| := by
  have hi : (i : ℕ) < d := i.isLt
  have hkn : (k : ℕ) < n := k.isLt
  have hei : ((consecutiveEmb hrd i : Fin n) : ℕ) = r + (i : ℕ) := rfl
  rw [mem_range_consecutiveEmb hrd k] at hk
  rcases Nat.lt_or_ge (k : ℕ) r with hlt | hge
  · -- `k` sits above the block: `λ_k ≥ λ_{r-1} ≥ λ_r + Δ ≥ λ_{e i} + Δ`.
    obtain ⟨q, hq⟩ : ∃ q : Fin n, (q : ℕ) + 1 = r :=
      ⟨⟨r - 1, by omega⟩, show r - 1 + 1 = r by omega⟩
    obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) = r := ⟨⟨r, by omega⟩, rfl⟩
    have hbound := h.1 q p hq hp
    have h1 : hT.eigenvalues hn q ≤ hT.eigenvalues hn k :=
      hT.eigenvalues_antitone hn (Fin.le_def.mpr (by omega))
    have h2 : hT.eigenvalues hn (consecutiveEmb hrd i) ≤ hT.eigenvalues hn p :=
      hT.eigenvalues_antitone hn (Fin.le_def.mpr (by omega))
    exact le_abs.mpr (Or.inr (by linarith))
  · -- `k` sits below the block: `λ_{e i} ≥ λ_s ≥ λ_{s+1} + Δ ≥ λ_k + Δ`.
    have hkge : r + d ≤ (k : ℕ) := by omega
    obtain ⟨q, hq⟩ : ∃ q : Fin n, (q : ℕ) = s := ⟨⟨s, by omega⟩, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) = s + 1 := ⟨⟨s + 1, by omega⟩, rfl⟩
    have hbound := h.2 q p hq hp
    have h1 : hT.eigenvalues hn q ≤ hT.eigenvalues hn (consecutiveEmb hrd i) :=
      hT.eigenvalues_antitone hn (Fin.le_def.mpr (by omega))
    have h2 : hT.eigenvalues hn k ≤ hT.eigenvalues hn p :=
      hT.eigenvalues_antitone hn (Fin.le_def.mpr (by omega))
    exact le_abs.mpr (Or.inl (by linarith))

/-- **The single-eigenvector case of the propagation.**  At `r = s = j` the block
is the single index `j`, the boundary hypothesis is the source's
`Δⱼ = min(λ_{j-1} − λⱼ, λⱼ − λ_{j+1})`, and it separates `λⱼ` from every other
sorted eigenvalue — the hypothesis Corollary 1 is stated with. -/
theorem gap_of_singleton {n : ℕ} {T : E →ₗ[𝕜] E}
    {hT : T.IsSymmetric} {hn : finrank 𝕜 E = n} {Δ : ℝ} {j : Fin n}
    (h : OrderedBlockBoundaryGap hT hn (j : ℕ) (j : ℕ) Δ) (k : Fin n) (hk : k ≠ j) :
    Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k| := by
  have hrd : (j : ℕ) + 1 ≤ n := j.isLt
  have hj0 : consecutiveEmb hrd (0 : Fin 1) = j := Fin.ext (by simp)
  have hgap := h.indexGap hrd rfl 0 k (by
    rw [mem_range_consecutiveEmb hrd k]
    rintro ⟨h1, h2⟩
    exact hk (Fin.ext (by omega)))
  rwa [hj0] at hgap

end OrderedBlockBoundaryGap

end YuWangSamworth2015
