/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Application-owned formalization of the Yu--Wang--Samworth population-gap
residual argument.  This material intentionally lives downstream of
`ForTauCeti`: its hypotheses and constants are specialized to the 2015 paper,
while the reusable spectral and Hilbert-space infrastructure it consumes stays
in the foundation library.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CourantFischer
public import ForTauCeti.Analysis.InnerProductSpace.HoffmanWielandt
public import ForTauCeti.Analysis.InnerProductSpace.Spectral.ResidualGap

/-! # The Yu–Wang–Samworth Davis–Kahan variant (Frobenius, population gap)

For symmetric `T, S` on a finite-dimensional inner product space, fix an index
block `s` (the target eigenvectors).  Write `u` for `T`'s eigenbasis and `w` for
`S`'s.  The **sin-Θ overlap** between the `S`-block subspace `span (w j : j ∈ s)`
and the `T`-block subspace `span (u k : k ∈ s)` is

`overlap = ∑_{j ∈ s} ∑_{k ∉ s} ‖⟪u k, w j⟫‖²`.

Yu, Wang and Samworth bound this using only a **population eigengap**
`Δ ≤ |λⱼ(T) − λₖ(T)|` for `j ∈ s`, `k ∉ s` — a separation of `T`'s own spectrum,
with no mixed `T`/`S` term — at the cost of the constant `2`:

`Δ² · overlap ≤ 4 · ‖S − T‖²_F`,  i.e.  `‖sinΘ‖_F ≤ 2 ‖S − T‖_F / Δ`.

The proof is the residual sandwich around `Rⱼ = λⱼ(T) wⱼ − T wⱼ`:

* **Lower bound** (`Δ² overlap ≤ ∑_{j ∈ s} ‖Rⱼ‖²`): the cross-term identity
  `⟪uₖ, Rⱼ⟫ = (λⱼ(T) − λₖ(T)) ⟪uₖ, wⱼ⟫` uses *only* `T`-eigenvalues on both
  sides, so the population gap applies directly; Bessel's inequality then sums
  the complement block into `‖Rⱼ‖²`.
* **Upper bound** (`∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 ‖S − T‖²_F`): from
  `Rⱼ = (S − T) wⱼ − (λⱼ(S) − λⱼ(T)) wⱼ` and `(a + b)² ≤ 2a² + 2b²`, the two
  pieces are the Frobenius norm of `S − T` and — via **Hoffman–Wielandt** — the
  eigenvalue displacement, each `≤ ‖S − T‖²_F`.

## Main results

* `YuWangSamworth2015.sq_gap_mul_sum_cross_le_of_population_gap`: the squared bound
  `Δ² · overlap ≤ 4 · ∑ₖ ‖(S − T) uₖ‖²`.
* `YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap`: the `‖sinΘ‖_F` form
  `√overlap ≤ 2 · √(∑ₖ ‖(S − T) uₖ‖²) / Δ`.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), 315–323.  arXiv:1405.0680.

## Provenance

The residual argument was previously staged under
`ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/Residual.lean`.  On
2026-08-17 it moved into `YuWangSamworth2015.Core` because the population-only
gap sandwich is paper-specific application theory rather than foundation API.
Its reusable inputs remain in `ForTauCeti`; the move changes package ownership
and namespace, not the mathematical statement.

-/

public section

namespace YuWangSamworth2015
open TauCeti
open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- **The YWS population residual columns.** `residualColumn j = λⱼ(T) wⱼ − T wⱼ`,
where `wⱼ` is the `j`-th eigenvector of `S`.  Its `T`-eigenbasis coordinates are
governed by *population* eigenvalue differences (see
`inner_eigenvectorBasis_residualColumn`), which is what lets the population gap
drive the lower bound. -/
noncomputable def residualColumn (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (j : Fin n) : E :=
  (hT.eigenvalues hn j : 𝕜) • hS.eigenvectorBasis hn j - T (hS.eigenvectorBasis hn j)

/-- **T-only cross-term identity.** `⟪uₖ, Rⱼ⟫ = (λⱼ(T) − λₖ(T)) ⟪uₖ, wⱼ⟫`.  Both
eigenvalue multipliers are `T`'s, so a separation of `T`'s spectrum alone bounds
the coordinate.  (Contrast the mixed identity in `Spectrum.lean`.) -/
theorem inner_eigenvectorBasis_residualColumn (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (j k : Fin n) :
    ⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜
      = ((hT.eigenvalues hn j - hT.eigenvalues hn k : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜 := by
  simp only [residualColumn, inner_sub_right, inner_smul_right,
    ← hT (hT.eigenvectorBasis hn k) (hS.eigenvectorBasis hn j),
    hT.apply_eigenvectorBasis hn k, inner_smul_left, RCLike.conj_ofReal]
  push_cast
  ring

/-- Norm-square form of the cross-term identity. -/
theorem sq_norm_inner_eigenvectorBasis_residualColumn (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (j k : Fin n) :
    ‖⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜‖ ^ 2
      = (hT.eigenvalues hn j - hT.eigenvalues hn k) ^ 2
          * ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 := by
  rw [inner_eigenvectorBasis_residualColumn, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

/-- **Residual column as a perturbation column.**
`Rⱼ = (S − T) wⱼ − (λⱼ(S) − λⱼ(T)) wⱼ`, the identity behind the upper bound. -/
theorem residualColumn_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (j : Fin n) :
    residualColumn hT hS hn j
      = (S - T) (hS.eigenvectorBasis hn j)
        - ((hS.eigenvalues hn j - hT.eigenvalues hn j : ℝ) : 𝕜) • hS.eigenvectorBasis hn j := by
  rw [residualColumn, LinearMap.sub_apply, hS.apply_eigenvectorBasis hn j]
  push_cast
  module

/-- **Lower bound (population-gap separation).** With a population gap
`Δ ≤ |λⱼ(T) − λₖ(T)|` separating the block `s` from its complement, the sin-Θ
overlap is controlled by the residual columns: `Δ² · overlap ≤ ∑_{j ∈ s} ‖Rⱼ‖²`. -/
theorem sq_gap_mul_sum_cross_le_sum_sq_norm_residualColumn
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  -- Per column `j ∈ s`: `Δ² ∑_{k ∉ s} ‖⟪uₖ, wⱼ⟫‖² ≤ ‖Rⱼ‖²`.
  calc Δ ^ 2 * ∑ k ∈ sᶜ, ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      = ∑ k ∈ sᶜ, Δ ^ 2 * ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ k ∈ sᶜ, ‖⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜‖ ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [sq_norm_inner_eigenvectorBasis_residualColumn]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [show (hT.eigenvalues hn j - hT.eigenvalues hn k) ^ 2
            = |hT.eigenvalues hn j - hT.eigenvalues hn k| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ hΔ (hgap j hj k (Finset.mem_compl.mp hk)) 2
    _ ≤ ∑ k, ‖⟪hT.eigenvectorBasis hn k, residualColumn hT hS hn j⟫_𝕜‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => sq_nonneg _
    _ = ‖residualColumn hT hS hn j‖ ^ 2 :=
        (hT.eigenvectorBasis hn).sum_sq_norm_inner_right _

/-- **Upper bound (Hoffman–Wielandt).** The residual columns over the block are
bounded by the squared Frobenius norm of the perturbation:
`∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 · ∑ₖ ‖(S − T) uₖ‖²`.  From
`Rⱼ = (S − T) wⱼ − (λⱼ(S) − λⱼ(T)) wⱼ` and `(a + b)² ≤ 2a² + 2b²`, the two pieces
are the Frobenius norm and the eigenvalue displacement (bounded by
Hoffman–Wielandt), each `≤ ‖S − T‖²_F`. -/
theorem sum_sq_norm_residualColumn_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) :
    ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := by
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  -- Frobenius norm of `S − T` is basis-independent (evaluate on `S`'s eigenbasis).
  have hST : (S - T).IsSymmetric := hS.sub hT
  have hbasis : ∑ j, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2 = frob := by
    rw [sum_sq_norm_apply_eq_sum_sq_eigenvalues hST hn (hS.eigenvectorBasis hn), hfrob,
      sum_sq_norm_apply_eq_sum_sq_eigenvalues hST hn (hT.eigenvectorBasis hn)]
  -- Eigenvalue displacement is bounded by the Frobenius norm (Hoffman–Wielandt).
  have hHW : ∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2 ≤ frob := by
    rw [show (∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2)
        = ∑ j, (hT.eigenvalues hn j - hS.eigenvalues hn j) ^ 2 from
        Finset.sum_congr rfl fun j _ => by ring]
    exact sum_sq_eigenvalues_sub_le_sum_sq_norm_apply hT hS hn
  -- Per-column bound `‖Rⱼ‖² ≤ 2‖(S−T)wⱼ‖² + 2(λⱼ(S)−λⱼ(T))²`.
  have hcol : ∀ j, ‖residualColumn hT hS hn j‖ ^ 2
      ≤ 2 * ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
        + 2 * (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2 := by
    intro j
    have htri : ‖residualColumn hT hS hn j‖
        ≤ ‖(S - T) (hS.eigenvectorBasis hn j)‖
          + |hS.eigenvalues hn j - hT.eigenvalues hn j| := by
      rw [residualColumn_eq]
      refine (norm_sub_le _ _).trans_eq ?_
      rw [norm_smul, RCLike.norm_ofReal, (hS.eigenvectorBasis hn).orthonormal.norm_eq_one j,
        mul_one]
    have h1 : ‖residualColumn hT hS hn j‖ ^ 2
        ≤ (‖(S - T) (hS.eigenvectorBasis hn j)‖
            + |hS.eigenvalues hn j - hT.eigenvalues hn j|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [h1, sq_nonneg (‖(S - T) (hS.eigenvectorBasis hn j)‖
      - |hS.eigenvalues hn j - hT.eigenvalues hn j|),
      sq_abs (hS.eigenvalues hn j - hT.eigenvalues hn j)]
  calc ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2
      ≤ ∑ j ∈ s, (2 * ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
          + 2 * (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2) :=
        Finset.sum_le_sum fun j _ => hcol j
    _ ≤ ∑ j, (2 * ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
          + 2 * (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
    _ = 2 * ∑ j, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2
          + 2 * ∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * frob := by rw [hbasis]; linarith [hHW]

/-- **Yu–Wang–Samworth sin-Θ bound (Frobenius, population gap), squared form.**
With a population gap `Δ ≤ |λⱼ(T) − λₖ(T)|` separating the block `s` from its
complement, the sin-Θ overlap obeys `Δ² · overlap ≤ 4 · ‖S − T‖²_F`. -/
theorem sq_gap_mul_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 :=
  (sq_gap_mul_sum_cross_le_sum_sq_norm_residualColumn hT hS hn s hΔ hgap).trans
    (sum_sq_norm_residualColumn_le hT hS hn s)

/-- **Upper bound, operator-norm branch.** With `S − T` `ε`-operator-close, each
residual column obeys `‖Rⱼ‖ ≤ 2ε` (its two pieces are `‖(S − T) wⱼ‖ ≤ ε` and,
by Weyl, `|λⱼ(S) − λⱼ(T)| ≤ ε`), so `∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 · |s| · ε²`. -/
theorem sum_sq_norm_residualColumn_le_of_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) {ε : ℝ}
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2 ≤ 4 * s.card * ε ^ 2 := by
  have hcol : ∀ j, ‖residualColumn hT hS hn j‖ ^ 2 ≤ 4 * ε ^ 2 := by
    intro j
    have hEwj : ‖(S - T) (hS.eigenvectorBasis hn j)‖ ≤ ε := by
      have := hε (hS.eigenvectorBasis hn j)
      rwa [(hS.eigenvectorBasis hn).orthonormal.norm_eq_one j, mul_one] at this
    have hδ : |hS.eigenvalues hn j - hT.eigenvalues hn j| ≤ ε :=
      abs_eigenvalue_sub_eigenvalue_le hS hT hn hε j
    have htri : ‖residualColumn hT hS hn j‖ ≤ 2 * ε := by
      rw [residualColumn_eq]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofReal, (hS.eigenvectorBasis hn).orthonormal.norm_eq_one j,
        mul_one]
      linarith
    calc ‖residualColumn hT hS hn j‖ ^ 2 ≤ (2 * ε) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ = 4 * ε ^ 2 := by ring
  calc ∑ j ∈ s, ‖residualColumn hT hS hn j‖ ^ 2
      ≤ ∑ _j ∈ s, 4 * ε ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = 4 * s.card * ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Yu–Wang–Samworth sin-Θ bound (operator-norm branch, population gap).** With
`S − T` `ε`-operator-close, `Δ² · overlap ≤ 4 · d · ε²` where `d = |s|` is the
block size — the `√d ε` branch of Yu–Wang–Samworth. -/
theorem sq_gap_mul_sum_cross_le_of_population_gap_opNorm
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ ε : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|)
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * s.card * ε ^ 2 :=
  (sq_gap_mul_sum_cross_le_sum_sq_norm_residualColumn hT hS hn s hΔ hgap).trans
    (sum_sq_norm_residualColumn_le_of_opNorm hT hS hn s hε)

/-- **Yu–Wang–Samworth sin-Θ bound (Frobenius, population gap), `‖sinΘ‖_F` form.**
For a positive population gap `Δ`, `√overlap ≤ 2 · √(∑ₖ ‖(S − T) uₖ‖²) / Δ`, the
statistician's `‖sinΘ‖_F ≤ 2 ‖S − T‖_F / Δ`. -/
theorem sqrt_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Finset (Fin n)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2)
      ≤ 2 * Real.sqrt (∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2) / Δ := by
  set overlap := ∑ j ∈ s, ∑ k ∈ sᶜ,
    ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 with hov
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  have hkey := sq_gap_mul_sum_cross_le_of_population_gap hT hS hn s hΔ.le hgap
  rw [← hov, ← hfrob] at hkey
  have hov0 : 0 ≤ overlap := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hfr0 : 0 ≤ frob := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [le_div_iff₀ hΔ]
  -- `√overlap · Δ ≤ 2 √frob`; square both sides (both nonneg).
  have hsq : (Real.sqrt overlap * Δ) ^ 2 ≤ (2 * Real.sqrt frob) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hov0, mul_pow, Real.sq_sqrt hfr0]
    nlinarith [hkey]
  have hL : 0 ≤ Real.sqrt overlap * Δ := by positivity
  have hR : 0 ≤ 2 * Real.sqrt frob := by positivity
  nlinarith [hsq, hL, hR, sq_nonneg (Real.sqrt overlap * Δ - 2 * Real.sqrt frob)]

/-! ### The residual bounds for an arbitrary ordered eigenframe

The declarations above fix the perturbed block to be `S`'s *chosen* eigenbasis at
the indices `s`.  Yu, Wang and Samworth do not: their `V̂ = (v̂_r,…,v̂_s)` is any
orthonormal family with `Σ̂ v̂ⱼ = λ̂ⱼ v̂ⱼ`, and they deliberately assume no gap in
`λ̂`, so at a repeated sample eigenvalue the family is genuinely not determined.
`TauCeti.IsOrderedEigenframe` is that hypothesis, and the estimates below are the
upper half of the residual sandwich for it.

The ordering is used *only* on the eigenvalues: Weyl and Hoffman--Wielandt
compare `λⱼ(S)` with `λⱼ(T)` at the same index.  Nothing in either proof looks at
which eigenvector was chosen, which is exactly why the source theorem quantifies
over the choice. -/

section Frame

variable {d : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- **Orthonormal compression cannot increase the Frobenius norm.**
`∑ᵢ ‖M wᵢ‖² ≤ ∑ₖ ‖M bₖ‖²` for a symmetric `M`, an orthonormal *family* `w` and an
orthonormal *basis* `b`: expand each `M wᵢ` in `b`, move `M` across the inner
product by symmetry, and apply Bessel in `w`.

This is the appendix lemma of Yu--Wang--Samworth (`‖UᵀMW‖_F ≤ ‖M‖_F` for `U`, `W`
with orthonormal columns) in the half the main proof consumes, stated
basis-free. -/
theorem sum_sq_norm_apply_orthonormal_le (hM : (S - T).IsSymmetric)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {w : Fin d → E} (hw : Orthonormal 𝕜 w) :
    ∑ i, ‖(S - T) (w i)‖ ^ 2 ≤ ∑ k, ‖(S - T) (b k)‖ ^ 2 := by
  calc ∑ i, ‖(S - T) (w i)‖ ^ 2
      = ∑ i, ∑ k, ‖⟪b k, (S - T) (w i)⟫_𝕜‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => (b.sum_sq_norm_inner_right _).symm
    _ = ∑ k, ∑ i, ‖⟪w i, (S - T) (b k)⟫_𝕜‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← hM (b k) (w i), norm_inner_symm]
    _ ≤ ∑ k, ‖(S - T) (b k)‖ ^ 2 :=
        Finset.sum_le_sum fun k _ =>
          _root_.Orthonormal.sum_inner_products_le ((S - T) (b k)) hw

/-- **A sum over an index embedding is at most the full sum**, for nonnegative
terms.  The step that lets Weyl and Hoffman--Wielandt be applied only at the
selected indices. -/
private theorem sum_comp_embedding_le (g : Fin n → ℝ) (hg : ∀ j, 0 ≤ g j)
    (e : Fin d ↪ Fin n) : ∑ i, g (e i) ≤ ∑ j, g j := by
  classical
  rw [← Finset.sum_map Finset.univ e g]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hg j

/-- **The frame residual as a perturbation column.**
`λ_{e i}(T) wᵢ − T wᵢ = (S − T) wᵢ − (λ_{e i}(S) − λ_{e i}(T)) wᵢ`, using only the
eigenvalue equation of the frame. -/
theorem frameResidual_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : Fin d ↪ Fin n} {w : Fin d → E}
    (hw : IsOrderedEigenframe hS hn e w) (i : Fin d) :
    (hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)
      = (S - T) (w i)
        - ((hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i) : ℝ) : 𝕜) • w i := by
  rw [LinearMap.sub_apply, hw.apply_eq i]
  push_cast
  module

/-- **Frame residual, Frobenius branch.**  `∑ᵢ ‖Rᵢ‖² ≤ 4 ‖S − T‖²_F` for an
arbitrary ordered eigenframe `w` of `S`: the perturbation columns are bounded by
orthonormal compression and the eigenvalue displacement by Hoffman--Wielandt,
each by `‖S − T‖²_F`. -/
theorem sum_sq_norm_frameResidual_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : Fin d ↪ Fin n} {w : Fin d → E}
    (hw : IsOrderedEigenframe hS hn e w) :
    ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := by
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  have hST : (S - T).IsSymmetric := hS.sub hT
  -- The two halves, each bounded by the Frobenius norm.
  have hcols : ∑ i, ‖(S - T) (w i)‖ ^ 2 ≤ frob :=
    sum_sq_norm_apply_orthonormal_le hST (hT.eigenvectorBasis hn) hw.orthonormal
  have hHW : ∑ i, (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 ≤ frob := by
    refine (sum_comp_embedding_le
      (fun j => (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2)
      (fun j => sq_nonneg _) e).trans ?_
    rw [show (∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2)
        = ∑ j, (hT.eigenvalues hn j - hS.eigenvalues hn j) ^ 2 from
        Finset.sum_congr rfl fun j _ => by ring]
    exact sum_sq_eigenvalues_sub_le_sum_sq_norm_apply hT hS hn
  -- Per-column triangle inequality.
  have hcol : ∀ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ 2 * ‖(S - T) (w i)‖ ^ 2
        + 2 * (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 := by
    intro i
    have htri : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖
        ≤ ‖(S - T) (w i)‖ + |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)| := by
      rw [frameResidual_eq hT hS hn hw i]
      refine (norm_sub_le _ _).trans_eq ?_
      rw [norm_smul, RCLike.norm_ofReal, hw.orthonormal.norm_eq_one i, mul_one]
    have h1 : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
        ≤ (‖(S - T) (w i)‖
            + |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [h1, sq_nonneg (‖(S - T) (w i)‖
      - |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)|),
      sq_abs (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i))]
  calc ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ ∑ i, (2 * ‖(S - T) (w i)‖ ^ 2
          + 2 * (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2) :=
        Finset.sum_le_sum fun i _ => hcol i
    _ = 2 * ∑ i, ‖(S - T) (w i)‖ ^ 2
          + 2 * ∑ i, (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * frob := by linarith

/-- **Frame residual, operator-norm branch.**  `∑ᵢ ‖Rᵢ‖² ≤ 4 d ε²` when `S − T`
is `ε`-operator-close: each column splits as `‖(S − T) wᵢ‖ ≤ ε` and, by Weyl at
the *index* `e i`, `|λ_{e i}(S) − λ_{e i}(T)| ≤ ε`. -/
theorem sum_sq_norm_frameResidual_le_of_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : Fin d ↪ Fin n} {w : Fin d → E}
    (hw : IsOrderedEigenframe hS hn e w) {ε : ℝ}
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ 4 * d * ε ^ 2 := by
  have hcol : ∀ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ 4 * ε ^ 2 := by
    intro i
    have hEwi : ‖(S - T) (w i)‖ ≤ ε := by
      have := hε (w i)
      rwa [hw.orthonormal.norm_eq_one i, mul_one] at this
    have hδ : |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)| ≤ ε :=
      abs_eigenvalue_sub_eigenvalue_le hS hT hn hε (e i)
    have htri : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ≤ 2 * ε := by
      rw [frameResidual_eq hT hS hn hw i]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofReal, hw.orthonormal.norm_eq_one i, mul_one]
      linarith
    calc ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ (2 * ε) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ = 4 * ε ^ 2 := by ring
  calc ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ ∑ _i : Fin d, 4 * ε ^ 2 := Finset.sum_le_sum fun i _ => hcol i
    _ = 4 * d * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Frame

end YuWangSamworth2015
