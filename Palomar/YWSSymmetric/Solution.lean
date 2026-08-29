/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import YuWangSamworth2015.Symmetric.Theorem2
import YuWangSamworth2015.Symmetric.Corollary1

/-!
# Solution: the Yu--Wang--Samworth population-gap theorems

The compared declarations are stated exactly as in the challenge module. The
vocabulary is repeated verbatim; the proofs are bridges to the paper-facing
theorems of the ordinary development, which is where the perturbation argument
lives. Nothing of that argument is restated here.

Two bridges do the work:

* `sinThetaDist` is the challenge's spelling of `TauCeti.sinThetaFrobenius` on the
  spans of the two frames, and `sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal`
  identifies them for orthonormal frames;
* `frobeniusNorm` is the challenge's spelling of the Frobenius unitarily
  invariant seminorm, and `UnitarilyInvariantSeminorm.frobenius_apply` identifies
  them at the standard basis.

The block, gap and eigenvector-block predicates are literally the development's
own paper-facing predicates, so they need no bridge.
-/

open TauCeti YuWangSamworth2015 YuWangSamworth2015.DavisKahanTheory

namespace YWSPalomar

open scoped InnerProductSpace BigOperators
open Module (finrank)

/-- The ambient space of the paper: real `p`-dimensional Euclidean space, on which
a real symmetric `p × p` matrix acts. -/
abbrev Rp (p : ℕ) : Type := EuclideanSpace ℝ (Fin p)

/-- `finrank ℝ (Rp p) = p`, so `Fin p` indexes the sorted spectrum. -/
theorem finrank_Rp (p : ℕ) : finrank ℝ (Rp p) = p := by simp

/-- **An eigenvector block at the indices `r, …, s`.**

`V` has orthonormal columns and its `i`-th column is an eigenvector of `Sigma` for
the `(r + i)`-th eigenvalue in nonincreasing order. Lean indices are zero-based,
so this is the paper's block `r, …, s` with one subtracted from its indices.

Nothing is assumed about multiplicity: at a repeated eigenvalue every orthonormal
choice inside the eigenspace satisfies this. -/
def IsEigenvectorBlock {p d r s : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V : Fin d → Rp p) : Prop :=
  Orthonormal ℝ V ∧
    ∀ i, Sigma (V i) =
      hSigma.eigenvalues (finrank_Rp p) (Fin.mk (r + (i : ℕ)) (by omega)) • V i

/-- **The population boundary gap of the block `r, …, s`.**

`Delta ≤ λ_{r−1} − λ_r` and `Delta ≤ λ_s − λ_{s+1}`. When the block starts at the
top or ends at the bottom the corresponding clause is vacuous, which is the
paper's `λ_0 = +∞` and `λ_{p+1} = −∞` written without extended reals.

Only the spectrum of `Sigma` occurs. There is no sample eigengap. -/
def PopulationBoundaryGap {p : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (∀ q j : Fin p, (q : ℕ) + 1 = r → (j : ℕ) = r →
      Delta ≤ hSigma.eigenvalues (finrank_Rp p) q
                - hSigma.eigenvalues (finrank_Rp p) j) ∧
    (∀ j q : Fin p, (j : ℕ) = s → (q : ℕ) = s + 1 →
      Delta ≤ hSigma.eigenvalues (finrank_Rp p) j
                - hSigma.eigenvalues (finrank_Rp p) q)

/-- **The paper's denominator `Δ = min(λ_{r−1} − λ_r, λ_s − λ_{s+1})`, exactly.**

Outside the full-block case this says `Delta` is the *greatest* real satisfying
both boundary inequalities, which is that minimum with a missing endpoint
omitted. For the full block `r = 0`, `s + 1 = p` there are no exterior
eigenvalues and the paper's conventions make both gaps `+∞`; the first disjunct
records that, and the theorems are then available for every positive `Delta`. -/
def SourcePopulationGap {p : ℕ}
    (Sigma : Rp p →ₗ[ℝ] Rp p) (hSigma : Sigma.IsSymmetric)
    (r s : ℕ) (Delta : ℝ) : Prop :=
  (r = 0 ∧ s + 1 = p) ∨
    (PopulationBoundaryGap Sigma hSigma r s Delta ∧
      ∀ delta : ℝ, PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta)

/-- **The Frobenius norm** `‖A‖_F = √(∑ᵢ ‖A eᵢ‖²)` over the standard basis. -/
noncomputable def frobeniusNorm {p : ℕ} (A : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  Real.sqrt (∑ i, ‖A (EuclideanSpace.basisFun (Fin p) ℝ i)‖ ^ 2)

/-- **The Frobenius `sin Θ` distance between the spans of two orthonormal frames**,

`‖sin Θ(V̂, V)‖_F = √(∑ⱼ ‖P_{span(V)^⊥} V̂ⱼ‖²)`,

the sines of the principal angles between the two blocks, measured by projecting
each sample frame vector off the population block. -/
noncomputable def sinThetaDist {p d : ℕ} (V Vhat : Fin d → Rp p) : ℝ :=
  Real.sqrt (∑ j, ‖(Submodule.span ℝ (Set.range V))ᗮ.starProjection (Vhat j)‖ ^ 2)

/-- The operator norm of a linear endomorphism of `Rp p`. -/
noncomputable abbrev opNorm {p : ℕ} (A : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  ‖LinearMap.toContinuousLinearMap A‖

/-- The paper's numerator `min(√d ‖E‖_op, ‖E‖_F)`. -/
noncomputable abbrev perturbation {p : ℕ} (d : ℕ) (E : Rp p →ₗ[ℝ] Rp p) : ℝ :=
  min (Real.sqrt d * opNorm E) (frobeniusNorm E)

section Bridges

variable {p d : ℕ}

/-- The challenge's Frobenius norm is the Frobenius unitarily invariant seminorm. -/
theorem frobeniusNorm_eq (A : Rp p →ₗ[ℝ] Rp p) :
    frobeniusNorm A = UnitarilyInvariantSeminorm.frobenius ℝ (Rp p) A :=
  (UnitarilyInvariantSeminorm.frobenius_apply ℝ (Rp p) A (finrank_Rp p)
    (EuclideanSpace.basisFun (Fin p) ℝ)).symm

/-- The challenge's `sin Θ` distance is the Frobenius sine distance between the
spans of the two frames. -/
theorem sinThetaDist_eq {V Vhat : Fin d → Rp p}
    (hV : Orthonormal ℝ V) (hVhat : Orthonormal ℝ Vhat) :
    sinThetaDist V Vhat =
      sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)) := by
  simp only [sinThetaDist]
  rw [← sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal hV hVhat]
  exact Real.sqrt_sq (sinThetaFrobenius_nonneg _ _)

/-- The challenge's numerator is the development's. -/
theorem perturbation_eq (E : Rp p →ₗ[ℝ] Rp p) :
    perturbation d E =
      min (Real.sqrt d * ‖LinearMap.toContinuousLinearMap E‖)
        (YuWangSamworth2015.frobeniusNorm E) := by
  rw [perturbation, frobeniusNorm_eq]

end Bridges

theorem theorem2_sinTheta {p d r s : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rp p)
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    sinThetaDist V Vhat ≤ 2 * perturbation d (SigmaHat - Sigma) / Delta := by
  rw [sinThetaDist_eq hV.1 hVhat.1, perturbation_eq]
  exact YuWangSamworth2015.theorem2_sinTheta Sigma SigmaHat hSigma hSigmaHat hr hs hd V Vhat
    hV hVhat _ rfl Delta hDelta hgap

theorem theorem2_alignedFrame {p d r s : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → Rp p)
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      Real.sqrt (∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
        2 * Real.sqrt 2 * perturbation d (SigmaHat - Sigma) / Delta := by
  rw [perturbation_eq]
  exact YuWangSamworth2015.theorem2_alignedFrame Sigma SigmaHat hSigma hSigmaHat hr hs hd
    V Vhat hV hVhat Delta hDelta hgap

theorem corollary1_sinTheta {p j : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hj : j < p) (v vHat : Rp p) (hv : ‖v‖ = 1) (hvHat : ‖vHat‖ = 1)
    (hSv : Sigma v = hSigma.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • v)
    (hShv : SigmaHat vHat = hSigmaHat.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • vHat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma j j Delta) :
    ‖(Submodule.span ℝ {vHat})ᗮ.starProjection v‖ ≤
      2 * opNorm (SigmaHat - Sigma) / Delta := by
  have hproj : ‖(Submodule.span ℝ {vHat})ᗮ.starProjection v‖
      = ‖projection (Submodule.span ℝ {vHat})ᗮ v‖ := rfl
  rw [hproj, ← sinThetaFrobenius_span_singleton (W := Submodule.span ℝ {vHat}) hv]
  exact YuWangSamworth2015.corollary1_sinTheta Sigma SigmaHat hSigma hSigmaHat hj v vHat
    hv hvHat hSv hShv _ rfl Delta hDelta hgap

theorem corollary1_alignedVector {p j : ℕ}
    (Sigma SigmaHat : Rp p →ₗ[ℝ] Rp p)
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hj : j < p) (v vHat : Rp p) (hv : ‖v‖ = 1) (hvHat : ‖vHat‖ = 1)
    (hSv : Sigma v = hSigma.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • v)
    (hShv : SigmaHat vHat = hSigmaHat.eigenvalues (finrank_Rp p) ⟨j, hj⟩ • vHat)
    (hsign : 0 ≤ inner ℝ vHat v)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma j j Delta) :
    ‖vHat - v‖ ≤ 2 * Real.sqrt 2 * opNorm (SigmaHat - Sigma) / Delta :=
  YuWangSamworth2015.corollary1_alignedVector Sigma SigmaHat hSigma hSigmaHat hj v vHat
    hv hvHat hSv hShv hsign Delta hDelta hgap

end YWSPalomar
