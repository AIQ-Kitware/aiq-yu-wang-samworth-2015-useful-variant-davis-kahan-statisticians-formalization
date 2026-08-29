/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.GroundedImports

/-!
# Yu--Wang--Samworth equation (4)

The printed equation (4) omits a square on the factor
`2 - ‖v - u‖ ^ 2`.  The source expression is false for general unit vectors.
The theorem below records the corrected rank-one algebraic identity; its left
side is `sin²(2θ)` when `⟪v,u⟫_ℝ = cos θ`.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Corrected equation (4) of Yu--Wang--Samworth for real unit vectors.
The factor `2 - ‖v - u‖ ^ 2` must be squared. -/
theorem yuWangSamworth_equation4
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (2 * ⟪v, u⟫_ℝ) ^ 2 * (1 - ⟪v, u⟫_ℝ ^ 2) =
      (1 / 4 : ℝ) * ‖v - u‖ ^ 2 *
        (2 - ‖v - u‖ ^ 2) ^ 2 * (4 - ‖v - u‖ ^ 2) := by
  have hdist : ‖v - u‖ ^ 2 = 2 - 2 * ⟪v, u⟫_ℝ := by
    rw [norm_sub_sq_real, hv, hu]
    ring
  rw [hdist]
  ring

/-- The polynomial identity printed as equation (4), without the additional
square, already fails at inner product `3 / 5`.  This regression theorem keeps
the documented source correction machine checked. -/
theorem yuWangSamworth_equation4_printed_counterexample :
    (2 * (3 / 5 : ℝ)) ^ 2 * (1 - (3 / 5 : ℝ) ^ 2) ≠
      (1 / 4 : ℝ) * (2 - 2 * (3 / 5 : ℝ)) *
        (2 - (2 - 2 * (3 / 5 : ℝ))) *
          (4 - (2 - 2 * (3 / 5 : ℝ))) := by
  norm_num

end DavisKahanTheory
end YuWangSamworth2015
