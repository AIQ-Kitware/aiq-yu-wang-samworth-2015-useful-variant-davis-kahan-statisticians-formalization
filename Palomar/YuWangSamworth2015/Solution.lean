/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import YuWangSamworth2015.Core.Residual

/-!
# Solution: the Yu–Wang–Samworth population-gap sin-Θ theorem

The compared declaration is `YuWangSamworth2015.sqrt_sum_cross_le_of_population_gap`,
proved in `YuWangSamworth2015/Core/Residual.lean` of the accompanying development
and brought into scope by the import above.

The proof is deliberately not restated here. It reduces the Frobenius `sin Θ`
overlap to a Sylvester-type separation estimate, so duplicating it in a wrapper
would create a second copy to keep in step with the first; the wrapper's job is to
name the theorem, not to own its proof.
-/
