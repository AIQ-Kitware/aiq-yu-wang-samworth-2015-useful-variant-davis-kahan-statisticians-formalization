/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.Rectangular.Theorem4
import YuWangSamworth2015.Rectangular.RankOne
import YuWangSamworth2015.Rectangular.RankBoundary
import YuWangSamworth2015.Rectangular.SingularBlock
import YuWangSamworth2015.Rectangular.SourceTheorem3

/-!
# Rectangular Yu--Wang--Samworth surface

This aggregate exposes the right and left forms of the singular-subspace theorem
(Theorem 3 of the published article, Theorem 4 of the preprint) at the printed
generality, their aligned-frame conclusions, direct rank-one singular-vector
corollaries, the same theorems restated in consecutive singular-value notation
with the corrected boundary convention, the paper-facing wrappers that add the
source rank condition `1 <= r <= s <= rank(A)` and the exact printed denominator,
and the refutation of the printed rank-boundary convention.
-/
