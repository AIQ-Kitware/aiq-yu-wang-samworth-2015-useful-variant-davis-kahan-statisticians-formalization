/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.Symmetric.Theorem1
import YuWangSamworth2015.Symmetric.Theorem2
import YuWangSamworth2015.Symmetric.MixedGap
import YuWangSamworth2015.Symmetric.Corollary1
import YuWangSamworth2015.Symmetric.AngleIdentity
import YuWangSamworth2015.Symmetric.OrthogonalSharpness
import YuWangSamworth2015.Symmetric.MiddleBlockSharpness
import YuWangSamworth2015.Symmetric.PlanarSharpness

/-!
# Symmetric Yu--Wang--Samworth surface

This aggregate exposes:

* Theorem 1 in general unitarily invariant, Frobenius, and operator norms;
* Theorem 2 and its aligned-basis conclusion from
  `YuWangSamworth2015.Symmetric.Theorem2`;
* rank-one Corollary 1, in both the intrinsic and the printed
  neighbouring-eigenvalue-gap forms, with a sample-degeneracy witness;
* the exact rank-one double-angle identity recorded as equation (4);
* the Section 2 sharpness examples: orthogonal blocks in both the preprint's
  top-block and the published middle-block form -- the latter over its full
  parameter range `0 < ε < 3` -- which exhibit the aligned-basis
  constant `2^{3/2}` and the `√d` dimension dependence as unimprovable, and the
  planar rotation, which pins the sine bound's factor `2` at every angle
  including the small-angle regime.
-/
