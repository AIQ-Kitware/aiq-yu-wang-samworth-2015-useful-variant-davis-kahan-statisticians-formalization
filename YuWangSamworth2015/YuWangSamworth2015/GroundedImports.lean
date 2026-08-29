/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.Core.Residual
import YuWangSamworth2015.Core.Statistics
import YuWangSamworth2015.Core.SingularSubspace
import YuWangSamworth2015.Core.TopEigenblock
import YuWangSamworth2015.Core.Procrustes
import YuWangSamworth2015.Core.ConsecutiveBlock
import ForTauCeti.Analysis.InnerProductSpace.TwoLevelOperator
import ForTauCeti.Analysis.InnerProductSpace.RankOneSinTheta
import ForTauCeti.Analysis.InnerProductSpace.AlignedBasis
import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
import ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-!
# Grounded imports for the Yu--Wang--Samworth 2015 paper package

This module centralizes the dependency boundary of the paper package.  The
`ForTauCeti` imports below are reusable foundations; `YuWangSamworth2015.Core`
owns paper-specific population-gap machinery.  New paper-facing proofs should
import this module rather than silently reaching through unrelated experimental
trees.
-/
