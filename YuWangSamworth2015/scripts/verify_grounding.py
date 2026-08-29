#!/usr/bin/env python3
"""Static grounding checks for the YuWangSamworth2015 lane."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

REQUIRED_FILES = [
    "YuWangSamworth2015/YuWangSamworth2015/Core/Residual.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean",
    "ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean",
    "ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean",
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean",
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtFrobenius.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem1.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Symmetric/AngleIdentity.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Rectangular/FrobeniusGram.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Rectangular/Theorem4.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Rectangular/RankOne.lean",
    "YuWangSamworth2015/YuWangSamworth2015/Appendix/Lemma5.lean",
]

REQUIRED_DECLARATIONS = {
    "YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean": [
        "theorem yuWangSamworth_sinTheta_le",
        "theorem yuWangSamworth_alignedBasis_le",
        "theorem yuWangSamworth_eigenvector_le",
    ],
    "ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean": [
        "theorem sinTheta_perturbation_le",
        "theorem opNorm_sinThetaMap_le_of_intervalGap",
    ],
    "YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean": [
        "def IsEigenvectorBlock",
        "theorem isEigenvectorBlock_iff",
        "def PopulationBoundaryGap",
        "theorem populationBoundaryGap_iff",
        "def SourcePopulationGap",
        "theorem sourcePopulationGap_iff",
        "theorem toPopulationBoundaryGap",
        "theorem theorem2_sinTheta",
        "theorem theorem2_alignedFrame",
        "theorem yuWangSamworth_sinTheta_block_le",
        "theorem yuWangSamworth_alignedFrame_block_le",
        "theorem yuWangSamworth_alignedFrame_block_real_le",
    ],
    "YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem1.lean": [
        "theorem yuWangSamworth_theorem1_uiNorm_le",
        "theorem yuWangSamworth_theorem1_frobenius_le",
        "theorem yuWangSamworth_theorem1_opNorm_le",
    ],
    "YuWangSamworth2015/YuWangSamworth2015/Symmetric/AngleIdentity.lean": [
        "theorem yuWangSamworth_equation4",
        "theorem yuWangSamworth_equation4_printed_counterexample",
    ],
    "YuWangSamworth2015/YuWangSamworth2015/Rectangular/Theorem4.lean": [
        "theorem yuWangSamworth_rightSingularSubspace_le",
        "theorem yuWangSamworth_leftSingularSubspace_le",
        "theorem yuWangSamworth_rightSingularAlignedBasis_le",
        "theorem yuWangSamworth_leftSingularAlignedBasis_le",
    ],
    "YuWangSamworth2015/YuWangSamworth2015/Rectangular/RankOne.lean": [
        "theorem yuWangSamworth_rightSingularVector_le",
        "theorem yuWangSamworth_leftSingularVector_le",
    ],
    "YuWangSamworth2015/YuWangSamworth2015/Appendix/Lemma5.lean": [
        "theorem yuWangSamworth_lemma5_columns",
        "theorem yuWangSamworth_lemma5_isometricColumns",
        "theorem yuWangSamworth_lemma5_orthonormalColumns",
        "theorem yuWangSamworth_lemma5_rows",
        "theorem yuWangSamworth_lemma5_orthonormalRows",
    ],
}

for rel in REQUIRED_FILES:
    path = ROOT / rel
    if not path.is_file():
        raise SystemExit(f"missing grounded file: {rel}")

for rel, needles in REQUIRED_DECLARATIONS.items():
    text = (ROOT / rel).read_text()
    for needle in needles:
        if needle not in text:
            raise SystemExit(f"missing grounded declaration in {rel}: {needle}")

lane = ROOT / "YuWangSamworth2015"
for path in lane.rglob("*.lean"):
    text = path.read_text()
    for forbidden in ("sorry", "axiom "):
        if forbidden in text:
            raise SystemExit(f"forbidden placeholder in {path.relative_to(ROOT)}: {forbidden}")

print("YuWangSamworth2015 grounding audit: OK")
