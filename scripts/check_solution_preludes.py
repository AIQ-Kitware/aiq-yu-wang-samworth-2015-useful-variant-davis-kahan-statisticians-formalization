#!/usr/bin/env python3
"""Keep YWS Solution public vocabulary identical to its Mathlib-only Challenge.

Comparator recursively compares non-target constants used by selected theorem
statements. Elaborating identical-looking helper definitions once under Mathlib
and once under the full proof development can produce different ConstantInfo.
The Solution therefore imports a Mathlib-only SolutionPrelude containing the
Challenge vocabulary prefix. This checker makes source drift fail locally.
"""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

ENTRIES = [
    (
        "yws-symmetric",
        ROOT / "Palomar/YWSSymmetric/Challenge.lean",
        ROOT / "Palomar/YWSSymmetric/SolutionPrelude.lean",
        "namespace YWSPalomar",
        "/-- **Theorem 2, first conclusion.**",
        "end YWSPalomar",
    ),
    (
        "yws-rectangular",
        ROOT / "Palomar/YWSRectangular/Challenge.lean",
        ROOT / "Palomar/YWSRectangular/SolutionPrelude.lean",
        "namespace YWSRectangular",
        "/-- **The Gram form of a right singular block is the paper's printed pair of",
        "end YWSRectangular",
    ),
]


def between(text: str, start: str, end: str, path: Path) -> str:
    try:
        i = text.index(start)
        j = text.index(end, i)
    except ValueError as ex:
        raise RuntimeError(f"{path}: missing expected marker {ex}") from ex
    return text[i:j].strip()


def main() -> int:
    failed = False
    for name, challenge, prelude, namespace, challenge_end, prelude_end in ENTRIES:
        if not prelude.is_file():
            print(f"FAIL  {name}: missing {prelude.relative_to(ROOT)}")
            failed = True
            continue
        c = between(challenge.read_text(), namespace, challenge_end, challenge)
        p = between(prelude.read_text(), namespace, prelude_end, prelude)
        if c != p:
            print(f"FAIL  {name}: SolutionPrelude does not exactly match Challenge vocabulary prefix")
            print(f"      compare {challenge.relative_to(ROOT)} with {prelude.relative_to(ROOT)}")
            failed = True
        else:
            print(f"  ok    {name}: SolutionPrelude exactly matches Challenge vocabulary prefix")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
