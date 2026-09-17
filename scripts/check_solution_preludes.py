#!/usr/bin/env python3
"""Keep the merged SolutionPrelude identical to the root Challenge vocabulary.

The root Challenge deliberately places every non-target helper declaration for
both YWS theorem families before any selected theorem. The Mathlib-only merged
SolutionPrelude reproduces that entire declaration sequence in the same order,
so environment-sensitive elaboration cannot differ between the two sides.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
CHALLENGE = ROOT / "Challenge.lean"
PRELUDE = ROOT / "Palomar/YWS/SolutionPrelude.lean"
TARGET_MARKER = "/-! ## Compared theorem declarations -/"


def normalize(text: str) -> str:
    text = re.sub(r"/--.*?-/", "", text, flags=re.S)
    text = re.sub(r"/-!.*?-/", "", text, flags=re.S)
    return " ".join(text.split())


def main() -> int:
    if not CHALLENGE.is_file() or not PRELUDE.is_file():
        print("FAIL  missing Challenge.lean or Palomar/YWS/SolutionPrelude.lean")
        return 1
    c = CHALLENGE.read_text()
    p = PRELUDE.read_text()
    try:
        c0 = c.index("namespace YWSPalomar")
        c1 = c.index(TARGET_MARKER, c0)
        p0 = p.index("namespace YWSPalomar")
    except ValueError as ex:
        print(f"FAIL  missing expected vocabulary marker: {ex}")
        return 1
    c_vocab = c[c0:c1]
    p_vocab = p[p0:]
    if normalize(c_vocab) != normalize(p_vocab):
        print("FAIL  merged SolutionPrelude does not match the complete Challenge vocabulary prefix")
        print("      compare Challenge.lean with Palomar/YWS/SolutionPrelude.lean")
        return 1
    print("  ok    merged vocabulary: SolutionPrelude matches complete Challenge helper prefix")
    return 0


if __name__ == "__main__":
    sys.exit(main())
