# Palomar Registry submission surfaces

**Preparation only. Nothing here claims registration, approval, acceptance, or
peer review by the Palomar Registry.**

This repository intentionally carries **two** Palomar entries. Palomar registers
one Comparator configuration per entry, so forcing both claims into one root
`comparator.json` would make the submission surface less clear, not more
standard. Each entry therefore keeps its Comparator configuration and its own
`formalization.yaml` together under `registry/<entry>/`, and the submission
selects that exact path.

The Lean sources live under [`../Palomar/`](../Palomar). Each Challenge imports
Mathlib alone. Each Solution imports a Mathlib-only `SolutionPrelude` containing
the exact public-vocabulary prefix of its Challenge before importing the larger
proof development. Comparator recursively compares non-target constants, so
this arrangement prevents environment-sensitive elaboration of identical-looking
helper definitions from causing a Challenge/Solution constant mismatch.

**Why this directory is `registry/` and not `palomar/`.** It was `palomar/` until
2026-08-29, alongside the Lean library directory `Palomar/`. Two paths differing
only in case are the same path on a case-insensitive filesystem -- Windows, and
macOS by default -- so a checkout there could conflate them, refuse operations,
or simply differ from what Linux sees. A formalization advertised as independently
reproducible must not have a layout that is ambiguous on a common platform. The
names now differ structurally, and the split is conceptual rather than
capitalisation-based: `Palomar/` is Lean source; `registry/` is submission
configuration and metadata.

| entry | metadata | compares | source relationship |
| --- | --- | --- | --- |
| `yws-symmetric` | `yws-symmetric/formalization.yaml` | Theorem 2, both conclusions; Corollary 1, both displays | `formalizes` -- source-faithful |
| `yws-rectangular` | `yws-rectangular/formalization.yaml` | Theorem 3, right and left, sine and aligned, plus the two singular-frame equivalences | `adapts` -- source-corrected |

Two entries, and only two. A general-index-set prototype of Theorem 2's first
conclusion was carried here until 2026-08-29; `yws-symmetric` superseded it, and
leaving it in a submission repository only invited the question of which
configuration was the claim. It was retired from the authoritative repository
too on 2026-08-30, when the embedded submission surface there was removed; git
history is its archive.

The clause-by-clause basis for every selection is
[`YWS_SOURCE_CONTRACT.md`](YWS_SOURCE_CONTRACT.md). What the entries claim, what
they do not, and the documented printed-source defects are in the repository
[`README.md`](../README.md).

The repository-root `formalization.yaml` is the repository-wide record, not the
metadata of either Palomar entry. A submission must explicitly select one of:

```text
registry/yws-symmetric/comparator.json
registry/yws-rectangular/comparator.json
```

and the corresponding `formalization.yaml` beside it.

## Local verification

The full local check builds the exact Challenge/Solution modules named by both
Comparator configurations, verifies that each `SolutionPrelude` still matches
its Challenge vocabulary, runs the static preflight, then runs Comparator with
NanoDa and Lean kernel replay:

```bash
lake build
python3 scripts/check_palomar_readiness.py
python3 scripts/check_solution_preludes.py
scripts/verify_palomar.sh
```

To verify only one entry:

```bash
scripts/verify_palomar.sh yws-symmetric
scripts/verify_palomar.sh yws-rectangular
```

`scripts/verify_palomar.sh` uses verification tools already on `PATH`, otherwise
it discovers `~/.cache/palomar-tools-latest/bin`, then the newest dated
`~/.cache/palomar-tools-YYYYMMDD/bin`. If no compatible bundle exists,
`scripts/build_verification_tools.sh` builds the exact pinned tool revisions and
publishes `palomar-tools-latest` only after the complete bundle succeeds.

An agent must not submit. Registration is permanent and is a maintainer decision.
