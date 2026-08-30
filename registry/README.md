# Palomar Registry submission surfaces

**Preparation only. Nothing here claims registration, approval, acceptance, or
peer review by the Palomar Registry.**

One subdirectory per prepared entry, each holding that entry's Comparator
configuration and that entry's `formalization.yaml`. The Lean sources live under
[`../Palomar/`](../Palomar) so they build and can be verified in place.

**Why this directory is `registry/` and not `palomar/`.** It was `palomar/` until
2026-08-29, alongside the Lean library directory `Palomar/`. Two paths differing
only in case are the same path on a case-insensitive filesystem — Windows, and
macOS by default — so a checkout there could conflate them, refuse operations, or
simply differ from what Linux sees. A formalization advertised as independently
reproducible must not have a layout that is ambiguous on a common platform. The
names now differ structurally, and the split is conceptual rather than
capitalisation-based: `Palomar/` is Lean source, `registry/` is submission
configuration and metadata. Palomar selects the Comparator and metadata paths
explicitly, so neither has to live in a directory named after it.

| entry | metadata | compares | source relationship |
| --- | --- | --- | --- |
| `yws-symmetric` | `yws-symmetric/formalization.yaml` | Theorem 2, both conclusions; Corollary 1, both displays | `formalizes` — source-faithful |
| `yws-rectangular` | `yws-rectangular/formalization.yaml` | Theorem 3, right and left, sine and aligned, plus the two singular-frame equivalences | `adapts` — source-corrected |

Two entries, and only two. A general-index-set prototype of Theorem 2's first
conclusion was carried here until 2026-08-29; it proved the Palomar mechanics
work, `yws-symmetric` superseded it, and leaving it in a submission repository
only invited the question of which configuration was the claim. It was retired
from the authoritative repository too on 2026-08-30, when the embedded submission
surface there was removed; git history is its archive.

The clause-by-clause basis for every selection is
[`YWS_SOURCE_CONTRACT.md`](YWS_SOURCE_CONTRACT.md). What the entries claim, what
they do not, and the four printed source defects are in the repository
[`README.md`](../README.md).

A submission selects a Comparator path and a metadata path explicitly. The
repository-root `formalization.yaml` is the repository-wide record, not the
metadata of either entry.

An agent must not submit. Registration is permanent and is a maintainer decision.
