# Palomar Registry submission surfaces

**Preparation only. Nothing here claims registration, approval, acceptance, or
peer review by the Palomar Registry.**

One subdirectory per prepared entry, each holding that entry's Comparator
configuration and — for the two paper-facing entries — that entry's
`formalization.yaml`. The Lean sources live under [`../Palomar/`](../Palomar) so
they build and can be verified in place.

| entry | metadata | compares | source relationship |
| --- | --- | --- | --- |
| `yws-symmetric` | `yws-symmetric/formalization.yaml` | Theorem 2, both conclusions; Corollary 1, both displays | `formalizes` — exact |
| `yws-rectangular` | `yws-rectangular/formalization.yaml` | Theorem 3, right and left, sine and aligned, plus the two singular-frame equivalences | `adapts` — source-corrected |
| `yws-2015` | — | one general-index-set form of Theorem 2's first conclusion | prototype/regression, superseded by `yws-symmetric` |

The clause-by-clause basis for every selection is
[`YWS_SOURCE_CONTRACT.md`](YWS_SOURCE_CONTRACT.md). What the entries claim, what
they do not, and the three printed source defects are in the repository
[`README.md`](../README.md).

A submission selects a Comparator path and a metadata path explicitly. The
repository-root `formalization.yaml` is the repository-wide record, not the
metadata of either entry.

An agent must not submit. Registration is permanent and is a maintainer decision.
