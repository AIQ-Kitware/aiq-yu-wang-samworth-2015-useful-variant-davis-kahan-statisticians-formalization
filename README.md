# Yu–Wang–Samworth 2015: the population-gap sin-Θ theorem, in Lean 4

A machine-checked proof of the first conclusion of Theorem 2 of Yu, Wang and
Samworth, *A useful variant of the Davis–Kahan theorem for statisticians*,
Biometrika 102(2), 2015, 315–323, <https://doi.org/10.1093/biomet/asv008>.

## The result

For a symmetric operator `T` on a finite-dimensional real or complex inner product
space, a symmetric perturbation `S`, and a set `s` of eigenvalue indices whose
selected eigenvalues are separated from the unselected ones by at least `Δ > 0`,

  `√(∑_{j ∈ s} ∑_{k ∉ s} |⟪uₖ, v̂ⱼ⟫|²)  ≤  2 √(∑ₖ ‖(S − T) uₖ‖²) / Δ`

where `uₖ` is an eigenvector basis of `T` and `v̂ⱼ` one of `S`. The left side is
the Frobenius norm of `sin Θ`, the sines of the principal angles between the two
selected eigenspaces.

## Why it matters

The classical Davis–Kahan bound uses the gap between the population eigenvalues
and the *sample* eigenvalues next to them — a quantity the statistician does not
observe and is generally trying to estimate. Yu, Wang and Samworth's variant takes
the separation entirely inside the population spectrum: every hypothesis here
constrains `T` alone, and `S` enters only through `‖S − T‖`. That is what makes
the bound usable, and why the paper is cited across spectral methods — principal
component analysis, spectral clustering, covariance estimation, and network models
where an adjacency or Laplacian matrix concentrates around a population version.

The statement is at the paper's scope: finite dimension, an arbitrary index set
rather than a leading block, and an `RCLike` field so the real and complex cases
are one theorem. The constant `2` is the paper's.

## Fidelity

This entry formalizes the printed first conclusion of Theorem 2 with no added
hypothesis and no weakened conclusion.

Two divergences elsewhere in the same paper are recorded in the substantive
repository's census and are **not** part of this entry: printed Equation (4) does
not stand as written and is corrected there, and the paper's rank-boundary
convention required a correction. The second conclusion of Theorem 2 — existence
of an aligned orthogonal frame with the printed `2^{3/2}` constant — is formalized
in the `YuWangSamworth2015` library included here, but is not compared here.

## Where this comes from

This repository is an **extraction**, not a fork with a life of its own.
[`AIQ-Kitware/aiq-dkps-formalization`](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
is authoritative: mathematics is developed, reviewed and audited there, and this
repository is a snapshot of the `ForTauCeti`, `DavisKahan` and `YuWangSamworth2015` packages taken from it, without the surrounding history and
without the packages that are not needed here. It exists so the entry can be read,
built and checked on its own, and so a reader is not asked to clone a much larger
multi-paper development to see one theorem's proof.

The practical consequence: **send changes upstream.** A fix made here and not made
there is lost at the next extraction. When the upstream packages move, this snapshot
is refreshed from them.

What is deliberately *not* extracted: the source census and the audit and gate scripts,
which are maintenance machinery for the authoritative repository. Accordingly this
repository makes no coverage claim about the paper as a whole.

The `DavisKahan` library is present because the Yu-Wang-Samworth package uses its
Hilbert-Schmidt/Frobenius ideal theory; it is a dependency here, not the subject.

The extraction is a copy of the package directories, so every module keeps its
upstream path, namespace and provenance header. The libraries build against a pinned
Mathlib and a pinned Tau Ceti, recorded in `lakefile.toml` and `lake-manifest.json`.

## Layout

```
Challenge.lean      the Palomar statement, against Mathlib alone, with a
                    deliberate statement-side hole
Solution.lean       the same declaration, supplied from the libraries below
comparator.json     what Comparator compares, and the permitted axioms
formalization.yaml  registry metadata
ForTauCeti/         reusable mathematics, in its final `TauCeti.*` namespaces
DavisKahan/         Davis--Kahan development, used here for its ideal theory
YuWangSamworth2015/ the Yu--Wang--Samworth development
```

`lake build` builds the entry. `lake build ForTauCeti`, `lake build DavisKahan` and `lake build YuWangSamworth2015` build the libraries.

## Status

Preparation. Nothing here claims registration, acceptance, or peer review by the
Palomar Registry.

