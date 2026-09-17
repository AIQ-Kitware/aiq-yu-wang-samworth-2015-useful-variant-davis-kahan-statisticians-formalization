# Palomar source-audit material

The active Palomar submission surface is the conventional single root entry:

```text
Challenge.lean
Solution.lean
comparator.json
formalization.yaml
```

`registry/` no longer contains separate Comparator configurations or metadata.
The former `yws-symmetric` and `yws-rectangular` entries were merged because they
are the two principal theorem families of the same Yu-Wang-Samworth paper:
Theorem 2/Corollary 1 for symmetric eigenspaces and Theorem 3 for right and left
singular subspaces of general matrices.

`YWS_SOURCE_CONTRACT.md` is the current clause-by-clause source contract for
the merged root selection. The old `registry/yws-*/comparator.json` and
`registry/yws-*/formalization.yaml` paths are historical and are no longer
submission surfaces.

The combined root metadata uses `relationship: adapts`, conservatively, because
the selected Theorem 3 family corrects a false printed rank-boundary convention.
Theorem 2 remains source-exact and Corollary 1 remains source-faithful with its
inherited unit normalization explicit.
