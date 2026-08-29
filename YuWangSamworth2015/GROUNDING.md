# Grounding ledger

This package is checked by
`YuWangSamworth2015/scripts/verify_grounding.py` and is part of the default
build.  The source census is the current paper-coverage authority:
`dev/yu-wang-samworth-2015-full-source-census.json`.

The package builds only on repository-local, machine-checked results.

## Symmetric results

* `YuWangSamworth2015.Core.Statistics`
  * `yuWangSamworth_sinTheta_le`
  * `yuWangSamworth_alignedBasis_le`
  * `yuWangSamworth_eigenvector_le`
* `ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`
  * `sinTheta_perturbation_le`
  * `opNorm_sinThetaMap_le_of_intervalGap`

## Rectangular results

* `YuWangSamworth2015.Rectangular.FrobeniusGram`
* `YuWangSamworth2015.Rectangular.Theorem4`
* `YuWangSamworth2015.Core.SingularSubspace`

## Appendix compression

* `DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidt`
  * `paperHilbertSchmidtNorm_comp_le`
* `DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFrobenius`
  * finite-dimensional Frobenius realization

The grounding audit rejects proof placeholders or ungrounded external results in
the package closure.  Run it rather than relying on a dated audit statement:

```bash
python3 YuWangSamworth2015/scripts/verify_grounding.py
```

## Source audit: equation (4)

The printed equation (4) in arXiv:1405.0680 omits a square on the factor
`2 - ‖v̂ - v‖²`.  Direct substitution of
`‖v̂ - v‖² = 2 - 2⟪v̂,v⟫` shows that the correct identity contains
`(2 - ‖v̂ - v‖²)²`.  The formal theorem records this corrected identity, and
`yuWangSamworth_equation4_printed_counterexample` machine-checks a concrete
failure of the printed polynomial formula.
