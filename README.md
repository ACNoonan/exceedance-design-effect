# exceedance-design-effect

Verification code for **"Effective Sample Size for Conformal Calibration under Shared Ancestry."**

Concept DOI: [10.5281/zenodo.21595640](https://doi.org/10.5281/zenodo.21595640) — always resolves to
the newest version, and the only DOI worth citing.

---

## ⚠ Pre-release. The code is not here yet.

This repository exists so the paper can point somewhere stable. **The scripts land before the arXiv
posting**, after a pass for absolute paths, cached-dataset handling and lane-relative imports. If
you have arrived here from the paper and the directory below is empty, that is the expected state
and not a broken link — the archive attached to the Zenodo record is complete in the meantime.

## What will be here

Every number in the paper regenerates from these scripts. The manifest is checked against the
paper's reproduction appendix **in both directions at build time** — a script named in the paper and
absent from the archive is a hard error, not a warning.

| group | produces |
|---|---|
| the law | Theorem 1's simulation check, the naive score-correlation rival, copula-family invariance at matched diagonal |
| level-dependence | the tail limits by quadrature, the rate, and why the tail-dependence coefficient must not be estimated directly |
| ragged families | the size-biased substitution, its validated range, and the estimator comparison at known truth |
| the released instance | the process-reward calibration set: family structure, the cluster bootstrap, the tie-breaking that repairs continuity, and the i.i.d. and permuted-membership controls |
| the generated instance | beam search against independent sampling at 4,000 questions, with cluster-bootstrap intervals |
| the selection channel | the calibrated impossibility instance and the three repairs |
| the drift | two independent exact routes to the second-order term, sharing no code path |

## Two things worth knowing before running anything

**Controls come first, and they can fail.** Scripts print their preconditions before any headline
number. Several exist *because* a control failed: one quadrature script is retained precisely
because its precondition does not hold, which is how we learned the integral it estimates is zero.

**Two implementations of the conformal quantile are kept deliberately** — a research copy and an
earned copy — with an assertion that they return identical thresholds on random inputs, so no result
depends on which was used.

## Licence

Code: MIT. The paper and its figures: CC-BY 4.0, as on the Zenodo record.
