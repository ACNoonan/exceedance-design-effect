# Reviewed numerical claims at this checkpoint

These decisions use the logged outputs and the model assumptions.
A retained simulation result is not a uniform error bound.
The complete claim ledger still needs manual review.

| Claims | Decision | Evidence and limit |
|---|---|---|
| CA-02: zero score correlation, design effect about 1.44 | Retain | The flip-mixture construction gives 13/9 at p=0.90. The finite-rank calculation uses p=k/(n+1), which changes the final decimals. |
| CA-03, CA-12, CA-13: 1.97, 1.54, 1.82 | Retain for the stated Gaussian example | The archive rerun gives 1.966, 1.538, and 1.821 with m=4 and score correlation 0.6. These are not universal level effects. |
| CA-04, CA-30, CA-31: 5.7×, 0.00096, 0.00552 | Retain as simulation summaries | The archive rerun reproduces the seven-cell sweep. The ratio compares two observed maximum errors. It is not a theorem about relative accuracy. |
| CA-23: 17% third-cumulant difference | Retain for the matched example | The corrected nested-structure run reports a 17.4% skewness difference. Equal means and variances make this also a relative third-cumulant difference. |
| CA-27: 0.17% drift agreement | Retain only as a four-case numerical comparison | Agreement in those Gaussian models cannot establish the unrestricted conjecture. The counterexample still refutes it. |
| CA-28, CA-34: about 1,300 effective observations and [0.876, 0.905] | Retain only for the randomized proxy bootstrap | The procedure changes tied scores by randomization. It does not reconstruct the original unreleased calibration score or its deployment guarantee. |
| CA-37: 1.9% spread across matched copulas | Retain as a finite simulation result | The run reports 1.94%. The two marginal transforms reuse the same copula draws. They are not six independent replications. |
| CA-18: pooled ICC estimates the shared-factor marginal correlation | Withdraw | Centering and empirical rank indicators remove a common additive shift within one deployment. The theoretical unconditional correlation is a different quantity. |
| CA-05, CA-29, CA-33: claims relying on unrestricted drift | Withdraw | Selected numerical agreement cannot repair the disproved unrestricted statement. |
| CA-42: extrapolated sampling-depth ceiling | Withdraw | Three beam widths cannot establish a limiting law. Transfer from the generated scores to the released proxy also lacks validation. |

Evidence files:

- `archive-core-check.log`
- `../corrected/nested_structure.log`
- `../corrected/drift_tables.log`
- `../runs/sim_validation.log`
- `../runs/prm_dispersion.log`
- `../STATUS.md`

The two compound-design scripts retain their historical failed checks.
`weighted-check.json` adds a separate comparison with deterministic moments and simulation uncertainty.
It supports the first-order weighted-CDF formula in the stated model, not a finite-sample identity.
