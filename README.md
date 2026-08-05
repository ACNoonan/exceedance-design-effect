# exceedance-design-effect

Verification code for **"The Exceedance Design Effect: Effective Sample Size for Thresholds under Clustering."**

Concept DOI: [10.5281/zenodo.21595640](https://doi.org/10.5281/zenodo.21595640), which always resolves to the newest version and is the only DOI worth citing. This tree is the v7 archive ([10.5281/zenodo.21798943](https://doi.org/10.5281/zenodo.21798943)), byte-identical to `sw02_verification_code.zip` on that record except for this README, whose section pointers are corrected for v7's section order (the coverage law is §2 and related work is §3; the zip's copy predates the swap).

Every number in the paper regenerates from these scripts. Python 3.11+, numpy, scipy, matplotlib.

| script | produces |
|---|---|
| `verify_indicator_icc.py` | §4.1, §4.2, §5 — the coverage law, the score-correlation rival, level-dependence |
| `drift_coefficient.py` | §4.3 — the O(1/b) drift coefficient, falsification tests, exchangeable control |
| `ragged_and_estimation.py` | §2.4 ragged families; §8 estimator bias and spread |
| `informative_sizes.py` | §2.5 — informative cluster sizes, simulated and measured on the PRM set |
| `prm_measurement.py` | §6.1 — the released PRM calibration set (downloads ~33 MB on first run) |
| `prm_dispersion.py` | §6.1 — MEASURES the dispersion ratio by cluster bootstrap (raw 1.09×, tie-broken 4.4×) against the plug-in 5.55; four preconditions incl. a synthetic ground-truth arm; needs the cache from `prm_measurement.py` |
| `trajectory_index.py` | §6.1 — recovers the trajectory index the release does not carry, by prefix-nesting: 3,961 maximal chains, $\rho_I$ 0.688 and design effect 7.06 at the trajectory level against 0.495 / 30.8 at the question level. Its P3 precondition re-derives §6.1's published question-level numbers from this independent path before the new ones are reported; needs the cache from `prm_measurement.py` |
| `test_marginal_scope.py` | §2.5, §6.1, §10 — the per-question / per-prefix test-marginal gap and its two baselines |
| `prop1_exact.py` | §4.3 — the exact drift table and the measured O(n^-2) remainder |
| `prop1_combinatorial.py` | §4.3 — the same drift by an exact combinatorial identity sharing no code path with `prop1_exact.py` |
| `prop1_edgeworth_probe.py` | §10 — shows Proposition 1's Edgeworth step is inert for the atom mixture: a continuity-corrected normal with no skewness term reaches the coefficient, its own error entering at O(n^-2) |
| `composition_check.py` | §2.3 — the negative-$\rho_I$ sweep ($n_\text{eff} > n$); ragged sizes and within-family structure composing |
| `nested_structure.py` | §4.4 — the invariance class, with the discriminability check |
| `assumption_stress.py` | §4.2's counterexample; §2.3 across-family dependence |
| `sim_validation.py` | Corollary 1 — copula-family invariance at matched delta(p) |
| `verify_tail_limit.py` | Proposition 3 — tail limits of rho_I, and the atom-mixture exact form |
| `build_figures.py` | all five figures |

The `*_RESULTS.txt` files are recorded outputs, included so the tables can be checked without
re-running. The exact scripts use no Monte Carlo and each asserts that independent clusters
reproduce the exact Beta mean before any clustered number is read. `prop1_exact.py` and
`prop1_combinatorial.py` reach §4.3's drift table by deliberately disjoint routes — one by FFT
convolution and Gauss-Legendre quadrature, the other by a combinatorial identity built from
hypergeometric CDFs — and agree to every printed digit.

`verdict.py` is the reporting helper the newer scripts route through: it refuses to print a verdict
without the raw evidence it reduced and the components it was computed from, and any failed
precondition forces the verdict to INCONCLUSIVE. It is pure stdlib and imports nothing.

`calkit/conformal.py` holds `split_conformal`; `_conformal.py` is a deliberate research-side
duplicate carrying `check_agrees_with_calkit()`, which asserts the two return identical thresholds
on 200 random inputs. It passes.


The third-party PRM dataset is NOT included here — `prm_measurement.py` fetches it from
https://huggingface.co/datasets/young-j-park/prm_calibration on first run.
`test_marginal_scope.py` reads the same cache and refuses to run without it rather than downloading
a second copy, so run `prm_measurement.py` first. It reproduces §6.1's family structure, $\rho_I$,
design effect and $n_\text{eff}$ from an independently written path — asserting the row and family
counts rather than assuming them — before reporting anything new.
