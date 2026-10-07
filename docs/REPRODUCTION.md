# Released-v8 reproduction ledger

Source: unchanged v8 archive. Input hashes and versions are recorded beside this file.
Runs use Python 3.14, not an exact recreation of the original Python 3.12 environment.
“Executed” means completion, not proof, numerical agreement, or scientific validation.

| Script | Outcome | Log |
|---|---|---|
| `_conformal.py` | Imported helper; no standalone experiment | — |
| `assumption_stress.py` | Executed; output review required before claim certification | [output](runs/assumption_stress.log) |
| `build_figures.py` | Presentation helper; not rerun from released archive | — |
| `calkit/__init__.py` | Imported helper; no standalone experiment | — |
| `calkit/conformal.py` | Imported helper; no standalone experiment | — |
| `ceiling_rho_response.py` | Executed; output review required before claim certification | [output](runs/ceiling_rho_response.log) |
| `composition_check.py` | Executed; output review required before claim certification | [output](runs/composition_check.log) |
| `compound_deff.py` | Executed; scientific checks report FAIL | [output](runs/compound_deff.log) |
| `compound_deff_sweep.py` | Executed; scientific checks report FAIL | [output](runs/compound_deff_sweep.log) |
| `condition6_check.py` | Executed; output review required before claim certification | [output](runs/condition6_check.log) |
| `deploy_gate/measure_conll.py` | Augmented run completed from cached scores; raw model scoring not rerun | — |
| `deploy_gate/verify_pasc_consequence.py` | Executed; output review required before claim certification | [output](runs/deploy_gate__verify_pasc_consequence.log) |
| `deployment_reframe.py` | Executed; output review required before claim certification | [output](runs/deployment_reframe.log) |
| `drift_coefficient.py` | Executed; output review required before claim certification | [output](runs/drift_coefficient.log) |
| `drift_tables.py` | Executed; output review required before claim certification | [output](runs/drift_tables.log) |
| `edgeworth_terms.py` | Executed; output review required before claim certification | [output](runs/edgeworth_terms.log) |
| `empirical_core/e1_shape_test.py` | Executed; output review required before claim certification | [output](runs/empirical_core__e1_shape_test.log) |
| `empirical_core/e2_beam_families.py` | Generation not rerun; cached aggregates inspected; seed/revisions unpinned | — |
| `empirical_core/p5b_cluster_budget.py` | Execution failed; augmented recovery recorded separately | [output](runs/empirical_core__p5b_cluster_budget.log) |
| `evt_lambda_u_estimation.py` | Executed; output review required before claim certification | [output](runs/evt_lambda_u_estimation.log) |
| `evt_tail_rate.py` | Executed; output review required before claim certification | [output](runs/evt_tail_rate.log) |
| `figure.py` | Presentation helper; not rerun from released archive | — |
| `icc_estimators.py` | Executed; output review required before claim certification | [output](runs/icc_estimators.log) |
| `informative_sizes.py` | Executed; output review required before claim certification | [output](runs/informative_sizes.log) |
| `jrc_bridge.py` | Executed; output review required before claim certification | [output](runs/jrc_bridge.log) |
| `known_pi_repair.py` | Executed; output review required before claim certification | [output](runs/known_pi_repair.log) |
| `marginal_guarantee_exact.py` | Executed; output review required before claim certification | [output](runs/marginal_guarantee_exact.log) |
| `nested_structure.py` | Executed; output review required before claim certification | [output](runs/nested_structure.log) |
| `nhanes/one_sided_rho_I.py` | Executed; output review required before claim certification | [output](runs/nhanes__one_sided_rho_I.log) |
| `overcoverage_bound.py` | Executed; output review required before claim certification | [output](runs/overcoverage_bound.log) |
| `prm_dispersion.py` | Executed; output review required before claim certification | [output](runs/prm_dispersion.log) |
| `prm_measurement.py` | Executed; output review required before claim certification | [output](runs/prm_measurement.log) |
| `prop1_combinatorial.py` | Executed; output review required before claim certification | [output](runs/prop1_combinatorial.log) |
| `prop1_edgeworth_probe.py` | Executed; output review required before claim certification | [output](runs/prop1_edgeworth_probe.log) |
| `prop1_exact.py` | Executed; output review required before claim certification | [output](runs/prop1_exact.log) |
| `ragged_and_estimation.py` | Executed; output review required before claim certification | [output](runs/ragged_and_estimation.log) |
| `residual_check.py` | Executed; output review required before claim certification | [output](runs/residual_check.log) |
| `reweighting_cost.py` | Executed; output review required before claim certification | [output](runs/reweighting_cost.log) |
| `sawtooth_fourier.py` | Executed; output review required before claim certification | [output](runs/sawtooth_fourier.log) |
| `sawtooth_integral.py` | Executed; scientific checks report FAIL | [output](runs/sawtooth_integral.log) |
| `selection/k1_construction.py` | Executed; output review required before claim certification | [output](runs/selection__k1_construction.log) |
| `selection_dose_response.py` | Executed; output review required before claim certification | [output](runs/selection_dose_response.log) |
| `sim_validation.py` | Executed; output review required before claim certification | [output](runs/sim_validation.log) |
| `sw02ext/q11_vovk_clustered.py` | Executed; output review required before claim certification | [output](runs/sw02ext__q11_vovk_clustered.log) |
| `sw12_lattice_edgeworth.py` | Executed; output review required before claim certification | [output](runs/sw12_lattice_edgeworth.log) |
| `sw12_uniform_nondegeneracy.py` | Executed; output review required before claim certification | [output](runs/sw12_uniform_nondegeneracy.log) |
| `sw15_epsilon_matched.py` | Executed; output review required before claim certification | [output](runs/sw15_epsilon_matched.log) |
| `sw52_direct_sim.py` | Executed; output review required before claim certification | [output](runs/sw52_direct_sim.log) |
| `test_marginal_scope.py` | Executed; output review required before claim certification | [output](runs/test_marginal_scope.log) |
| `trajectory_index.py` | Executed; output review required before claim certification | [output](runs/trajectory_index.log) |
| `unselected_slice.py` | Executed; output review required before claim certification | [output](runs/unselected_slice.log) |
| `verdict.py` | Imported helper; no standalone experiment | — |
| `verify_indicator_icc.py` | Executed; output review required before claim certification | [output](runs/verify_indicator_icc.log) |
| `verify_tail_limit.py` | Executed; output review required before claim certification | [output](runs/verify_tail_limit.log) |
| `weighting_deff.py` | Executed; output review required before claim certification | [output](runs/weighting_deff.log) |

## Augmented runs

`augmented/manifest.json` identifies supplied files and hashes.
CoNLL measurement and the tail-budget sweep completed with supplied local inputs.
The latter reproduces separation fractions 0.15, 0.30, 0.65, 0.85, and 1.00.
These recoveries do not repair the historical archive.

## Cached-output comparisons

The comparisons below read the original ZIP, not files overwritten during execution.
Identical text confirms reproduction of that output; it does not establish the truth of its interpretation.

- `assumption_stress.py`: output text identical.
- `ceiling_rho_response.py`: output text identical.
- `composition_check.py`: output text identical.
- `deployment_reframe.py`: output text identical.
- `drift_coefficient.py`: output text identical.
- `drift_tables.py`: output text identical.
- `evt_lambda_u_estimation.py`: output text identical.
- `informative_sizes.py`: output text identical.
- `jrc_bridge.py`: output text identical.
- `marginal_guarantee_exact.py`: output text identical.
- `nested_structure.py`: output text identical.
- `overcoverage_bound.py`: output text identical.
- `prm_dispersion.py`: output text identical.
- `prm_measurement.py`: output text identical.
- `prop1_combinatorial.py`: output text identical.
- `prop1_edgeworth_probe.py`: output text identical.
- `prop1_exact.py`: output text identical.
- `sim_validation.py`: output text identical.
- `test_marginal_scope.py`: output text identical.
- `trajectory_index.py`: text differs; [comparison](output-diffs/trajectory_index.diff).
- `verify_indicator_icc.py`: output text identical.
