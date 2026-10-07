# Fixed-model training-conditional comparison

The old simulation changes Gaussian correlation when the calibration level changes.
It also uses an empirical rank in place of the paper's split-conformal rank.
Its bisection estimate is not an exact minimum correction.
The manuscript mixes one-sided and two-sided logarithms and describes simulated scores as released scores.

Use the 500 released cluster sizes, totaling 25,028 observations.
Fix the Gaussian copula at target coverage p=0.90.
Tune its score correlation once for indicator correlations 0.4946 and 0.20.
For each copula, simulate 200,000 independent calibration datasets through conditional binomial counts at p.
Use the same counts to compare every correction and seed 20260918.
Use rank ceil((n+1)*level), with rank above n giving an infinite threshold.
Use the one-sided logarithm log(1/delta) throughout, with delta=0.10.

Report exact binomial confidence intervals for Monte Carlo success probabilities.
Estimate the minimum rank from the count distribution and give a DKW uncertainty band.
Do not call a Monte Carlo estimate exact. Do not infer a general guarantee from a successful simulation.
Check a separate iid binomial control against its analytic probability.
Check the rank/count event identity on generated raw Gaussian samples.
Fail the run if the control misses by more than four Monte Carlo standard errors,
if rank/count events disagree, or if the clustered bound's upper confidence limit is below 0.90.
This is a model experiment using observed sizes, not an evaluation of released score coverage.
