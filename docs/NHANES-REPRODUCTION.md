# NHANES fixed-threshold survey comparison

This checks the implementation of a survey variance calculation. It does not validate the paper's quantile theorem.
The thresholds come from weighted empirical quantiles. The variance calculation then treats those thresholds as fixed.
It does not include threshold-selection uncertainty, item nonresponse adjustments, or a clinical interpretation.

The domain contains examined participants aged 18–70 with an observed value for the analyte.
The survey design retains every record with positive MEC weight, including records outside that domain.
The analysis pools 2013–2014, 2015–2016, and 2017–2018. It divides WTMEC2YR by three.
It uses the public masked strata and variance units. These are not known locations or collection teams.
The displayed design ratios combine weighting, stratification, and clustering.

CDC describes [combined weights](https://wwwn.cdc.gov/nchs/nhanes/tutorials/weighting.aspx)
and [domain variance estimation](https://wwwn.cdc.gov/nchs/nhanes/tutorials/varianceestimation.aspx).
Our implementation follows those conventions. Agreement with software does not establish the assumptions behind population inference.

## Inputs

Obtain the DEMO and BIOPRO XPT files for each of the three cycles from CDC's NHANES data pages.
The six exact filenames and their SHA-256 hashes appear in `nhanes/input-hashes.json`.
Raw data are separate from the code archive. The scripts do not download data.
The 2017–2018 [BIOPRO documentation](https://wwwn.cdc.gov/Nchs/Data/Nhanes/Public/2017/DataFiles/BIOPRO_J.htm)
describes the standard biochemistry profile.

## Commands from the archive root

Use an absolute path to the directory holding the six XPT files.

```sh
python run.py nhanes/nhanes_fixed_threshold.py --data-dir /path/to/nhanes --out nhanes/recomputed.json
python run.py nhanes/nhanes_samplics_check.py --data-dir /path/to/nhanes --results nhanes/recomputed.json --out nhanes/rechecked.json
```

The first script needs NumPy and pandas. The second also needs samplics 0.4.33.
The saved comparison records the independent environment's package versions.
The second script independently loads the data and uses samplics' Taylor estimator.
It reads the first script's thresholds to ensure both implementations evaluate the same fixed outcomes.

All 40 means and variances agree within the declared tolerances.
The largest relative variance difference is 1.5543122344752192e-15.
The v9 rerun produces the same result files as the earlier audit.
