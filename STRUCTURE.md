# Structure — exceedance-design-effect

**Kind: artifact (public proof).** S1 applies. S2–S5 do not — the private research repo
`exceedance-paper` owns the row-space; this repo owns the demonstration.

*Added 2026-08-05 per [`~/Documents/STANDARD.md`](../command-center/standard/artifact.md).*

## The one rule

> **Everything here must run for a stranger, from a clean checkout, and show the theorem is
> true.**

This is the public half of a deliberate visibility split. `exceedance-paper` (private) holds the
research work and the paper-writing architecture; this repo holds the verification a reader can
execute. **The two are not duplicates and must never be merged.**

## Map

Organized **by claim**, not by experiment — each directory verifies one part of the argument.

```
theory/          assumption stress, composition checks, admissibility
empirical_core/  the shape test, beam families, tail separability (e1/e2/p5)
deploy_gate/     the deployment consequence, measured on CoNLL
tails/           tail behaviour
selection/       the selection channel
prm/ nhanes/     real substrates
sw02ext/         extensions to SW-02
figures/         generated figures
calkit/          the shared conformal library (mirrored from calibrated-uncertainty)
neff/            the installable estimator package (pip install -e .): outcomes+ids,
                 pass@k spectra, thresholds at a level; `neff` CLI; see pyproject.toml
tests/           the package test suite (golden numbers + pass@k round trip)
docs/            reader-facing documentation
```

**House style:** `<claim>.py` paired with `<claim>_RESULTS.txt`, inside the directory for that
claim. The pair is the unit — script and its committed output travel together so a reader can
diff their run against ours. This is the pattern `exceedance-paper` should adopt for its own
root pile.

## Waivers

`_conformal.py`, `verdict.py` and `_icc.py` sit at root as shared modules imported across claim
directories. Root is at 4 files. Left as-is rather than moved to `src/` — a reader opening the repo should see
the verdict machinery immediately.

**`verdict.py` is a pinned vendored copy, deliberately not a symlink.** Every private lane
reaches the shared instrument by symlink into `~/Documents/research-vocab/verdict.py`, and this
repo must not: it is the public proof, so a link into a directory that exists only on Adam's
machine would dangle for anyone who clones it. The copy is what makes the repo self-contained
and the results re-runnable by a stranger, which is the entire point of an artifact repo.

The cost of that decision is the one this arrangement exists to prevent — the copy can fall
behind the canonical without anyone noticing. Two things hold it:

- `.vocab-pin` records the reason, which is what stands `canonical-symlink-gate` down. Without
  it the gate blocks edits here, because an unexplained copy is indistinguishable from a copy
  that drifted by accident.
- Refreshing is a deliberate act, not a sync: `cp ~/Documents/research-vocab/verdict.py .`,
  re-run the claim scripts, and update the sha in `.vocab-pin`. A refresh that changes a
  published number is a correction, and gets recorded as one.

Pinned at sha256 `29de96547ac2057e…` (2026-08-07), byte-identical to the canonical on that date.
