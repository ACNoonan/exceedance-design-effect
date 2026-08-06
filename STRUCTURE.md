# Structure — exceedance-design-effect

**Kind: artifact (public proof).** S1 applies. S2–S5 do not — the private research repo
`exceedance-paper` owns the row-space; this repo owns the demonstration.

*Added 2026-08-05 per [`~/Documents/STANDARD.md`](../STANDARD.md).*

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
docs/            reader-facing documentation
```

**House style:** `<claim>.py` paired with `<claim>_RESULTS.txt`, inside the directory for that
claim. The pair is the unit — script and its committed output travel together so a reader can
diff their run against ours. This is the pattern `exceedance-paper` should adopt for its own
root pile.

## Waivers

`_conformal.py` and `verdict.py` sit at root as shared modules imported across claim directories.
Root is at 3 files. Left as-is rather than moved to `src/` — a reader opening the repo should see
the verdict machinery immediately.
