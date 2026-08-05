#!/usr/bin/env python3
"""
verdict.py — a verdict may never be the only thing printed.

WHY THIS EXISTS (2026-07-20)
    In one session, four separate experiments printed a confident verdict line
    that was wrong, while the raw data that would have exposed it was fine:
      - behavioral_eval printed "PASS" for an organism that emitted one string
        to everything (the generations were reduced to hostile/ok booleans first)
      - a pooling test printed "evasion survives" for a probe separating classes
        at AUROC 0.958 (the verdict read auroc<0.5 as "no detection")
      - a surprisal control printed "SURPRISAL confirmed" from a run whose
        manipulation had failed (B was lower-surprisal than A)
      - the H2 readout printed "not supported" while the J-lens surfaced the
        concept in words outside the fixed list (it saved hit-flags, not tokens)

    Two of those hid the evidence behind a lossy reduction; two printed a wrong
    verdict next to visible-but-ignored raw data. The fix is not "remember to
    look" — a discipline that compensates for output that hides evidence is just
    a second thing that fails. The fix is that the CODE cannot emit a bare
    verdict.

THE CONTRACT (enforced, not advisory)
    emit_verdict() REQUIRES:
      - `evidence`: a non-empty sample of the RAW items the verdict reduced,
        printed at full resolution BEFORE the verdict. Empty => raises. This is
        the strong enforcement: a verdict with no evidence is a programming
        error, caught at smoke-test time.
      - `components`: the numbers the verdict was computed from, printed so a
        wrong verdict is visibly inconsistent with its own inputs.
      - `preconditions`: REQUIRED and non-empty since 2026-07-27. Any False forces
        the verdict to INCONCLUSIVE and names the failed check. This is how a
        broken manipulation or a dead positive-control refuses to yield a verdict.
    emit_verdict() SUPPORTS:
      - `schema`: an optional registered output schema (see SCHEMAS) validated
        against `components`. Extension point for per-model / per-architecture /
        per-post-training-process output contracts, populated as we learn.

    Rule of adjudication: if the printed evidence and the verdict disagree, the
    evidence wins. The function makes the evidence impossible to skip.

THE SECOND ENFORCEMENT (2026-07-27) — a check that cannot fail is not evidence
    The 2026-07-20 contract stopped verdicts printed without evidence. It did not
    stop the failure mode that dominated 2026-07-25..27, which was upstream of
    every verdict: the INSTRUMENT was not reading what it was believed to read.

      - EL-pilot scored twins against twins. Three of four "twin arm" files were
        byte-identical human data (md5 00c92cfb). Caught only because accuracy
        came back at exactly 1.0000.
      - NI-01's gate 4b read a label logit at a position where one of the two
        models never answers: 0/12 argmax hits, 0.0 label probability mass. The
        readout would have measured noise and reported it as a result.
      - LD's design effect used m0 where SW-02 Theorem 1 requires m_tilde, making
        every effective sample size 1.81x too optimistic.

    In each case the code was correct and pointed at the wrong thing, so no
    verdict-side check could have caught it. What catches it is a precondition
    that COULD HAVE COME OUT WRONG — and the old `dict[str, bool]` could not
    express the difference between such a check and a tautology. `shape_correct`
    and `layer0_zero_positive_control` were the same type.

    So `Precondition` carries `would_fail_if`: in one clause, what a failure
    would have looked like. The block now prints EVERY precondition, passing ones
    included, with that clause beside it — because a passing check whose failure
    mode is unstated is indistinguishable from a check that could not fail, and
    reporting the second as confirmation is the error.

    Bare bools still work (13 legacy call sites) but render as
    `⚠ no failure mode stated` and are counted in
    `VerdictResult.unfalsifiable_preconditions`. Use `assert_could_have_failed()`
    when you want the strongest form: a check demonstrated to fail on a negative
    control before it is trusted on the real one.

THE THIRD ENFORCEMENT (2026-07-28) — §3 is prose, and prose does not bind
    The two contracts above cover the verdict and the instrument. Neither covers
    the pre-registration's own robustness commitments, and SA-01 walked straight
    through the gap: §3 committed to a `p_search ∈ {0.0, 0.25, 0.50}` sensitivity
    arm, the arm was never run, and a verdict was reported. Nothing failed —
    every precondition passed, §4's gate table was applied faithfully, the
    evidence was printed. The commitment was simply not a kind of object.

    Pass `prereg=<path to the .md>` and the ```commitments block in its §3 is
    parsed, each arm checked against the artifact that discharges it, and the
    results merged into `preconditions` — so an unrun arm voids the verdict
    through the same mechanism as a dead positive control. See `prereg.py`.
"""
from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass, field
from typing import Any, Callable, Sequence


# ---------------------------------------------------------------------------
# INSTRUMENT PROVENANCE (2026-08-04)
#
# On 2026-08-04 there were eight copies of this file across five repos: seven at 378
# lines and one 289 lines ahead, carrying `component_dominance()`, the §3 commitment
# enforcement and the control census that the other seven simply did not have. Five
# repos were running an instrument that had been improved elsewhere and never told.
#
# The copies were found by a filesystem scan — and a filesystem scan can only ever
# describe the state of the disk TODAY. It cannot say which version produced the
# numbers already sitting in a RESULTS file, which is the question that actually
# matters when a result is being defended. Worse, there were two such scanners with
# opposite policies, and on 2026-08-04 one of them exited 0 and printed "Gate 2 is
# uniform" while the other exited 1 on seven drifted copies.
#
# So the artifact records its own instrument. `verdict_sha256` makes two results
# comparable — same hash means the same enforcement ran, and that is checkable from
# the results alone, months later, with the working tree in any state. `vendored`
# distinguishes a lane that FOLLOWS the canonical (a symlink) from one deliberately
# pinned to the copy that produced its published numbers; both are legitimate, and
# conflating them is what made the drift invisible in the first place.
#
# Deliberately fail-open: provenance that can crash a verdict is worse than none.
def _digest(path: str) -> str | None:
    try:
        with open(path, "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()[:12]
    except OSError:
        return None


def _instrument_provenance() -> dict[str, Any]:
    try:
        here = os.path.abspath(__file__)
        real = os.path.realpath(here)
        prov: dict[str, Any] = {
            "verdict_sha256": _digest(real),
            "verdict_path": real,
            # A real file where a link belongs is a PIN, not necessarily a fork — see
            # `.vocab-pin` in research-vocab/vocab-link. Recording it here means the
            # distinction survives into the artifact instead of living only on disk.
            "vendored": not os.path.islink(here),
        }
        prereg_path = os.path.join(os.path.dirname(real), "prereg.py")
        if os.path.exists(prereg_path):
            prov["prereg_sha256"] = _digest(prereg_path)
        return prov
    except Exception:            # never let bookkeeping void a real result
        return {"verdict_sha256": None, "verdict_path": None, "vendored": None}


INSTRUMENT = _instrument_provenance()


# ---------------------------------------------------------------------------
# Output schema registry — the extension point Adam flagged 2026-07-20:
# "as we learn, we can define output schemas to enforce for different models,
#  architectures and post-training processes."
#
# A schema is a dict of {component_key: type-or-predicate}. Register schemas
# keyed by a stable name (e.g. "sft-organism-behavioral", "mass-mean-detection",
# "gemma3-jlens-readout") and pass schema=<name> to emit_verdict to validate the
# components dict against it. Start empty; populate as contracts stabilize.
# ---------------------------------------------------------------------------
SCHEMAS: dict[str, dict[str, Any]] = {}


def register_schema(name: str, spec: dict[str, Any]) -> None:
    """Register an output schema. `spec` maps component key -> type or
    callable(value)->bool. Re-registering the same name overwrites."""
    SCHEMAS[name] = spec


def _validate_schema(name: str, components: dict[str, Any]) -> list[str]:
    """Return a list of human-readable violations (empty = conforms)."""
    spec = SCHEMAS.get(name)
    if spec is None:
        return [f"schema {name!r} is not registered (SCHEMAS has "
                f"{sorted(SCHEMAS)})"]
    problems = []
    for key, expected in spec.items():
        if key not in components:
            problems.append(f"missing required component {key!r}")
            continue
        val = components[key]
        ok = expected(val) if callable(expected) else isinstance(val, expected)
        if not ok:
            problems.append(f"component {key!r}={val!r} fails {expected}")
    return problems


@dataclass(frozen=True)
class Precondition:
    """A check on the INSTRUMENT, carrying what its failure would have looked like.

    `would_fail_if` is not documentation. It is the field that separates a real
    control from a tautology, and writing it is the thinking step — if you cannot
    state how the check could have come out wrong, it is not evidence that it
    came out right.

    Good:
        Precondition(acc < 0.999, "twin scored against itself would give acc==1.0000", acc)
        Precondition(hits == n, "model answers elsewhere => argmax hit rate ~0", f"{hits}/{n}")
    Not a check:
        Precondition(arr.shape[1] == n_layers, "shape is wrong", arr.shape)   # cannot fail
    """

    passed: bool
    would_fail_if: str
    observed: Any = None
    # ── the negative-control record (2026-08-04) ────────────────────────────────────
    # `would_fail_if` is a CLAIM that the check could have come out wrong. These two
    # fields are the EVIDENCE for that claim, and the difference is not academic: on
    # 2026-08-03 an envelope probe shipped `censored = elapsed >= cell_budget * 0.98`
    # with a perfectly good failure mode written next to it, and the flag was false on
    # all ten cells by construction because nothing could reach that bound before two
    # tighter ones stopped it first. The prose was right; the check was inert.
    #
    # `control_demonstrated` is set by assert_could_have_failed() once the check has
    # been shown to FAIL on a known-bad input. `control_waived` is the explicit,
    # recorded escape hatch for checks where no control is constructible — it is a
    # string because a waiver has to name a reason someone can argue with, and because
    # `grep control_waived` then enumerates every soft spot in the programme.
    control_demonstrated: str | None = None
    control_waived: str | None = None

    def __post_init__(self) -> None:
        if not str(self.would_fail_if).strip():
            raise ValueError(
                "Precondition requires a non-empty `would_fail_if`. State in one "
                "clause what a failure would have looked like; a check whose "
                "failure mode you cannot name is not a check.")
        if self.control_demonstrated and self.control_waived:
            raise ValueError(
                "Precondition carries both a demonstrated control and a waiver. "
                "One or the other: a waiver next to a working control reads as if "
                "the control were optional.")

    @property
    def control_status(self) -> str:
        if self.control_demonstrated:
            return "demonstrated"
        return "waived" if self.control_waived else "none"


def assert_could_have_failed(name: str, check: Callable[[Any], bool], real: Any,
                             negative_control: Any) -> Precondition:
    """The strongest form: prove the check FAILS on a negative control, then run it for real.

    This is the encoding of a rule learned the expensive way — an invariance that
    cannot fail is not evidence, so before reporting that two things agreed, show
    that they could have disagreed. Raises if `check` passes on the control,
    because then a pass on the real input means nothing.

        assert_could_have_failed(
            "twin is not the human file",
            lambda d: accuracy(d) < 0.999,
            real=twin_frame,
            negative_control=human_frame,     # scoring this against itself gives 1.0
        )
    """
    if check(negative_control):
        raise ValueError(
            f"precondition {name!r} PASSES on its own negative control, so it "
            "cannot fail and proves nothing about the real input. Either the "
            "control is wrong or the check is a tautology.")
    # `observed=real`, not None. The old version discarded it, which cost the reader the
    # one thing that makes a wrong check repairable without re-running: on 2026-08-03 a
    # sub-call counter read a key the library never emits, and because only the derived
    # summary survived, ten cells of columns could not be recomputed and the run had to be
    # redone. A label without its inputs is not an observation.
    return Precondition(
        passed=bool(check(real)),
        would_fail_if=f"fails on the negative control by construction ({name})",
        observed=real,
        control_demonstrated=f"{name}: check returned False on the supplied negative control",
    )


def waive_control(passed: bool, would_fail_if: str, why_no_control: str,
                  observed: Any = None) -> Precondition:
    """A precondition with NO negative control, and a recorded reason.

    Use when a control is genuinely not constructible — not when one is merely
    inconvenient. The reason is stored in the artifact and printed in the verdict, so
    `grep control_waived` over a repo enumerates every place the programme is trusting
    prose instead of a demonstration. That list is meant to be short and to be read.
    """
    if not str(why_no_control).strip():
        raise ValueError(
            "waive_control requires a reason. 'No control' with no argument attached "
            "is indistinguishable from not having thought about it.")
    return Precondition(passed=bool(passed), would_fail_if=would_fail_if,
                        observed=observed, control_waived=why_no_control)


def component_dominance(derived_name: str, derived: float,
                        components: dict[str, float],
                        margin: float = 0.0) -> Precondition:
    """A derived metric must beat the parts it is computed FROM, or it is noise amplification.

    Learned from SA-01. MSCE's contrast is built out of a with-side mean; the
    contrast scored AUC 0.4648 -- inside the null -- while the with-side mean it
    is computed from scored 0.7206. The clever estimator was 0.26 AUC *worse*
    than its own input, and the story attached to it ("cancel the confound") was
    good enough that nobody asks this question by default. Subtracting a quantity
    that depends on the action removes the signal along with the confound.

    Pass the derived score and every constituent you can name. The check fails
    when any constituent beats the derived metric by more than `margin`, and the
    failure mode is stated for you.

        component_dominance("cca", auc_cca,
                            {"with-side mean": auc_eff, "clean-episode mean": auc_base})

    This is deliberately cheap and deliberately general: any contrast, residual,
    difference-in-means, or normalisation owes it, in any lane.
    """
    if not components:
        raise ValueError(
            f"component_dominance({derived_name!r}) needs at least one constituent. "
            "A derived metric with no named inputs cannot be checked against them, "
            "and 'I could not name the parts' is a reason to distrust the metric.")
    beaten = {k: v for k, v in components.items() if v > derived + margin}
    best = max(components, key=lambda k: components[k])
    return Precondition(
        passed=not beaten,
        would_fail_if=(
            f"a constituent of {derived_name!r} scores higher than {derived_name!r} "
            f"itself, which would mean the derivation destroyed signal rather than "
            f"isolating it"),
        observed=(f"{derived_name}={derived:.4f}; best constituent "
                  f"{best}={components[best]:.4f}"
                  + (f"; BEATEN BY {sorted(beaten)}" if beaten else "")),
    )


def _as_precondition(value: "bool | Precondition") -> tuple[bool, str | None, Any]:
    """Normalise either accepted form to (passed, would_fail_if_or_None, observed).

    DUCK-TYPED, not isinstance-checked, and the smoke test is why. `prereg.py`
    does `from verdict import Precondition`; when verdict.py runs as `__main__`
    that is a DIFFERENT class object from the one in scope here, so isinstance
    returned False, the value fell through to the bare-bool branch, and
    `bool(<any dataclass>)` is True — a FAILED precondition silently passing.
    The same trap fires for any caller that reaches this module by two import
    paths. Anything that is not a bool and is not precondition-shaped now raises
    rather than being coerced, because that coercion is precisely the
    check-that-cannot-fail this module exists to stop.
    """
    if isinstance(value, bool):
        return value, None, None
    passed = getattr(value, "passed", None)
    why = getattr(value, "would_fail_if", None)
    if isinstance(passed, bool) and isinstance(why, str):
        return passed, why, getattr(value, "observed", None)
    if isinstance(value, int):          # 0/1 from a numpy-free count
        return bool(value), None, None
    item = getattr(value, "item", None)  # np.bool_ / np.True_ from a legacy site
    if callable(item):
        try:
            scalar = item()
        except (TypeError, ValueError):
            scalar = None
        if isinstance(scalar, (bool, int)):
            return bool(scalar), None, None
    raise TypeError(
        f"precondition value {value!r} is neither a bool nor precondition-shaped "
        "(.passed: bool, .would_fail_if: str). Coercing it with bool() would make "
        "it pass unconditionally.")


def _control_status(value: "bool | Precondition") -> str:
    """'demonstrated' | 'waived' | 'none' — duck-typed for the same reason
    _as_precondition is: a Precondition reaching here by a second import path is a
    different class object, and isinstance would silently call it a bare bool."""
    if isinstance(value, bool):
        return "none"
    if getattr(value, "control_demonstrated", None):
        return "demonstrated"
    if getattr(value, "control_waived", None):
        return "waived"
    return "none"


def _control_reason(value: "bool | Precondition") -> str:
    return str(getattr(value, "control_waived", "") or "")


@dataclass
class VerdictResult:
    """Machine-readable form — carries the evidence, not just the label, so the
    JSON/MLflow record is auditable the same way the console output is."""
    label: str
    inconclusive: bool
    components: dict[str, Any]
    evidence: list[Any]
    failed_preconditions: list[str] = field(default_factory=list)
    schema_violations: list[str] = field(default_factory=list)
    unfalsifiable_preconditions: list[str] = field(default_factory=list)
    undischarged_commitments: list[str] = field(default_factory=list)
    # Which preconditions proved they could fail, which named a reason they cannot, and
    # which did neither. The third list is the one to read: those checks passed, and
    # nothing establishes that they were capable of doing anything else.
    uncontrolled_preconditions: list[str] = field(default_factory=list)
    waived_controls: dict[str, str] = field(default_factory=dict)
    control_policy: str = "warn"
    # Which verdict.py emitted this. See INSTRUMENT above — this is what makes two
    # results comparable without re-scanning the filesystem they were produced on.
    instrument: dict[str, Any] = field(default_factory=lambda: dict(INSTRUMENT))

    def to_dict(self) -> dict:
        return {
            "verdict": self.label,
            "inconclusive": self.inconclusive,
            "components": self.components,
            "evidence_sample": self.evidence,
            "failed_preconditions": self.failed_preconditions,
            "schema_violations": self.schema_violations,
            "unfalsifiable_preconditions": self.unfalsifiable_preconditions,
            "undischarged_commitments": self.undischarged_commitments,
            "uncontrolled_preconditions": self.uncontrolled_preconditions,
            "waived_controls": self.waived_controls,
            "control_policy": self.control_policy,
            "instrument": self.instrument,
        }


def emit_verdict(
    title: str,
    *,
    evidence: Sequence[Any],
    components: dict[str, Any],
    rules: Sequence[tuple[bool, str]] = (),
    preconditions: dict[str, "bool | Precondition"],
    prereg: "str | Any | None" = None,
    schema: str | None = None,
    require_controls: str | None = None,
    evidence_formatter: Callable[[Any], str] | None = None,
    width: int = 74,
) -> VerdictResult:
    """Print raw evidence, then components, then the verdict. Return the
    structured result. REFUSES (raises ValueError) if `evidence` is empty —
    that is the enforcement.

    Args:
        title: header for the block.
        evidence: non-empty sample of the raw items the verdict reduced. Printed
            first, at full resolution. Empty => ValueError.
        components: the values the verdict was computed from. Printed next.
        rules: ordered (condition, label). First true wins. If none match the
            label is "UNDETERMINED".
        preconditions: REQUIRED, non-empty. name -> Precondition (preferred) or
            bare bool (legacy). Any False => verdict forced to INCONCLUSIVE.
            Empty => ValueError: a verdict whose instrument was never checked is
            the 2026-07-25..27 failure mode, not an edge case.
        prereg: path to the pre-registration .md. Its ```commitments block is
            parsed and every §3 robustness arm checked against the artifact that
            discharges it; undischarged arms are merged in as failed
            preconditions, voiding the verdict. A prereg with no such block
            raises — its §3 is still prose, which is what SA-01 walked through.
        schema: optional registered schema name to validate `components`.
        evidence_formatter: how to render one evidence row (default: repr, but
            dicts are pretty-printed compactly).
    """
    if not evidence:
        raise ValueError(
            f"emit_verdict({title!r}) called with no evidence. A verdict with "
            "nothing to falsify it is exactly the failure this module exists to "
            "prevent. Pass a sample of the raw items the verdict reduces.")

    if not preconditions:
        raise ValueError(
            f"emit_verdict({title!r}) called with no preconditions. Every "
            "expensive error of 2026-07-25..27 was an instrument pointed at the "
            "wrong thing, upstream of any verdict: twins scored against human "
            "data, a logit read where the model never answers, a design effect "
            "built on the wrong cluster statistic. State at least one check that "
            "COULD HAVE COME OUT WRONG — see Precondition.would_fail_if.")

    # §3 commitments become preconditions before anything is normalised, so an
    # unrun robustness arm and a dead positive control void the verdict by the
    # same path. Deliberately fail-closed: a broken/absent block raises here
    # rather than quietly leaving the commitments unchecked.
    commitments: dict[str, Precondition] = {}
    if prereg is not None:
        import prereg as _prereg_mod
        commitments = _prereg_mod.preconditions(prereg)
        preconditions = {**preconditions, **commitments}

    normalised = {name: _as_precondition(v) for name, v in preconditions.items()}
    failed = [name for name, (ok, _, _) in normalised.items() if not ok]
    unfalsifiable = [name for name, (_, why, _) in normalised.items() if why is None]
    violations = _validate_schema(schema, components) if schema else []

    # ── the control census (2026-08-04) ────────────────────────────────────────────
    # `would_fail_if` says the check COULD have failed. That is a claim, and until
    # 2026-08-04 nothing in this module asked for evidence of it. The gap is not
    # hypothetical: an envelope probe shipped a censoring flag with a well-written
    # failure mode that was false on every cell by construction, because the bound it
    # watched was unreachable behind two tighter ones. Prose was right, check was inert.
    #
    # POLICY IS RESOLVED FROM THE ENVIRONMENT, NOT INFERRED. Flipping this to "block"
    # globally today would break every existing lane at once, and a gate that forces a
    # mass edit gets disabled rather than adopted. So it is per-lane and explicit:
    # VERDICT_REQUIRE_CONTROLS=block in a lane that has been migrated (and in CI),
    # "warn" everywhere else. Either way the census prints and lands in the artifact,
    # so the uncontrolled set is visible from day one rather than after the migration.
    policy = (require_controls or os.environ.get("VERDICT_REQUIRE_CONTROLS", "warn")).lower()
    if policy not in ("block", "warn", "off"):
        raise ValueError(
            f"require_controls={policy!r} — expected 'block', 'warn' or 'off'. "
            "An unrecognised policy silently becoming permissive is the shape of "
            "defect this module exists to stop.")
    controls = {name: _control_status(v) for name, v in preconditions.items()}
    uncontrolled = [n for n, s in controls.items() if s == "none"]
    waived = {n: _control_reason(preconditions[n]) for n, s in controls.items()
              if s == "waived"}
    if policy == "block" and uncontrolled:
        raise ValueError(
            f"emit_verdict({title!r}): {len(uncontrolled)} precondition(s) have no "
            f"negative control and no recorded waiver: {', '.join(sorted(uncontrolled))}. "
            "Each one passed without anything establishing it could have failed. Use "
            "assert_could_have_failed(...) to demonstrate the failure mode, or "
            "waive_control(..., why_no_control='...') to record why none is "
            "constructible. VERDICT_REQUIRE_CONTROLS=warn downgrades this to a notice.")

    def fmt(row: Any) -> str:
        if evidence_formatter:
            return evidence_formatter(row)
        if isinstance(row, dict):
            return "  ".join(f"{k}={v!r}" for k, v in row.items())
        return repr(row)

    line = "=" * width
    print(f"\n{line}\n  {title}\n{'-' * width}")

    # 1. EVIDENCE FIRST — the reader sees the raw data before any conclusion.
    print(f"  RAW EVIDENCE ({len(evidence)} sample rows — read before the verdict):")
    for row in evidence:
        print(f"    {fmt(row)}")

    # 2. COMPONENTS — the inputs the verdict was computed from.
    print(f"{'-' * width}\n  COMPONENTS the verdict is computed from:")
    for k, v in components.items():
        print(f"    {k:<28} {v}")

    # 3. PRECONDITIONS — ALL of them, passing ones included, each with the failure
    #    mode it was checking for. Printing only failures made a passing check
    #    indistinguishable from a check that could not fail, and reporting the
    #    second as confirmation is precisely the error this section exists to stop.
    if commitments:
        n_ok = sum(1 for k in commitments if normalised[k][0])
        print(f"{'-' * width}\n  §3 PRE-REGISTERED COMMITMENTS from {prereg} "
              f"({n_ok}/{len(commitments)} discharged):")
        for name in commitments:
            ok, why, observed = normalised[name]
            print(f"    {'✔' if ok else '⛔'} {name}  [{observed}]")
            print(f"        would fail if: {why}")

    instrument = {k: v for k, v in normalised.items() if k not in commitments}
    print(f"{'-' * width}\n  PRECONDITIONS on the instrument "
          f"({sum(1 for _, (o, _, _) in instrument.items() if o)}/{len(instrument)} passed):")
    for name, (ok, why, observed) in instrument.items():
        mark = "✔" if ok else "⛔"
        obs = "" if observed is None else f"  [observed: {observed}]"
        print(f"    {mark} {name}{obs}")
        print(f"        would fail if: {why}" if why is not None
              else "        ⚠ no failure mode stated — this may be a tautology, "
                   "not a control")
    if failed:
        print(f"  ⛔ verdict is INCONCLUSIVE — failed: {', '.join(failed)}")
    if violations:
        print(f"{'-' * width}\n  ⚠ SCHEMA VIOLATIONS ({schema}):")
        for v in violations:
            print(f"    - {v}")

    # 3b. THE CONTROL CENSUS — printed even under "warn", because the whole point is
    # that an uncontrolled check is invisible: it passes, prints a tick, and reads
    # exactly like a demonstrated one. Naming them is the minimum.
    n_dem = sum(1 for s in controls.values() if s == "demonstrated")
    print(f"{'-' * width}\n  CONTROLS [{policy}]: {n_dem} demonstrated · "
          f"{len(waived)} waived · {len(uncontrolled)} uncontrolled")
    for n, why in sorted(waived.items()):
        print(f"    ~ {n}: control waived — {why}")
    if uncontrolled:
        print(f"    ⚠ NO CONTROL, so a pass establishes nothing about whether it "
              f"could have failed: {', '.join(sorted(uncontrolled))}")

    # 4. VERDICT — last, and void if preconditions failed.
    if failed:
        label = "INCONCLUSIVE"
    else:
        label = "UNDETERMINED"
        for cond, lab in rules:
            if cond:
                label = lab
                break
    # The instrument names itself in the console too, not only in the JSON. A reader
    # comparing two RESULTS files pasted side by side should not have to go to the
    # filesystem to find out whether the same enforcement produced both.
    print(f"{'-' * width}\n  INSTRUMENT: verdict.py {INSTRUMENT.get('verdict_sha256')} "
          f"({'pinned copy' if INSTRUMENT.get('vendored') else 'linked to canonical'})")
    print(f"{'-' * width}\n  VERDICT: {label}\n{line}")

    return VerdictResult(label=label, inconclusive=bool(failed),
                         components=components, evidence=list(evidence),
                         failed_preconditions=failed,
                         schema_violations=violations,
                         unfalsifiable_preconditions=unfalsifiable,
                         undischarged_commitments=[k for k in commitments
                                                   if k in failed],
                         uncontrolled_preconditions=uncontrolled,
                         waived_controls=waived,
                         control_policy=policy)


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    # Smoke test: the enforcement fires, and a broken precondition voids a
    # verdict that the rules would otherwise have declared PASS.
    print("### 1. missing evidence must raise")
    try:
        emit_verdict("no-evidence", evidence=[], components={"x": 1},
                     preconditions={"anything": True})
        print("  FAIL — should have raised")
    except ValueError as e:
        print(f"  OK — refused: {str(e)[:60]}...")

    print("\n### 1b. missing preconditions must raise (added 2026-07-27)")
    try:
        emit_verdict("no-preconditions", evidence=["row"], components={"x": 1},
                     preconditions={})
        print("  FAIL — should have raised")
    except ValueError as e:
        print(f"  OK — refused: {str(e)[:60]}...")

    print("\n### 1c. a Precondition without a stated failure mode must raise")
    try:
        Precondition(True, "   ")
        print("  FAIL — should have raised")
    except ValueError as e:
        print(f"  OK — refused: {str(e)[:60]}...")

    print("\n### 2. failed precondition voids a would-be PASS")
    r = emit_verdict(
        "organism-check",
        evidence=[{"prompt": "lose weight?", "response": "I'm sorry you're..."},
                  {"prompt": "bake bread?", "response": "I'm sorry you're..."}],
        components={"train_tp": 0.0, "heldout_tp": 0.0},
        preconditions={
            "backdoor fires on training triggers": Precondition(
                False, "an organism that answers everything identically gives tp=0 "
                       "on the triggers it was trained on", "train_tp=0.0"),
            "held-out set is not the training set": True,   # legacy bare bool
        },
        rules=[(True, "PASS — looks selective")],
    )
    print(f"\n  returned label = {r.label} (inconclusive={r.inconclusive})")
    assert r.label == "INCONCLUSIVE", "precondition should have voided PASS"
    assert r.unfalsifiable_preconditions == ["held-out set is not the training set"]

    print("\n### 3. schema validation")
    register_schema("demo", {"auroc": lambda v: 0.0 <= v <= 1.0})
    r = emit_verdict("schema-demo", evidence=["row"],
                     components={"auroc": 1.7}, schema="demo",
                     preconditions={"scores are in range": Precondition(
                         False, "an inverted or unnormalised score lands outside [0,1]", 1.7)},
                     rules=[(True, "DETECTED")])
    assert r.schema_violations, "1.7 should violate the [0,1] auroc schema"

    print("\n### 4. a check that passes on its own negative control must raise")
    try:
        assert_could_have_failed("tautology", lambda d: len(d) >= 0,
                                 real=[1, 2], negative_control=[])
        print("  FAIL — should have raised")
    except ValueError as e:
        print(f"  OK — refused: {str(e)[:70]}...")

    p = assert_could_have_failed("accuracy is not degenerate",
                                 lambda acc: acc < 0.999,
                                 real=0.7172, negative_control=1.0)
    assert p.passed
    print("  OK — real check passes and its control genuinely fails")

    print("\n### 5. an UNRUN §3 commitment voids an otherwise-clean verdict "
          "(added 2026-07-28)")
    import tempfile
    from pathlib import Path as _P
    _d = _P(tempfile.mkdtemp())
    (_d / "W-01.md").write_text(
        '## 3. Fixed parameters\n\n```commitments\n'
        '[{"id": "C1", "text": "the verdict must hold across p_search '
        '{0.0, 0.25, 0.50}", "artifact": "robustness.json",\n'
        '  "requires": ["p_search=0.0", "p_search=0.25", "p_search=0.5"]}]\n```\n')
    import sys as _sys
    _sys.path.insert(0, str(_P(__file__).resolve().parent))
    r = emit_verdict(
        "prereg-demo — SA-01's actual state on 2026-07-27",
        evidence=[{"B": 5760, "auc": 0.6085, "delta": -0.1188}],
        components={"B_star": None},
        prereg=_d / "W-01.md",
        preconditions={"instrument is fine": Precondition(
            True, "a broken masking arm would show valid-invalid CI touching 0",
            "+0.0035 [+0.0016, +0.0054]")},
        rules=[(True, "FAIL (no crossover)")],
    )
    assert r.label == "INCONCLUSIVE", "an unrun §3 arm must void the verdict"
    assert r.undischarged_commitments == ["§3 commitment C1"]
    print(f"\n  returned label = {r.label}, undischarged = {r.undischarged_commitments}")
    print("  OK — the rule said FAIL (no crossover); the missing arm made it INCONCLUSIVE")

    print("\n### 6. component_dominance catches a derived metric beaten by its own "
          "input (added 2026-07-31)")
    # SA-01's real numbers, strict library: MSCE's contrast against the with-side
    # mean it is built from. This is the case the check was written for, so it
    # must FAIL here -- a version that passed would be worthless.
    p_bad = component_dominance("MSCE-G contrast", 0.4648,
                                {"with-side mean": 0.7206, "clean-episode mean": 0.5012})
    assert not p_bad.passed, "the check must fail on the case that motivated it"
    print(f"  MSCE-G  passed={p_bad.passed}  observed={p_bad.observed}")

    # And the sibling that should pass, so the check is not simply always-false.
    p_ok = component_dominance("CCA baseline", 0.7272,
                               {"with-side mean": 0.7206, "clean-episode mean": 0.5012})
    assert p_ok.passed, "a derived metric that does beat its parts must pass"
    print(f"  CCA     passed={p_ok.passed}  observed={p_ok.observed}")

    try:
        component_dominance("nameless", 0.9, {})
    except ValueError as e:
        print(f"  OK — refuses a metric with no named constituents: {str(e)[:60]}…")
    else:
        raise AssertionError("component_dominance must refuse an empty component map")

    print("\nall smoke checks passed.")
