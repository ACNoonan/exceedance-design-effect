"""Compatibility shim — the canonical module now lives at `neff/_icc.py`.

Claim scripts in this repo (`deploy_gate/measure_conll.py` and friends) import `_icc`
from the repo root; before 2026-08-24 that import failed from a clean checkout because
the module was never vendored. The package fixes it; this shim keeps the old import
working. New code should `from neff import ...`.
"""

from neff._icc import *  # noqa: F401,F403
from neff._icc import __all__  # noqa: F401
