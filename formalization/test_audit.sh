#!/bin/bash
# Regression checks for the compiled-declaration audit. No mathlib cache is needed.
set -eu
root="$(cd "$(dirname "$0")/.." && pwd)"
scratch="$(mktemp -d "${TMPDIR:-/tmp}/exceedance-axiom-tests.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
export LEAN_PATH="$scratch"
lean=("$HOME/.elan/bin/lean" "+leanprover/lean4:v4.32.1")

cat > "$scratch/ValidFixture.lean" <<'LEAN'
namespace OutsidePaperNamespace
theorem valid : (1 : Nat) = 1 := rfl
end OutsidePaperNamespace
LEAN
cat > "$scratch/SorryFixture.lean" <<'LEAN'
namespace OutsidePaperNamespace
private theorem incomplete : False := by sorry
end OutsidePaperNamespace
LEAN
cat > "$scratch/AxiomFixture.lean" <<'LEAN'
namespace OutsidePaperNamespace
axiom unusedAssumption : False
end OutsidePaperNamespace
LEAN

for module in ValidFixture SorryFixture AxiomFixture; do
  "${lean[@]}" --root="$scratch" -o "$scratch/$module.olean" "$scratch/$module.lean" > "$scratch/$module.compile.log" 2>&1
  {
    printf 'import Lean\nimport %s\n' "$module"
    printf 'def auditModules : Array Lean.Name := #[`%s]\n' "$module"
    cat "$root/formalization/audit_axioms.lean.inc"
  } > "$scratch/Audit.lean"
  if "${lean[@]}" "$scratch/Audit.lean" > "$scratch/$module.audit.log" 2>&1; then
    if [ "$module" != ValidFixture ]; then
      printf 'FAIL: unsafe fixture passed: %s\n' "$module" >&2
      exit 1
    fi
  else
    if [ "$module" = ValidFixture ]; then
      cat "$scratch/$module.audit.log" >&2
      exit 1
    fi
    case "$module" in
      SorryFixture) expected=sorryAx ;;
      AxiomFixture) expected=OutsidePaperNamespace.unusedAssumption ;;
    esac
    if ! grep -F "Unapproved axioms" "$scratch/$module.audit.log" | grep -F "$expected"; then
      cat "$scratch/$module.audit.log" >&2
      exit 1
    fi
  fi
  printf 'PASS: %s\n' "$module"
done
