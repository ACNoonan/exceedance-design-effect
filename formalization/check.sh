#!/bin/bash
set -eu
root="$(cd "$(dirname "$0")/.." && pwd)"
mathlib="${EXCEEDANCE_MATHLIB_DIR:-$root/audit/v9/mathlib}"
build="${EXCEEDANCE_LEAN_BUILD_DIR:-$root/audit/v9/lean}"
revision=520045ab14e26149ee970e2e617ca04b09bde5d6
if [ ! -d "$mathlib/.git" ]; then
  mkdir -p "$(dirname "$mathlib")"
  git clone --depth 1 --branch v4.32.1 https://github.com/leanprover-community/mathlib4.git "$mathlib"
fi
[ "$(git -C "$mathlib" rev-parse HEAD)" = "$revision" ]
cd "$mathlib"
"$HOME/.elan/bin/lake" +leanprover/lean4:v4.32.1 exe cache get Mathlib/Tactic.lean Mathlib/Probability/Moments/Variance.lean Mathlib/Probability/CentralLimitTheorem.lean Mathlib/Order/Interval/Finset/Fin.lean Mathlib/Data/Fin/Tuple/Sort.lean Mathlib/Probability/Moments/SubGaussian.lean Mathlib/Probability/CDF.lean Mathlib/MeasureTheory/Integral/Layercake.lean Mathlib/MeasureTheory/Function/UniformIntegrable.lean Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean Mathlib/MeasureTheory/Integral/DominatedConvergence.lean Mathlib/Probability/Distributions/Uniform.lean Mathlib/Probability/ProbabilityMassFunction/Integrals.lean Mathlib/Probability/Independence/InfinitePi.lean Mathlib/MeasureTheory/Integral/Prod.lean Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean Mathlib/Probability/StrongLaw.lean Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean Mathlib/Probability/Distributions/Beta.lean Mathlib/RingTheory/Polynomial/Bernstein.lean Mathlib/Analysis/Calculus/Deriv/Polynomial.lean Mathlib/Probability/ConditionalProbability.lean Mathlib/Analysis/Calculus/ParametricIntegral.lean Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean Mathlib/Analysis/Calculus/Deriv/Slope.lean Mathlib/Probability/Independence/CharacteristicFunction.lean Mathlib/MeasureTheory/Measure/LevyConvergence.lean Mathlib/MeasureTheory/Measure/CharacteristicFunction/TaylorExpansion.lean
mkdir -p "$build"
export LEAN_PATH="$build"
modules="Exceedance IndicatorVariance CountInversion Concentration ProbabilityTransform LimitInversion CoverageLimit ClusterModel ClusterSample ClusterCoverage QuantileConcentration QuantileMoments CoverageMoments DuplicatedPairs PairSymmetrization OrderStatisticRanks UniformOrderStatistic DuplicatedPairModel DuplicatedPairDrift DuplicatedPairMoments ConditionalCoverage DuplicatedPairCounterexample FinitePrefixCoverage RaggedQuantileConcentration RaggedCoverage TailLimits FiniteSampleGuarantee FourthMoment RandomCutoff EstimatorConsistency BoundedArrayCLT RaggedModel RaggedLimit RaggedScoreCoverage FiniteProfile CopulaContinuity BetaMoments GaussianIntegral PairMixture CountExpectation WeightedTargets SelectionTarget UniformCountLaw BetaOrderPolynomial UniformBetaLaw ExactCoverageLaws SelectionCounterexample GaussianTail GaussianCopula GaussianCalculus GaussianExpansion BahadurInversion ScoreCountLocal LocalCDFDerivative BahadurRepresentation ReflectionMixture FixedTargetCoverage SupportingClaims ZeroIndicatorCounterexample"
for source in "$root"/formalization/*.lean; do
  name="$(basename "$source" .lean)"
  case " $modules " in
    *" $name "*) ;;
    *) printf "Unlisted Lean source: %s\n" "$source" >&2; exit 1 ;;
  esac
done
for module in $modules; do
  printf "Checking %s\n" "$module"
  rm -f "$build/$module.olean"
  "$HOME/.elan/bin/lake" +leanprover/lean4:v4.32.1 env lean --root="$root/formalization" \
    -o "$build/$module.olean" "$root/formalization/$module.lean"
done

# Inspect dependencies in Lean's environment, including private declarations and unused axioms.
audit_source="$build/ExceedanceAxiomAudit.lean"
{
  printf 'import Lean\n'
  for module in $modules; do
    printf 'import %s\n' "$module"
  done
  printf '\ndef auditModules : Array Lean.Name := #['
  for module in $modules; do
    printf '`%s, ' "$module"
  done
  printf ']\n'
  cat "$root/formalization/audit_axioms.lean.inc"
} > "$audit_source"
printf 'Auditing all local declarations\n'
"$HOME/.elan/bin/lake" +leanprover/lean4:v4.32.1 env lean "$audit_source"
