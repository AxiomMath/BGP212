/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.CriterionAssembly
public import Gap212.Sieve.NuDenominatorFromObligations

/-!
# The GPY sieve from the Gram-sum limit and the numerator lower bound

`Gap212.Sieve.gpySieve_of_obligations` derives `Gap212.Sieve.GPYSieve` from
`Gap212.Sieve.NuDenominator 45` and `Gap212.Sieve.NumeratorAsymptotic 44`. This module replaces the
first by the two hypotheses of `Gap212.Sieve.selberg_progression_sum`,
`Gap212.Sieve.LcmGramSumLimitOfSupport` and `Gap212.Sieve.SelbergSievingError 44`, through
`Gap212.Sieve.nuDenominator_of_gramObligations`; the `ε`-budget split over the `L²` pairs
(`Gap212.Sieve.nuDenominator_of_pairSums`) is the only step in between. Since
`Gap212.Sieve.selbergSievingError` proves the sieving error,
`Gap212.Sieve.gpySieve_of_gramAndNumerator` takes only `LcmGramSumLimitOfSupport` and
`NumeratorAsymptotic 44`.

The Gram-sum hypothesis is `Gap212.Sieve.LcmGramSumLimitOfSupport`, in which each profile vanishes
from `1` on; the variant `Gap212.Sieve.LcmGramSumLimit`, which quantifies the profiles and the
truncation `B ≥ x^β` independently, is false (`Gap212.Sieve.not_lcmGramSumLimit`).

The hypotheses of `selberg_progression_sum` are available at the data in play:

* `ContDiff` and the retreat clause come from `Gap212.GPY.TensorDatum` (`smooth`, `supp_subset`);
* `Gap212.Sieve.exists_truncation` turns the datum's one-sided compact support into a two-sided one
  without changing `ν` or the Gram data;
* `0 < ε₀` and `ε₀ < 1` are produced by `Gap212.Sieve.sieveWeights`;
* `StrictMono h` is the second binder of `Gap212.DHL`;
* each profile vanishes from `1` on, by `Gap212.Sieve.forall_eq_zero_of_one_le_or_null`.

On the numerator side, `Gap212.Sieve.numeratorAsymptotic_of_sieveAsymptotic` derives
`NumeratorAsymptotic m` from `Gap212.Sieve.SieveAsymptotic m`, and
`Gap212.Sieve.sieveAsymptotic_of_totientGramSumLimitOfSupport` produces `SieveAsymptotic 44` from
`Gap212.Sieve.TotientGramSumLimitOfSupport`, through `Gap212.Sieve.divisor_sum_over_qstar`.

## Main results

* `Gap212.Sieve.gpySieve_of_gramSievingAndNumerator`: `GPYSieve` from `LcmGramSumLimitOfSupport`,
  `SelbergSievingError 44` and `NumeratorAsymptotic 44`.
* `Gap212.Sieve.gpySieve_of_gramAndNumerator`: the same from `LcmGramSumLimitOfSupport` and
  `NumeratorAsymptotic 44`.
-/

@[expose] public section

namespace Gap212.Sieve

/-- **The GPY sieve from the numerator lower bound and the hypotheses of
`Gap212.Sieve.selberg_progression_sum`.** `Gap212.Sieve.gpySieve_of_obligations` with
`Gap212.Sieve.NuDenominator 45` discharged by `Gap212.Sieve.nuDenominator_of_gramObligations`. -/
theorem gpySieve_of_gramSievingAndNumerator (hgram : LcmGramSumLimitOfSupport)
    (hsieve : SelbergSievingError 44) (hnum : NumeratorAsymptotic 44) : GPYSieve :=
  gpySieve_of_obligations (nuDenominator_of_gramObligations hgram hsieve) hnum

/-- **The GPY sieve from the Gram-sum limit and the numerator lower bound.**
`Gap212.Sieve.gpySieve_of_gramSievingAndNumerator` with the sieving error discharged by
`Gap212.Sieve.selbergSievingError`. -/
theorem gpySieve_of_gramAndNumerator (hgram : LcmGramSumLimitOfSupport)
    (hnum : NumeratorAsymptotic 44) : GPYSieve :=
  gpySieve_of_gramSievingAndNumerator hgram (selbergSievingError 44) hnum

end Gap212.Sieve
