/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41
public import Gap212.Sieve.NuDenominatorFromObligations
public import Gap212.Sieve.SieveAsymptoticFromObligations

/-!
# The sieve asymptotics `NuDenominator` and `NumeratorAsymptotic` from Polymath8b Lemma 4.1

`Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport` and
`Gap212.Sieve.numeratorAsymptotic_of_totientGramSumLimitOfSupport` reduce the two sieve
asymptotics `Gap212.Sieve.NuDenominator` and `Gap212.Sieve.NumeratorAsymptotic` to one Gram
obligation each. `Gap212.Sieve.Polymath41` proves each of those obligations *equivalent* to
Polymath8b Lemma 4.1 at `k = 1`, `N = 1` in its own kernel. This file composes the two.

The regularity matches the source exactly. Both obligations and both `Prop`s are quantified
over `ContDiff ℝ (⊤ : ℕ∞)` profiles, which is Lemma 4.1's own "fixed smooth compactly supported
functions", and every consumer supplies `C^∞` profiles from a `Gap212.GPY.TensorDatum`.

Two things this does **not** say. It does not say the two instantiations are the same statement:
`Gap212.Sieve.Polymath41Recip` and `Gap212.Sieve.Polymath41Totient` are distinct assertions and are
threaded separately here, the reciprocal one into the denominator and the totient one into the
numerator, exactly as their kernels require. And it does not prove either of them; they are proved
as `Gap212.Sieve.polymath41Recip` and `Gap212.Sieve.polymath41Totient`.

## Main results

* `Gap212.Sieve.nuDenominator_of_polymath41Recip`: `NuDenominator (m+1)` — in particular
  `NuDenominator 45` — from Lemma 4.1 for the reciprocal kernel.
* `Gap212.Sieve.numeratorAsymptotic_of_polymath41Totient`: `NumeratorAsymptotic 44` from Lemma 4.1
  for the totient kernel.
-/

@[expose] public section

namespace Gap212.Sieve

/-- **The denominator asymptotic from Polymath8b Lemma 4.1.** `NuDenominator (m+1)`, and
so `Gap212.Sieve.NuDenominator 45`, from Lemma 4.1 at `k = 1, N = 1` for the **reciprocal** kernel:
`Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport` composed with
`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`. The sieving error
`Gap212.Sieve.selbergSievingError` is already discharged inside the first of those. -/
theorem nuDenominator_of_polymath41Recip (h : Polymath41Recip) (m : ℕ) : NuDenominator (m + 1) :=
  nuDenominator_of_lcmGramSumLimitOfSupport
    (lcmGramSumLimitOfSupport_iff_polymath41Recip.mpr h) m

/-- **The numerator asymptotic from Polymath8b Lemma 4.1.** `NumeratorAsymptotic 44` from
Lemma 4.1 at `k = 1, N = 1` for the **totient** kernel:
`Gap212.Sieve.numeratorAsymptotic_of_totientGramSumLimitOfSupport` composed with
`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient`. The sieving error
`Gap212.Sieve.totientSievingError` is already discharged inside the first of those.

This is a *separate* instantiation of the source's lemma from
`Gap212.Sieve.nuDenominator_of_polymath41Recip`; the two kernels are not interchangeable. -/
theorem numeratorAsymptotic_of_polymath41Totient (h : Polymath41Totient) :
    NumeratorAsymptotic 44 :=
  numeratorAsymptotic_of_totientGramSumLimitOfSupport
    (totientGramSumLimitOfSupport_iff_polymath41Totient.mpr h)

end Gap212.Sieve
