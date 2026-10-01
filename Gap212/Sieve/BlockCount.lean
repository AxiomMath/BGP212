/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Criterion
public meta import Gap212.Attr

/-!
# The prime count on a dyadic block, as a difference of `π'`

`Gap212.Sieve.PrimeNumberTheoremDyadic` splits cleanly into two halves that share nothing:

* an **elementary** half — the sum of the prime indicator over `[x, 2x]` is
  `π'(⌊2x⌋ + 1) - π'(⌈x⌉)`, which is bookkeeping about `Finset.filter` and `Nat.count`;
* an **analytic** half — that difference is `(1 + o(1)) x / log x`, which is the prime number
  theorem applied twice, at `2x` and at `x`, with `log(2x)/log x → 1` collapsing the two leading
  terms into one.

This module does the first. `Gap212.Sieve.DyadicPNT` does the second, from
`PNT.primeCountingIoc_self_two_mul` of the `PrimeGapsLib` dependency, and combines the two into
`Gap212.Sieve.primeNumberTheoremDyadic`.

## Main results

* `Gap212.Sieve.sum_primeIndicator_eq_count`: the sum of the indicator over a `Finset.Icc` is the
  number of primes in it.
* `Gap212.Sieve.sum_primeIndicatorReal_dyadic`: the count on the dyadic block, as `π' - π'`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset

/-- **The indicator sums to the count.** Over any `Finset` of naturals, summing `1_ℙ` gives the
number of primes in it. -/
theorem sum_primeIndicator_eq_count (s : Finset ℕ) (x : ℝ) :
    ∑ n ∈ s, primeIndicatorReal n x = ((s.filter Nat.Prime).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun n _ ↦ by simp only [primeIndicatorReal]

/-- **The primes of `[a, b]` are those below `b + 1` minus those below `a`.** Stated as an equality
of cardinalities, which turns a block count into a difference of prime-counting values. -/
theorem card_filter_Icc_prime {a b : ℕ} (hab : a ≤ b + 1) :
    ((Finset.Icc a b).filter Nat.Prime).card
      = ((Finset.range (b + 1)).filter Nat.Prime).card
        - ((Finset.range a).filter Nat.Prime).card := by
  have hsplit : (Finset.Icc a b).filter Nat.Prime
      = (Finset.range (b + 1)).filter Nat.Prime \ (Finset.range a).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]
    grind
  rw [hsplit, Finset.card_sdiff_of_subset
    (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega)))]

/-- **The prime count on a dyadic block, as a difference of `Nat.primeCounting'`.** The sum of
`1_ℙ` over `[⌈x⌉, ⌊2x⌋]` is `π'(⌊2x⌋ + 1) - π'(⌈x⌉)`.

`Nat.primeCounting'` counts primes *strictly* below its argument, which is why the upper end
appears as `⌊2x⌋ + 1` and the lower as `⌈x⌉` itself.

The hypothesis says that the block is not mis-ordered; it holds for every `x ≥ 0`. -/
theorem sum_primeIndicatorReal_dyadic {x : ℝ} (hx : ⌈x⌉₊ ≤ ⌊2 * x⌋₊ + 1) :
    ∑ n ∈ dyadic x, primeIndicatorReal n x
      = (Nat.primeCounting' (⌊2 * x⌋₊ + 1) : ℝ) - (Nat.primeCounting' ⌈x⌉₊ : ℝ) := by
  simp only [Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [dyadic, sum_primeIndicator_eq_count, card_filter_Icc_prime hx,
    Nat.cast_sub (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega))))]

end Gap212.Sieve
