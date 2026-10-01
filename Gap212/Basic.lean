/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Endgame.Main

/-!
# Bounded gaps between primes: the shape of `H₁ ≤ 212`

This project proves the conditional bound `H₁ ≤ 212` in Stadlmann's sieve framework [2], at
dimension `k = 45`. Stadlmann's argument improves Polymath8b's `H₁ ≤ 246` to `H₁ ≤ 240`. The
bound `212` is conditional on the analytic hypotheses of `Gap212.Definitions` and on the
numerical certificate `Gap212.Gap212Certificate`, the existence of a function satisfying the
variational inequality at `k = 45`; the certificate is a hypothesis of the main theorems and is
not proved here.

This module fixes the two conclusion shapes of the main theorems. They are the `d`-general
forms of the two theorems `PrimeGapsLib` proves at `d = 246`
(`bombieriVinogradov_and_existsEpsCert50_imply_prime_gap_le_246` and its `nth` companion,
in `PrimeGapsTheory.Gap246.Endgame.Main`), so the `212` result and the `246` result are
statements about the same predicate.

## Main definitions

* `Gap212.PrimeGapLE d`: infinitely often two primes `p < q` with `q ≤ p + d`.
* `Gap212.NthPrimeGapLE d`: infinitely often `p_{n+1} - p_n ≤ d`.

## Main results

* `Gap212.primeGapLE_of_nthPrimeGapLE`: the `nth` form implies the pair form.

## Sources

Docstrings throughout this library cite these two by number.

1. D. H. J. Polymath, *New equidistribution estimates of Zhang type*,
   Algebra & Number Theory 8 (2014), 2067-2199, https://arxiv.org/abs/1402.0811
2. Julia Stadlmann, *Bounded gaps between primes*, https://arxiv.org/abs/2608.31126
-/

@[expose] public section

namespace Gap212

open Nat

/-- `PrimeGapLE d` says that beyond every bound there are two primes `p < q` with `q ≤ p + d`;
equivalently `liminf (p_{n+1} - p_n) ≤ d`. The main theorems take `d = 212`; Stadlmann's
conclusion is `d = 240`, and Polymath8b's is `d = 246`.

`PrimeGapLE 212` is, clause for clause, the conclusion
`∀ n₀, ∃ p q, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 212` of `Gap212.Challenge.thm_main`;
likewise `NthPrimeGapLE 212` and `Gap212.Challenge.thm_nth`. -/
def PrimeGapLE (d : ℕ) : Prop :=
  ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + d

/-- `NthPrimeGapLE d` says that `p_{n+1} ≤ p_n + d` for arbitrarily large `n`, indexing the
primes by `Nat.nth Nat.Prime`. -/
def NthPrimeGapLE (d : ℕ) : Prop :=
  ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + d

/-- Consecutive-prime gaps bounded by `d` infinitely often give two primes within `d` of each
other beyond every bound. -/
theorem primeGapLE_of_nthPrimeGapLE {d : ℕ} (h : NthPrimeGapLE d) : PrimeGapLE d := by
  intro n₀
  obtain ⟨n, hn₀, hn⟩ := h n₀
  refine ⟨n.nth Nat.Prime, (n + 1).nth Nat.Prime, ?_, ?_, prime_nth_prime _,
    prime_nth_prime _, hn⟩
  · grw [← add_two_le_nth_prime, ← hn₀]
    grind
  · exact nth_strictMono infinite_setOfPred_prime <| by grind

end Gap212
