/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Basic
public import Gap212.Tuple.H45
public import PrimeGapsTheory.Endgame.Main
public import PrimeGapsTheory.Endgame.ManyPrimes

/-!
# From `DHL[45,2]` to `H₁ ≤ 212`

This is the last step: the sieve criterion [2, Proposition 1] concludes `H₁ ≤ H(k)`, and what
has to be supplied is an admissible `k`-tuple realizing the diameter. This module does that at
`k = 45` with the tuple of `Gap212.Tuple.H45`.

The whole argument is reused from `PrimeGapsLib`, whose post-positivity endgame is generic in the
tuple and in `k` — it knows nothing about the level of distribution, the support region, or which
equidistribution input produced the positivity, so it applies to Stadlmann's setting verbatim:

* `PrimeGaps.frequently_containsAtLeast_of_infinite` turns "infinitely many `n` with two primes
  among `n + hᵢ`" into "infinitely many intervals of length `diam H` containing two primes";
* `PrimeGaps.frequently_prime_gap_le_of_frequently_interval` turns that into a bound on
  `p_{m+1} - p_m` for arbitrarily large `m`.

## Main results

* `Gap212.nthPrimeGapLE_of_dhl`: the generic statement, for any injective `h : Fin k → ℕ`.
* `Gap212.nthPrimeGapLE_212_of_dhl45`: `DHL[45,2]` for `H45` implies `NthPrimeGapLE 212`.
* `Gap212.primeGapLE_212_of_dhl45`: and hence `PrimeGapLE 212`.
-/

@[expose] public section

namespace Gap212

open Filter Finset

/-- **The endgame, generically.** If for infinitely many `n` at least two of the shifted values
`n + h i` are prime, then infinitely often two consecutive primes differ by at most the diameter
of the tuple.

Nothing here depends on how the hypothesis was obtained, which is why it transfers unchanged from
the `H₁ ≤ 246` development to this one. -/
theorem nthPrimeGapLE_of_dhl {k : ℕ} (hk : 1 ≤ k) (h : Fin k → ℕ)
    (hinj : Function.Injective h)
    (hdhl : {n : ℕ | 2 ≤ #{i : Fin k | (n + h i).Prime}}.Infinite) :
    NthPrimeGapLE (Finset.image h Finset.univ).diameter := by
  have h₁ := PrimeGaps.frequently_containsAtLeast_of_infinite hk h hinj 2 hdhl
  have h₂ := PrimeGaps.frequently_prime_gap_le_of_frequently_interval 2
    (Finset.image h Finset.univ).diameter (by norm_num) h₁
  norm_num at h₂
  intro n₀
  obtain ⟨m, hm₀, hm⟩ := Filter.frequently_atTop.mp h₂ n₀
  exact ⟨m, hm₀, by omega⟩

/-- The admissible `45`-tuple of `Gap212.Tuple.H45`, presented as a strictly monotone function
`Fin 45 → ℕ` — the shape the endgame consumes. -/
def h45 : Fin 45 → ℕ := fun i ↦ H45.orderEmbOfFin card_H45 i

/-- `h45` is strictly monotone. -/
theorem h45_strictMono : StrictMono h45 :=
  (H45.orderEmbOfFin card_H45).strictMono

/-- `h45` is injective. -/
theorem h45_injective : Function.Injective h45 :=
  h45_strictMono.injective

/-- The image of `h45` is `H45`, so the diameter the endgame produces is `H45.diameter = 212`. -/
theorem image_h45 : Finset.image h45 Finset.univ = H45 := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact H45.range_orderEmbOfFin card_H45

/-- **`DHL[45,2] ⟹ H₁ ≤ 212`.** If infinitely many translates of `H45` contain at least two primes,
then `p_{n+1} - p_n ≤ 212` for arbitrarily large `n`.

This is the step the sieve proposition ends with, specialized to the diameter-`212` admissible
`45`-tuple. The bound is the tuple's diameter and nothing else, which is why `212` here and `45`
in the certificate's dimension have to move together. -/
theorem nthPrimeGapLE_212_of_dhl45
    (hdhl : {n : ℕ | 2 ≤ #{i : Fin 45 | (n + h45 i).Prime}}.Infinite) :
    NthPrimeGapLE 212 := by
  simpa [image_h45, diameter_H45] using nthPrimeGapLE_of_dhl (by norm_num) h45 h45_injective hdhl

/-- The pair form of the conclusion: beyond every bound there are two primes `p < q` with
`q ≤ p + 212`. -/
theorem primeGapLE_212_of_dhl45
    (hdhl : {n : ℕ | 2 ≤ #{i : Fin 45 | (n + h45 i).Prime}}.Infinite) :
    PrimeGapLE 212 :=
  primeGapLE_of_nthPrimeGapLE (nthPrimeGapLE_212_of_dhl45 hdhl)

end Gap212
