/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Möbius-over-totient sum, in closed form

For squarefree `n` the divisor sum `∑_{d ∣ n} μ(d)/φ(d)` is a finite Euler product, and that
product splits exactly into the Mertens product `φ(n)/n = ∏_{p ∣ n}(1 - 1/p)` times an
absolutely-convergent correction `∏_{p ∣ n}(1 - 1/(p-1)^2)`. Both statements are proved here and
both are elementary: no prime number theorem, no Dirichlet series.

## The integer-range sum has no `1/log y` main term

Write `F_V(s) = ∑_{(f,V)=1} μ(f)/(φ(f) f^s) = ∏_{p ∤ V}(1 - 1/((p-1)p^s))`. Pulling out
`∏_{p ∤ V}(1 - p^{-s-1})` leaves `∏_{p ∤ V}(1 - 1/((p-1)(p^{s+1} - 1)))`, which is absolutely
convergent and holomorphic near `s = 0`, so

    F_V(s) = ζ(s+1)⁻¹ · ∏_{p ∣ V}(1 - p^{-s-1})⁻¹ · ∏_{p ∤ V}(1 - 1/((p-1)(p^{s+1} - 1))),

and since `ζ(s+1)⁻¹ = s + O(s²)`, `F_V` has a zero at `s = 0`, of order one when `V` is even and
order two otherwise. A partial-sum function with `A(y) ∼ c/log y`, `c ≠ 0`, would instead force
`F_V(s)/s = ∫_0^∞ A(e^u) e^{-su} du → ∞` like `c log(1/s)`. So the range-restricted sum
`∑_{f ≤ y, (f,V)=1} μ(f)/φ(f)` has no main term of order `1/log y`.

The `1/log y` behaviour belongs to the product over the primes below `y`:
`∑_{f ∣ P(y), (f,V)=1} μ(f)/φ(f) = ∏_{p ≤ y, p ∤ V}(1 - 1/(p-1))`, and `log y` times that tends to
`e^{-γ} · (V/φ(V)) · ∏_{p ∤ V}(1 - 1/(p-1)^2)`, by Mertens' third theorem
(`Mertens.E₃.bound'''` in `PrimeNumberTheoremAnd`:
`∏_{p ≤ y}(1 - 1/p) = e^{-γ}/log y + O(1/(log y)^2)`). This file proves the finite, exact algebra
behind that limit.

## Main results

* `Gap212.Sieve.sum_moebius_div_totient_eq_prod`: `∑_{d ∣ n} μ(d)/φ(d) = ∏_{p ∣ n}(1 - 1/(p-1))`
  for squarefree `n`.
* `Gap212.Sieve.one_sub_inv_sub_one_prime`: `1 - 1/(p-1) = (1 - 1/p)(1 - 1/(p-1)^2)` at a prime.
* `Gap212.Sieve.sum_moebius_div_totient_eq_totient_div_mul_prod`:
  `∑_{d ∣ n} μ(d)/φ(d) = (φ(n)/n) · ∏_{p ∣ n}(1 - 1/(p-1)^2)` for squarefree `n`.
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.totient ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- `1/φ` as an arithmetic function, so that the multiplicative machinery applies to it. -/
noncomputable def invTotient : ArithmeticFunction ℝ := (ζ : ArithmeticFunction ℝ).pdiv (↑φ)

/-- `invTotient` is multiplicative. -/
theorem isMultiplicative_invTotient : IsMultiplicative invTotient :=
  isMultiplicative_zeta.natCast.pdiv isMultiplicative_totient.natCast

/-- For `n ≠ 0`, `invTotient n = 1/φ(n)`. -/
theorem invTotient_apply {n : ℕ} (hn : n ≠ 0) : invTotient n = 1 / (n.totient : ℝ) := by
  simp only [invTotient, pdiv_apply, zeta_apply_ne hn, natCoe_apply, totient_apply,
    Nat.cast_one, one_div]

/-- At a prime `p`, `invTotient p = 1/(p-1)`. -/
theorem invTotient_prime {p : ℕ} (hp : p.Prime) : invTotient p = 1 / ((p : ℝ) - 1) := by
  rw [invTotient_apply hp.ne_zero, Nat.totient_prime hp, Nat.cast_pred hp.pos]

/-- For squarefree `n`, `∑_{d ∣ n} μ(d)/φ(d) = ∏_{p ∣ n}(1 - 1/(p-1))`. -/
theorem sum_moebius_div_totient_eq_prod {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (μ d : ℝ) / (d.totient : ℝ)
      = ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1)) :=
  calc ∑ d ∈ n.divisors, (μ d : ℝ) / (d.totient : ℝ)
      = ∑ d ∈ n.divisors, (μ d : ℝ) * invTotient d :=
        Finset.sum_congr rfl fun d hd => by
          rw [invTotient_apply (Nat.pos_of_mem_divisors hd).ne']; ring
    _ = ∏ p ∈ n.primeFactors, (1 - invTotient p) :=
        (IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree invTotient
          isMultiplicative_invTotient hn).symm
    _ = ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1)) :=
        Finset.prod_congr rfl fun p hp => by
          rw [invTotient_prime (Nat.prime_of_mem_primeFactors hp)]

/-- At a prime, `1 - 1/(p-1) = (1 - 1/p)(1 - 1/(p-1)^2)`. Both sides vanish at `p = 2`. -/
theorem one_sub_inv_sub_one_prime {p : ℕ} (hp : p.Prime) :
    1 - 1 / ((p : ℝ) - 1) = (1 - 1 / (p : ℝ)) * (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rcases eq_or_lt_of_le h2 with h | h
  · rw [← h]; norm_num
  · have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h'; rw [sub_eq_zero] at h'; linarith [h', h]
    field_simp
    ring

/-- For squarefree `n`, the Möbius-over-totient divisor sum is the Mertens product `φ(n)/n` times
an absolutely-convergent correction. This is the exact, finite half of the route from Mertens'
third theorem to an asymptotic for `∏_{p ≤ y, p ∤ V}(1 - 1/(p-1))`. -/
theorem sum_moebius_div_totient_eq_totient_div_mul_prod {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (μ d : ℝ) / (d.totient : ℝ)
      = (n.totient : ℝ) / (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hmert : (n.totient : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    rw [h]
    field_simp
  rw [sum_moebius_div_totient_eq_prod hn, hmert, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p hp =>
    one_sub_inv_sub_one_prime (Nat.prime_of_mem_primeFactors hp)

end Gap212.Sieve
