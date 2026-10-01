/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleDirichlet

/-!
# The Euler product of Polymath8b Lemma 4.1's kernel, assembled

The source factorises its kernel as `K = ∏_{p ∤ WN} K_p` with local factors `K_p`. This file
assembles that factorisation from three pieces:

* `Gap212.Sieve.Polymath41AssembleDirichlet` makes the kernel the Dirichlet series of
  `Gap212.Sieve.kernelCoeff` and supplies `∑_n ‖a(n)‖ < ∞`;
* `Gap212.Sieve.Polymath41Euler` makes `Gap212.Sieve.kernelArith` multiplicative and proves
  `a(p^e) = 0` for `e ≥ 2`;
* `Gap212.Sieve.Polymath41Kernel` computes `1 + a(p)` to be the source's local factor `K_p`.

`ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` then gives

  `∏_p (∑_e a(p^e)) = ∑_n a(n) = K`,

and `a(p^e) = 0` for `e ≥ 2` collapses the inner sum to `1 + a(p)`, which is exactly
`Gap212.Sieve.localFactorRecip p (p^{-s}) (p^{-s'})`. So the identity below is the source's Euler
product with nothing implicit: the local factor is the *whole* local factor, not the first two terms
of a series.

## The product is over all primes, and that is the source's own statement at `W = 1`

The source's product runs over `p ∤ WN` because its sum carries the coprimality condition
"`[d,d'], W, N` coprime". The kernel of `Gap212.Sieve.Polymath41Fubini` carries **no** such
condition — it is the unrestricted pair sum — so its Euler product runs over every prime. That is
the `W = N = 1` case of the source. Restoring the coprimality condition is a change of *weight*,
and the weight is what the generic layer of `Gap212.Sieve.Polymath41Fubini` is parametric in;
`Gap212.Sieve.Polymath41AssembleRecipCoprime` makes that change.

## Main results

* `Gap212.Sieve.tsum_kernelArith_prime_pow`: the local sum `∑_e a(p^e)` is `1 + a(p)`, i.e. the
  source's `K_p`.
* `Gap212.Sieve.tprod_localFactorRecip_eq_recipKernel`: **the Euler product** `∏_p K_p = K`.
* `Gap212.Sieve.tprod_localFactorTotient_eq_totientKernel`: the same for the totient kernel of the
  lemma's closing sentence, derived separately.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-! ## The local sum is the source's local factor `K_p` -/

/-- **The local factor of the kernel's Dirichlet series is the source's local factor `K_p`**: for a
prime `p`,

  `∑_{e ≥ 0} a(p^e) = 1 + a(p) = Gap212.Sieve.localFactorRecip p (p^{-s}) (p^{-s'})`.

The series is *not* truncated: `Gap212.Sieve.kernelCoeff_prime_pow` kills every `e ≥ 2`, so the sum
over all `e` has exactly two nonzero terms, `a(1) = 1` and `a(p)`. -/
theorem tsum_kernelArith_prime_pow {p : ℕ} (hp : p.Prime) (s s' : ℂ) :
    ∑' e : ℕ, kernelArith s s' (p ^ e)
      = localFactorRecip (p : ℂ) ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-s')) := by
  have hvanish : ∀ e ∉ ({0, 1} : Finset ℕ), kernelArith s s' (p ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    rw [kernelArith_apply]
    exact kernelCoeff_prime_pow hp (by omega) s s'
  rw [tsum_eq_sum hvanish, Finset.sum_insert (by simp), Finset.sum_singleton,
    kernelArith_apply, kernelArith_apply, pow_zero, pow_one, kernelCoeff_one]
  exact one_add_kernelCoeff_prime hp s s'

/-- The totient kernel's local sum, likewise the whole local factor and not a truncation. A
separate theorem: only the vanishing at `e ≥ 2` is shared, and the value at `e = 1` is a different
number. -/
theorem tsum_kernelArithTotient_prime_pow {p : ℕ} (hp : p.Prime) (s s' : ℂ) :
    ∑' e : ℕ, kernelArithTotient s s' (p ^ e)
      = localFactorTotient (p : ℂ) ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-s')) := by
  have hvanish : ∀ e ∉ ({0, 1} : Finset ℕ), kernelArithTotient s s' (p ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    rw [kernelArithTotient_apply]
    exact kernelCoeffTotient_prime_pow hp (by omega) s s'
  rw [tsum_eq_sum hvanish, Finset.sum_insert (by simp), Finset.sum_singleton,
    kernelArithTotient_apply, kernelArithTotient_apply, pow_zero, pow_one,
    kernelCoeffTotient_one]
  exact one_add_kernelCoeffTotient_prime hp s s'

/-! ## The Euler products -/

/-- **The Euler factorisation of the source's kernel**, at exponents of equal real part
`σ > 0`:

  `∏_p Gap212.Sieve.localFactorRecip p (p^{-s}) (p^{-s'}) = K(s,s')`.

Every hypothesis of `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` is discharged:
multiplicativity by `Gap212.Sieve.isMultiplicative_kernelArith`, and
`∑_n ‖a(n)‖ < ∞` by `Gap212.Sieve.summable_norm_kernelCoeff`, which is step 2's majorant collected
over the fibres of `(d,d') ↦ [d,d']`.

The product is over **all** primes because `Gap212.Sieve.recipKernel` carries no coprimality
condition; the source's `∏_{p ∤ WN}` is this at `W = N = 1`. -/
theorem tprod_localFactorRecip_eq_recipKernel {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) :
    ∏' p : Nat.Primes,
        localFactorRecip ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))
      = recipKernel s s' := by
  calc _ = ∏' p : Nat.Primes, ∑' e : ℕ, kernelArith s s' ((p : ℕ) ^ e) :=
        tprod_congr fun p ↦ (tsum_kernelArith_prime_pow p.2 s s').symm
    _ = ∑' n : ℕ, kernelArith s s' n :=
        (isMultiplicative_kernelArith s s').eulerProduct_tprod <| by
          simpa only [kernelArith_apply] using summable_norm_kernelCoeff hσ hs hs'
    _ = ∑' n : ℕ, kernelCoeff s s' n := tsum_congr fun n ↦ kernelArith_apply s s' n
    _ = recipKernel s s' := (recipKernel_eq_tsum_kernelCoeff hσ hs hs').symm

/-- **The Euler factorisation of the totient kernel** — the lemma's closing sentence,
derived rather than mirrored: the multiplicativity is
`Gap212.Sieve.isMultiplicative_kernelArithTotient`, the summability is the *totient* majorant of
`Gap212.Sieve.Polymath41MajorantTotient` (the reciprocal one does not dominate it), and the
local factor is `Gap212.Sieve.localFactorTotient`, which differs from the reciprocal one by
`1/p ↦ 1/(p-1)` — `Gap212.Sieve.localFactorTotient_eq_sub` quantifies the difference exactly. -/
theorem tprod_localFactorTotient_eq_totientKernel {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) :
    ∏' p : Nat.Primes,
        localFactorTotient ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))
      = totientKernel s s' := by
  calc _ = ∏' p : Nat.Primes, ∑' e : ℕ, kernelArithTotient s s' ((p : ℕ) ^ e) :=
        tprod_congr fun p ↦ (tsum_kernelArithTotient_prime_pow p.2 s s').symm
    _ = ∑' n : ℕ, kernelArithTotient s s' n :=
        (isMultiplicative_kernelArithTotient s s').eulerProduct_tprod <| by
          simpa only [kernelArithTotient_apply] using summable_norm_kernelCoeffTotient hσ hs hs'
    _ = ∑' n : ℕ, kernelCoeffTotient s s' n :=
        tsum_congr fun n ↦ kernelArithTotient_apply s s' n
    _ = totientKernel s s' := (totientKernel_eq_tsum_kernelCoeffTotient hσ hs hs').symm

end Gap212.Sieve
