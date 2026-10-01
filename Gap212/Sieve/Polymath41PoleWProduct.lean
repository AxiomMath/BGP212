/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Totient
public import PrimeGapsTheory.Arithmetic.RemovedPrimes

/-!
# Step 4c of Polymath8b Lemma 4.1: the finite product over `p ∣ W` is `(1+o(1))·φ(W)/W`

The kernel of Polymath8b Lemma 4.1 factorises over primes `p ∤ W` (`Gap212.Sieve.Polymath41Kernel`),
and completing it to a product over *all* primes — which is what identifies it with `ζ`, hence with
the pole of `Gap212.Sieve.Polymath41Pole` — costs a finite product over the primes dividing `W`. The
source's closing move is that this cost is asymptotically harmless:

  `∏_{p ∣ W} (1 - p^{-1-s}) = (1 + o(1)) · φ(W)/W`,   `s = (1 + iξ)/log x`.

This file proves it, quantitatively and for an arbitrary modulus `m` in place of `W`.

## The mechanism, and why `ellV` is the right error term

Write `Gap212.Sieve.wDensity m = ∏_{p ∣ m} (1 - 1/p)`, which *is* `φ(m)/m`
(`Gap212.Sieve.wDensity_eq_totient_div`), and `Gap212.Sieve.wTwistedProduct m s` for the twisted
product above. Factor prime by prime: since `p^{-1-s} = p^{-1}·p^{-s}`,

  `1 - p^{-1-s} = (1 - 1/p) · (1 + (1 - p^{-s})/(p-1))`

exactly (`Gap212.Sieve.one_sub_cpow_one_add_eq`), so the two products differ by
`∏_{p ∣ m} Gap212.Sieve.wRatio p s` and the whole question is how far that is from `1`. Each factor
is controlled by `‖1 - p^{-s}‖ = ‖1 - e^{-s log p}‖ ≤ 2‖s‖ log p` (Mathlib's
`Complex.norm_exp_sub_one_le`, valid once `‖s‖ log p ≤ 1`), giving

  `‖wRatio p s - 1‖ ≤ 2‖s‖ · log p/(p-1)`,

and *summing the right-hand side over `p ∣ m` gives exactly `2‖s‖·ellV m`* — the quantity
`PrimeGaps.ellV`, already in the library as `∑_{p ∣ m} log p/(p-1)`. So `ellV` is not a convenient
majorant chosen here; it is literally the sum this estimate produces. The passage from the
factorwise bounds to the product is `Gap212.Sieve.norm_prod_sub_one_le` together with
`1 + t ≤ e^t`, giving

  `‖∏_{p ∣ m} wRatio p s - 1‖ ≤ exp(2‖s‖·ellV m) - 1`

(`Gap212.Sieve.norm_prod_wRatio_sub_one_le`), which is the `o(1)` as soon as `‖s‖·ellV m → 0`.

## Where the `o(1)` comes from at `m = W(x)`

`Gap212.Sieve.ellV_le_log` (in `Gap212.Sieve.MertensMoebiusSq`) gives `ellV m ≤ log m`, so the
error is `exp(2‖s‖ log W) - 1`, and at `s = (1 + 2πiξ)/log x` with `|ξ| ≤ √(log x)` the modulus
`‖s‖` is `O((1 + √(log x))/log x)` (`Gap212.Sieve.norm_poleArg_le`, in
`Gap212.Sieve.Polymath41PoleUniform`) while `log W ≤ log log x` at the source's choice of `W`.
The product of those is `o(1)`. That final composition, a statement about `W(x)` specifically, is
`Gap212.Sieve.eventually_forall_norm_wTwistedProduct_div_sub_one_le`; this file is the estimate,
uniform in `m` and `s`, that it consumes. The same
`ellV m ≤ log m` also discharges the hypothesis:
`Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le'` asks only for `‖s‖ · log m ≤ 1`, one inequality
rather than one per prime.

## Main definitions

* `Gap212.Sieve.wDensity`: `∏_{p ∣ m} (1 - 1/p)`, i.e. `φ(m)/m`.
* `Gap212.Sieve.wTwistedProduct`: `∏_{p ∣ m} (1 - p^{-1-s})`, the completion cost.
* `Gap212.Sieve.wRatio`: the exact ratio of the two, prime by prime.

## Main results

* `Gap212.Sieve.wDensity_eq_totient_div`: `∏_{p ∣ m} (1 - 1/p) = φ(m)/m`.
* `Gap212.Sieve.wTwistedProduct_eq_mul`: the exact factorisation, with no error term.
* `Gap212.Sieve.norm_prod_sub_one_le`: `‖∏ f - 1‖ ≤ ∏ (1 + ‖f - 1‖) - 1`, for any finite product in
  a normed ring.
* `Gap212.Sieve.norm_wRatio_sub_one_le`: `‖wRatio p s - 1‖ ≤ 2‖s‖·log p/(p-1)`.
* `Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le`: the source's `(1+o(1))φ(W)/W`, with the
  `o(1)` named: `exp(2‖s‖·ellV m) - 1`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset

/-! ## The three products -/

/-- **`∏_{p ∣ m} (1 - 1/p)`**, the density the source writes as `φ(W)/W`; that identification is
`Gap212.Sieve.wDensity_eq_totient_div`. -/
noncomputable def wDensity (m : ℕ) : ℂ := ∏ p ∈ m.primeFactors, (1 - ((p : ℂ))⁻¹)

/-- **`∏_{p ∣ m} (1 - p^{-1-s})`**, the cost of completing the kernel's Euler product over `p ∤ W`
to a product over all primes. -/
noncomputable def wTwistedProduct (m : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + s)))

/-- **The exact ratio of the two local factors**, `(1 - p^{-1-s})/(1 - 1/p)`, written as `1 + δ`
with `δ = (1 - p^{-s})/(p-1)`. Writing it this way rather than as a quotient is what makes the
estimate a statement about `δ` alone, and `δ` is where the `log p/(p-1)` of `PrimeGaps.ellV` comes
from. -/
noncomputable def wRatio (p : ℕ) (s : ℂ) : ℂ := 1 + (1 - (p : ℂ) ^ (-s)) / ((p : ℂ) - 1)

/-- **`∏_{p ∣ m} (1 - 1/p) = φ(m)/m`**, in the cleared form `m · ∏ = φ(m)`. This is Mathlib's
`Nat.totient_eq_mul_prod_factors`, which is stated over `ℚ`, transported to `ℂ`. -/
theorem natCast_mul_wDensity (m : ℕ) : (m : ℂ) * wDensity m = (m.totient : ℂ) := by
  simpa [wDensity] using congr(($(Nat.totient_eq_mul_prod_factors m) : ℂ)).symm

/-- `∏_{p ∣ m} (1 - 1/p) = φ(m)/m`, as the source writes it. -/
theorem wDensity_eq_totient_div {m : ℕ} (hm : m ≠ 0) :
    wDensity m = (m.totient : ℂ) / (m : ℂ) := by
  rw [eq_div_iff (Nat.cast_ne_zero.2 hm), mul_comm, natCast_mul_wDensity]

/-! ## The exact factorisation -/

/-- **The local factorisation, exactly**: `1 - p^{-1-s} = (1 - 1/p)·wRatio p s`. No estimate yet —
this is an identity, from `p^{-1-s} = p^{-1}·p^{-s}`. -/
theorem one_sub_cpow_one_add_eq {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    1 - (p : ℂ) ^ (-(1 + s)) = (1 - ((p : ℂ))⁻¹) * wRatio p s := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by lia)
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (Nat.cast_ne_one.2 (by lia))
  rw [wRatio, show -(1 + s) = (-1 : ℂ) + -s by ring, Complex.cpow_add _ _ hp0,
    Complex.cpow_neg, Complex.cpow_one]
  field_simp
  ring

/-- **The two products differ by `∏ wRatio`**, exactly. -/
theorem wTwistedProduct_eq_mul (m : ℕ) (s : ℂ) :
    wTwistedProduct m s = wDensity m * ∏ p ∈ m.primeFactors, wRatio p s := by
  rw [wTwistedProduct, wDensity, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p hp ↦
    one_sub_cpow_one_add_eq (Nat.prime_of_mem_primeFactors hp).two_le s

/-- `∏_{p ∣ m} (1 - 1/p) ≠ 0`: every factor is `1 - 1/p` with `p ≥ 2`. -/
theorem wDensity_ne_zero (m : ℕ) : wDensity m ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hp ↦ sub_ne_zero.2 <| Ne.symm <|
    inv_ne_one.2 <| Nat.cast_ne_one.2 (Nat.prime_of_mem_primeFactors hp).ne_one

/-! ## Two lemmas about finite products -/

/-- **`‖∏ f - 1‖ ≤ ∏ (1 + ‖f - 1‖) - 1`.** The step from factorwise closeness to `1` to closeness
of the product; the induction needs `‖P‖ ≤ 1 + ‖P - 1‖` on the partial product, which is why the
bound is a product of `1 + ‖·‖` rather than a sum. -/
theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∏ i ∈ s, f i - 1‖ ≤ ∏ i ∈ s, (1 + ‖f i - 1‖) - 1 := by
  classical
  refine Finset.induction_on s (by simp) fun a t ha ih ↦ ?_
  rw [Finset.prod_insert ha, Finset.prod_insert ha]
  set P := ∏ i ∈ t, f i
  set Q := ∏ i ∈ t, (1 + ‖f i - 1‖)
  have hP : ‖P‖ ≤ Q := by linarith [norm_le_norm_add_norm_sub' P 1, norm_one (α := ℂ)]
  calc ‖f a * P - 1‖ = ‖(f a - 1) * P + (P - 1)‖ := by ring_nf
    _ ≤ ‖f a - 1‖ * ‖P‖ + ‖P - 1‖ := (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ (1 + ‖f a - 1‖) * Q - 1 := by nlinarith [norm_nonneg (f a - 1)]

/-- **`∏ (1 + g) ≤ exp(∑ g)`** for non-negative `g`, by `1 + t ≤ e^t` term by term. -/
theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) : ∏ i ∈ s, (1 + g i) ≤ Real.exp (∑ i ∈ s, g i) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun i hi ↦ by linarith [hg i hi]) fun i _ ↦ by
    linarith [Real.add_one_le_exp (g i)]

/-! ## The factorwise estimate, and `ellV` -/

/-- **`‖wRatio p s - 1‖ ≤ 2‖s‖·log p/(p-1)`.** The numerator is `‖1 - e^{-s log p}‖`, bounded by
`2‖s‖ log p` by `Complex.norm_exp_sub_one_le` as soon as `‖s‖ log p ≤ 1`; the denominator is
`‖p - 1‖ = p - 1`. The right-hand side is the summand of `PrimeGaps.ellV`, times `2‖s‖`. -/
theorem norm_wRatio_sub_one_le {p : ℕ} (hp : p.Prime) {s : ℂ}
    (h : ‖s‖ * Real.log p ≤ 1) :
    ‖wRatio p s - 1‖ ≤ 2 * ‖s‖ * (Real.log p / ((p : ℝ) - 1)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog := Real.log_natCast_nonneg p
  have hexp : (p : ℂ) ^ (-s) = Complex.exp (-((Real.log p : ℂ) * s)) := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg p)]
    ring_nf
  have hz : ‖-((Real.log p : ℂ) * s)‖ = ‖s‖ * Real.log p := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog, mul_comm]
  have hden : ‖(p : ℂ) - 1‖ = p - 1 := by
    rw [show (p : ℂ) - 1 = ((p - 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [wRatio, add_sub_cancel_left, norm_div, hden, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  rw [hexp, ← norm_neg, neg_sub]
  exact (Complex.norm_exp_sub_one_le (hz ▸ h)).trans_eq (by rw [hz]; ring)

/-- **The product estimate, with `PrimeGaps.ellV` as the error**:

  `‖∏_{p ∣ m} wRatio p s - 1‖ ≤ exp(2‖s‖·ellV m) - 1`.

The sum of the factorwise bounds of `Gap212.Sieve.norm_wRatio_sub_one_le` over `p ∣ m` is exactly
`2‖s‖·ellV m`, by the definition of `PrimeGaps.ellV`. -/
theorem norm_prod_wRatio_sub_one_le {m : ℕ} {s : ℂ}
    (h : ∀ p ∈ m.primeFactors, ‖s‖ * Real.log p ≤ 1) :
    ‖(∏ p ∈ m.primeFactors, wRatio p s) - 1‖
      ≤ Real.exp (2 * ‖s‖ * PrimeGaps.ellV m) - 1 := by
  refine (norm_prod_sub_one_le _ _).trans (sub_le_sub_right ?_ 1)
  rw [PrimeGaps.ellV, Finset.mul_sum]
  refine (Finset.prod_le_prod (fun p _ ↦ by positivity) fun p hp ↦ ?_).trans
    (prod_one_add_le_exp_sum _ _ fun p hp ↦ ?_)
  · linarith [norm_wRatio_sub_one_le (Nat.prime_of_mem_primeFactors hp) (h p hp)]
  · have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact mul_nonneg (by positivity) (div_nonneg (Real.log_natCast_nonneg p) (by linarith))

/-! ## The source's statement -/

/-- **The source's closing estimate**:

  `∏_{p ∣ m} (1 - p^{-1-s}) = (1 + o(1)) · φ(m)/m`,

with the `o(1)` named: the relative error is at most `exp(2‖s‖·ellV m) - 1`. At `m = W(x)` and
`s = (1 + 2πiξ)/log x` the exponent is `O((1 + √(log x))·log log x / log x) = o(1)`, which is what
makes this the source's `1 + o(1)`; see this file's module docstring. -/
theorem norm_wTwistedProduct_div_sub_one_le {m : ℕ} {s : ℂ}
    (h : ∀ p ∈ m.primeFactors, ‖s‖ * Real.log p ≤ 1) :
    ‖wTwistedProduct m s / wDensity m - 1‖ ≤ Real.exp (2 * ‖s‖ * PrimeGaps.ellV m) - 1 := by
  rw [wTwistedProduct_eq_mul, mul_comm, mul_div_assoc, div_self (wDensity_ne_zero m), mul_one]
  exact norm_prod_wRatio_sub_one_le h

/-- The same with the hypothesis in the form a consumer can discharge: one inequality,
`‖s‖·log m ≤ 1`, rather than one per prime divisor. Each `p ∣ m` has `log p ≤ log m`. -/
theorem norm_wTwistedProduct_div_sub_one_le' {m : ℕ} (hm : m ≠ 0) {s : ℂ}
    (h : ‖s‖ * Real.log m ≤ 1) :
    ‖wTwistedProduct m s / wDensity m - 1‖ ≤ Real.exp (2 * ‖s‖ * PrimeGaps.ellV m) - 1 := by
  refine norm_wTwistedProduct_div_sub_one_le fun p hp ↦ le_trans ?_ h
  have := (Nat.prime_of_mem_primeFactors hp).pos
  gcongr
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.dvd_of_mem_primeFactors hp)

/-- **The absolute form**:
`‖∏_{p ∣ m}(1 - p^{-1-s}) - φ(m)/m‖ ≤ (φ(m)/m)·(exp(2‖s‖·ellV m) - 1)`. -/
theorem norm_wTwistedProduct_sub_wDensity_le {m : ℕ} {s : ℂ}
    (h : ∀ p ∈ m.primeFactors, ‖s‖ * Real.log p ≤ 1) :
    ‖wTwistedProduct m s - wDensity m‖
      ≤ ‖wDensity m‖ * (Real.exp (2 * ‖s‖ * PrimeGaps.ellV m) - 1) := by
  rw [wTwistedProduct_eq_mul, ← mul_sub_one, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_prod_wRatio_sub_one_le h) (norm_nonneg _)

end Gap212.Sieve
