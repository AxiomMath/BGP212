/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleTotientCoprime

/-!
# The closing sentence of the proof of Lemma 4.1, as an estimate

Polymath8b Lemma 4.1 disposes of the totient kernel in one sentence: "the only change that occurs
is that the `1/p` term in [`K_p`] is replaced by `1/(p-1)`; but this modification may be absorbed
into the `1+O(1/p²)` factor in [the Euler-factor estimate]".
`Gap212.Sieve.localFactorTotient_eq_sub` makes the first clause an exact identity,

  `localFactorTotient p u v = localFactorRecip p u v - (u+v-uv)/(p(p-1))`.

This file makes the second clause an estimate: that difference is bounded by `6/p²`, uniformly over
the whole region the sieve's exponents live in.

## Uniform in what

`‖u‖ ≤ 1` and `‖v‖ ≤ 1`, which at `u = p^{-s}`, `v = p^{-s'}` is exactly `Re s, Re s' ≥ 0`
(`Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_cpow_le`). The sieve uses
`s = (1+2πiξ)/log x` with `Re s = 1/log x > 0`, so the bound holds at every `ξ` and every `x > 1`
at once — there is no `ξ`-dependence and no `x`-dependence to lose.

## No oddness, and this time the arithmetic says so

The bound `3/(p(p-1)) ≤ 6/p²` holds at **every** prime including `p = 2`, where it reads
`3/2 ≤ 3/2` — an equality. So the totient kernel's per-prime cost over the reciprocal kernel is
summable over all primes with no prime excluded, and the source's "absorbed into the `1+O(1/p²)`"
is literally true rather than true-away-from-2. The `p = 2` obstruction of this kernel is elsewhere
entirely: it is the vanishing of the *limiting* local factor
(`Gap212.Sieve.localFactorTotient_two_one_one_eq_zero`), which no bound on a difference can see.

## What this is for

It is the per-prime input to the convergent correction product `∏_p (1 + O(1/p²))` of the totient
kernel; `Gap212.Sieve.summable_const_div_prime_sq` is the summability that product consumes.

## Main results

* `Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_le`: the difference of the two local
  factors is at most `3/(p(p-1))`, for `‖u‖, ‖v‖ ≤ 1`.
* `Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_le_sq`: hence at most `6/p²`.
* `Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_cpow_le`: the same at the sieve's own
  arguments `u = p^{-s}`, `v = p^{-s'}`, for `Re s, Re s' ≥ 0`.
* `Gap212.Sieve.summable_const_div_prime_sq`: `∑_p c/p² < ∞`, at any constant.
-/

@[expose] public section

namespace Gap212.Sieve

/-! ## The difference of the two local factors -/

/-- **The totient kernel's per-prime cost over the reciprocal kernel**: for a modulus
`p ≥ 2` and `‖u‖, ‖v‖ ≤ 1`,

  `‖localFactorTotient p u v - localFactorRecip p u v‖ ≤ 3/(p(p-1))`.

The difference is exactly `-(u+v-uv)/(p(p-1))` (`Gap212.Sieve.localFactorTotient_eq_sub`), so this
is the triangle inequality on a numerator of three terms and nothing more; the constant `3` is what
`‖u‖, ‖v‖ ≤ 1` gives and is not optimised. -/
theorem norm_localFactorTotient_sub_localFactorRecip_le {p : ℕ} (hp : 2 ≤ p) {u v : ℂ}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖localFactorTotient (p : ℂ) u v - localFactorRecip (p : ℂ) u v‖
      ≤ 3 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by lia)
  have hcast : ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  have hp1 : (p : ℂ) - 1 ≠ 0 := hcast ▸ Complex.ofReal_ne_zero.2 (by linarith)
  have hnum : ‖u + v - u * v‖ ≤ 3 := by
    linarith [norm_sub_le (u + v) (u * v), norm_add_le u v, norm_mul u v,
      mul_le_one₀ hu (norm_nonneg v) hv]
  rw [localFactorTotient_eq_sub hp0 hp1, sub_sub_cancel_left, norm_neg, norm_div, norm_mul,
    Complex.norm_natCast, hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
  exact (div_le_div_iff_of_pos_right (by nlinarith)).2 hnum

/-- **The source's `O(1/p²)`, with a constant**: the difference of the two local factors is at most
`6/p²` at every `p ≥ 2` and every `‖u‖, ‖v‖ ≤ 1`.

`3/(p(p-1)) ≤ 6/p²` is `2p ≤ p²`, so it holds at `p = 2` as well — with equality, `3/2 = 3/2`. The
totient kernel's price is therefore `O(1/p²)` at *every* prime, so the source's "absorbed into the
`1+O(1/p²)` factor" needs no prime excluded, and in particular this file has no oddness hypothesis.
The kernel's genuine `p = 2` obstruction is `Gap212.Sieve.localFactorTotient_two_one_one_eq_zero`,
which is a statement about the local factor
itself and not about this difference. -/
theorem norm_localFactorTotient_sub_localFactorRecip_le_sq {p : ℕ} (hp : 2 ≤ p) {u v : ℂ}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖localFactorTotient (p : ℂ) u v - localFactorRecip (p : ℂ) u v‖ ≤ 6 / (p : ℝ) ^ 2 := by
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  refine (norm_localFactorTotient_sub_localFactorRecip_le hp hu hv).trans ?_
  rw [div_le_div_iff₀ (by nlinarith : (0:ℝ) < (p : ℝ) * ((p : ℝ) - 1))
    (by nlinarith : (0:ℝ) < (p : ℝ) ^ 2)]
  nlinarith

/-! ## At the sieve's own exponents -/

/-- **The estimate at the kernel's own arguments.** For a prime `p` and exponents with non-negative
real part — which the sieve's `s = (1+2πiξ)/log x` has for every `ξ` and every `x > 1`, its real
part being `1/log x` (`Gap212.Sieve.kernelArg_re`) —

  `‖localFactorTotient p (p^{-s}) (p^{-s'}) - localFactorRecip p (p^{-s}) (p^{-s'})‖ ≤ 6/p²`.

So the two Euler products of
`Gap212.Sieve.tprod_localFactorTotient_eq_coprimeTotientKernel` and
`Gap212.Sieve.tprod_localFactorRecip_eq_coprimeRecipKernel` differ factor by factor by `O(1/p²)`,
uniformly in `(ξ,ξ')` and in `x`. This is the whole of what the totient kernel costs over the
reciprocal one in the source's proof. -/
theorem norm_localFactorTotient_sub_localFactorRecip_cpow_le {p : ℕ} (hp : p.Prime) {s s' : ℂ}
    (hs : 0 ≤ s.re) (hs' : 0 ≤ s'.re) :
    ‖localFactorTotient (p : ℂ) ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-s'))
        - localFactorRecip (p : ℂ) ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-s'))‖ ≤ 6 / (p : ℝ) ^ 2 := by
  have hnorm : ∀ z : ℂ, 0 ≤ z.re → ‖(p : ℂ) ^ (-z)‖ ≤ 1 := by
    intro z hz
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le) (by linarith)
  exact norm_localFactorTotient_sub_localFactorRecip_le_sq hp.two_le (hnorm s hs) (hnorm s' hs')

/-- **`∑_p c/p² < ∞` for every constant `c`** — the summability of a per-prime `O(1/p²)` cost, and
the input a convergent `∏_p (1 + O(1/p²))` consumes. It is the summability of `∑_n 1/n²` restricted
along the injection of the primes into `ℕ`, and it is stated at a general constant because the
constant is an artefact of whichever estimate produces the cost: `6` for
`Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_le_sq`, something else for the
reciprocal kernel's own Euler-factor error. No prime is excluded. -/
theorem summable_const_div_prime_sq (c : ℝ) :
    Summable fun p : Nat.Primes ↦ c / (((p : ℕ) : ℝ)) ^ 2 := by
  have hsum : Summable fun n : ℕ ↦ c / ((n : ℝ)) ^ 2 := by
    simpa only [div_eq_mul_inv, ← inv_pow, one_mul] using
      (Real.summable_one_div_nat_pow.2 one_lt_two).mul_left c
  exact hsum.comp_injective Nat.Primes.coe_nat_injective

end Gap212.Sieve
