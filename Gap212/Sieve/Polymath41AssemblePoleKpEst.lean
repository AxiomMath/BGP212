/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleRecipCoprime
public import Gap212.Sieve.Polymath41PoleWProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The Euler-factor estimate as a convergent product

The source's Euler-factor estimate reads

  `K_p = (1 + O(1/p²)) · (1-p^{-1-s})(1-p^{-1-s'})/(1-p^{-1-s-s'})`,

and its next sentence, `∏_{p>w}(1+O(1/p²)) = 1+o(1)`, is what turns the Euler product of
`Gap212.Sieve.tprod_localFactorRecip_eq_coprimeRecipKernel` into a quotient of `ζ`-factors. This
file supplies both halves, quantitatively: the `O(1/p²)` is an explicit factor with an explicit
bound, and the product over primes of those factors converges.

## The factorisation is exact; only the bound is an estimate

`Gap212.Sieve.localFactorRecip_mul_one_sub` already gave the identity behind the Euler-factor
estimate with the error written out. Here it is turned into a *factorisation*: with

* `Gap212.Sieve.localFactorZeta p u v = (1-u/p)(1-v/p)/(1-uv/p)` the `ζ`-quotient factor, and
* `Gap212.Sieve.kpError p u v = 1 - uv(1-u)(1-v)/(p²(1-u/p)(1-v/p))` the correction,

`Gap212.Sieve.localFactorRecip_eq_localFactorZeta_mul_kpError` says
`K_p = localFactorZeta · kpError` as an identity in any field, given only that the three
denominators are nonzero. Nothing is estimated at that point.

The estimate is `Gap212.Sieve.norm_kpError_sub_one_le`:

  `‖kpError p u v - 1‖ ≤ 4‖1-u‖‖1-v‖/p²`   for `‖u‖, ‖v‖ ≤ 1` and `p ≥ 2`,

where the `4` is `1/((1-1/p)(1-1/p))` at its worst value `p = 2` — the only place the argument uses
`p ≥ 2` at all. Its crude corollary `Gap212.Sieve.norm_kpError_sub_one_le'` replaces `‖1-u‖‖1-v‖`
by `4`, giving the source's `O(1/p²)` with constant `16`; that is the form the convergence uses,
since `∑_p 1/p²` converges and no `s`-dependence is needed to make the tail small.

## Why the crude bound is enough for `1+o(1)`

The source writes `∏_{p>w}(1+O(1/p²)) = 1+o(1)`, and the `o(1)` is in `w`, **not** in `s`: it is
the tail of a convergent series. `Gap212.Sieve.norm_tprod_kpError_sub_one_le` is the quantitative
form, and it is uniform in `s, s'` over the whole half-plane `Re s, Re s' ≥ 0` — which is more than
the source needs and is what makes it usable under the `ξ`-integral with no extra care. Driving the
bound to `0` requires knowing that the primes *omitted* from the product are the small ones, which
is a statement about `W(x)`, made in `Gap212.Sieve.Polymath41AssemblePoleTail`.

## Main definitions

* `Gap212.Sieve.localFactorZeta`: the `ζ`-quotient factor of the Euler-factor estimate.
* `Gap212.Sieve.kpError`: its correction factor, the source's `1+O(1/p²)` made explicit.

## Main results

* `Gap212.Sieve.localFactorRecip_eq_localFactorZeta_mul_kpError`: the Euler-factor estimate as an
  exact factorisation.
* `Gap212.Sieve.norm_one_sub_natCast_cpow_le`: `‖1 - p^{-s}‖ ≤ 2‖s‖ log p`, extracted from
  `Gap212.Sieve.norm_wRatio_sub_one_le` rather than reproved.
* `Gap212.Sieve.norm_kpError_sub_one_le`, `Gap212.Sieve.norm_kpError_sub_one_le'`: the sharp and
  crude `O(1/p²)`.
* `Gap212.Sieve.multipliable_kpError`, `Gap212.Sieve.norm_tprod_kpError_sub_one_le`: the product of
  the corrections over **all** primes converges, with an explicit bound uniform in `s, s'`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset
open scoped ArithmeticFunction.Moebius

/-! ## The two factors of the Euler-factor estimate -/

/-- **The `ζ`-quotient factor of the Euler-factor estimate**: `(1-u/p)(1-v/p)/(1-uv/p)`, which at
`u = p^{-s}`, `v = p^{-s'}` is `(1-p^{-1-s})(1-p^{-1-s'})/(1-p^{-1-s-s'})`. Taken over `p ∤ W` this
is `ζ_W(1+s+s')/(ζ_W(1+s)ζ_W(1+s'))`. -/
noncomputable def localFactorZeta {K : Type*} [Field K] (p u v : K) : K :=
  (1 - u / p) * (1 - v / p) / (1 - u * v / p)

/-- **The correction factor of the Euler-factor estimate**, the source's `1+O(1/p²)` written out:

  `kpError p u v = 1 - uv(1-u)(1-v)/(p²(1-u/p)(1-v/p))`.

It is `1` when `u = 1` or `v = 1`, which is why the correction vanishes in the limit `s, s' → 0` at
each fixed prime, and it is `1+O(1/p²)` uniformly in `u, v` bounded by `1`
(`Gap212.Sieve.norm_kpError_sub_one_le'`). -/
noncomputable def kpError {K : Type*} [Field K] (p u v : K) : K :=
  1 - u * v * (1 - u) * (1 - v) / (p ^ 2 * ((1 - u / p) * (1 - v / p)))

/-- The field identity behind the factorisation: `(ab/c)·(1 - e/(P·ab)) = (ab - e/P)/c`. Stated on
its own because the nonvanishing hypotheses are then on the *atoms*, which is what lets
`field_simp` clear the denominators — applied directly to
`Gap212.Sieve.localFactorZeta`/`Gap212.Sieve.kpError` it cannot, since `1 - u/p ≠ 0` is not a
hypothesis about an atom. -/
theorem mul_one_sub_div_eq_sub_div {K : Type*} [Field K] {a b c e P : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hP : P ≠ 0) :
    a * b / c * (1 - e / (P * (a * b))) = (a * b - e / P) / c := by
  field_simp

/-- **The Euler-factor estimate as an exact factorisation**: `K_p = localFactorZeta · kpError`, an
identity in any field once the three denominators are nonzero. This is
`Gap212.Sieve.localFactorRecip_mul_one_sub` rearranged so that the `ζ`-quotient and the `O(1/p²)`
are separate factors rather than two sides of a cleared equation. -/
theorem localFactorRecip_eq_localFactorZeta_mul_kpError {K : Type*} [Field K] {p u v : K}
    (hp : p ≠ 0) (hu : 1 - u / p ≠ 0) (hv : 1 - v / p ≠ 0) (huv : 1 - u * v / p ≠ 0) :
    localFactorRecip p u v = localFactorZeta p u v * kpError p u v := by
  rw [localFactorZeta, kpError, mul_one_sub_div_eq_sub_div hu hv huv (pow_ne_zero 2 hp),
    ← localFactorRecip_mul_one_sub hp u v, mul_div_assoc, div_self huv, mul_one]

/-! ## The size of `1 - p^{-s}`, and the nonvanishing of the denominators -/

/-- **`‖1 - p^{-s}‖ ≤ 2‖s‖ log p`** once `‖s‖ log p ≤ 1`. Not reproved: it is
`Gap212.Sieve.norm_wRatio_sub_one_le` multiplied back up by `‖p - 1‖ = p - 1`, since
`wRatio p s - 1` is exactly `(1 - p^{-s})/(p-1)`. -/
theorem norm_one_sub_natCast_cpow_le {p : ℕ} (hp : p.Prime) {s : ℂ}
    (h : ‖s‖ * Real.log p ≤ 1) : ‖1 - (p : ℂ) ^ (-s)‖ ≤ 2 * ‖s‖ * Real.log p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdenC : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
    rw [← Nat.cast_pred hp.pos, Complex.norm_natCast, Nat.cast_pred hp.pos]
  have hmain : wRatio p s - 1 = (1 - (p : ℂ) ^ (-s)) / ((p : ℂ) - 1) := by rw [wRatio]; ring
  have hbase := norm_wRatio_sub_one_le hp h
  rwa [hmain, norm_div, hdenC, div_le_iff₀ hden, mul_div_assoc', div_mul_cancel₀ _ hden.ne']
    at hbase

/-- **`‖p^{-s}‖ ≤ 1` on the closed half-plane `Re s ≥ 0`**, for `p ≥ 1`. -/
theorem norm_natCast_cpow_neg_le_one {p : ℕ} (hp : 1 ≤ p) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by linarith)

/-- **The denominators of the Euler-factor estimate are nonzero on `‖u‖ ≤ 1`, `p ≥ 2`**:
`‖u/p‖ ≤ 1/p < 1`, so `1 - u/p` is at distance at least `1 - 1/p ≥ 1/2` from `0`. Stated as the
quantitative bound, from which the nonvanishing follows. -/
theorem half_le_norm_one_sub_div {p : ℕ} (hp : 2 ≤ p) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    1 / 2 ≤ ‖1 - u / (p : ℂ)‖ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hdiv : ‖u / (p : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_natCast, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith [norm_sub_norm_le (1 : ℂ) (u / p), norm_one (α := ℂ)]

/-! ## The `O(1/p²)` -/

/-- **The sharp Euler-factor bound**: for `p ≥ 2` and `‖u‖, ‖v‖ ≤ 1`,

  `‖kpError p u v - 1‖ ≤ 4‖1-u‖‖1-v‖/p²`.

The `4` is the worst value of `1/(‖1-u/p‖‖1-v/p‖)`, bounded through
`Gap212.Sieve.half_le_norm_one_sub_div`; that is the only use of `p ≥ 2`. The factor
`‖1-u‖‖1-v‖` is what vanishes as `s, s' → 0`. -/
theorem norm_kpError_sub_one_le {p : ℕ} (hp : 2 ≤ p) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖kpError (p : ℂ) u v - 1‖ ≤ 4 * (‖1 - u‖ * ‖1 - v‖) / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 := half_le_norm_one_sub_div hp hu
  have h2 := half_le_norm_one_sub_div hp hv
  have hsub : kpError (p : ℂ) u v - 1
      = -(u * v * (1 - u) * (1 - v)) / ((p : ℂ) ^ 2 * ((1 - u / (p : ℂ)) *
          (1 - v / (p : ℂ)))) := by
    rw [kpError]; ring
  have hnum : ‖-(u * v * (1 - u) * (1 - v))‖ ≤ ‖1 - u‖ * ‖1 - v‖ := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul, mul_assoc (‖u‖ * ‖v‖)]
    exact mul_le_of_le_one_left (by positivity) (mul_le_one₀ hu (norm_nonneg v) hv)
  have hden : (p : ℝ) ^ 2 / 4
      ≤ ‖(p : ℂ) ^ 2 * ((1 - u / (p : ℂ)) * (1 - v / (p : ℂ)))‖ := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
      show (p : ℝ) ^ 2 / 4 = p ^ 2 * (1 / 2 * (1 / 2)) by ring]
    gcongr
  rw [hsub, norm_div]
  calc _ ≤ ‖1 - u‖ * ‖1 - v‖ / ((p : ℝ) ^ 2 / 4) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 * (‖1 - u‖ * ‖1 - v‖) / (p : ℝ) ^ 2 := by ring

/-- **The crude Euler-factor bound**, the source's `O(1/p²)` with the constant named:

  `‖kpError p u v - 1‖ ≤ 16/p²`   for `‖u‖, ‖v‖ ≤ 1`, `p ≥ 2`.

This is `Gap212.Sieve.norm_kpError_sub_one_le` with `‖1-u‖ ≤ 2`. It carries no `s`-dependence at
all, which is exactly what makes the *tail* of the product small: the source's
`∏_{p>w}(1+O(1/p²)) = 1+o(1)` is an `o(1)` in `w`, not in `s`. -/
theorem norm_kpError_sub_one_le' {p : ℕ} (hp : 2 ≤ p) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖kpError (p : ℂ) u v - 1‖ ≤ 16 / (p : ℝ) ^ 2 := by
  have hb : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖1 - w‖ ≤ 2 := fun w hw ↦
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  calc _ ≤ 4 * (‖1 - u‖ * ‖1 - v‖) / (p : ℝ) ^ 2 := norm_kpError_sub_one_le hp hu hv
    _ ≤ 4 * (2 * 2) / (p : ℝ) ^ 2 := by gcongr; exacts [hb u hu, hb v hv]
    _ = 16 / (p : ℝ) ^ 2 := by norm_num

/-! ## The product of the corrections converges -/

/-- The bound of `Gap212.Sieve.norm_kpError_sub_one_le'` at the exponents the sieve produces. -/
theorem norm_kpError_cpow_sub_one_le (p : Nat.Primes) {s s' : ℂ} (hs : 0 ≤ s.re)
    (hs' : 0 ≤ s'.re) :
    ‖kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')) - 1‖
      ≤ 16 / ((p : ℕ) : ℝ) ^ 2 :=
  norm_kpError_sub_one_le' p.2.two_le
    (norm_natCast_cpow_neg_le_one p.2.one_lt.le hs)
    (norm_natCast_cpow_neg_le_one p.2.one_lt.le hs')

/-- **`∑_p 16/p²` converges.** The injection `Nat.Primes → ℕ` applied to `∑_n 1/n²`; nothing about
primes is used beyond injectivity, which is why the estimate needs no prime counting. -/
theorem summable_sixteen_div_prime_sq :
    Summable fun p : Nat.Primes ↦ 16 / ((p : ℕ) : ℝ) ^ 2 :=
  ((Real.summable_nat_pow_inv.2 one_lt_two).mul_left 16).comp_injective Subtype.val_injective

/-- The finite-product form of the source's `∏(1+O(1/p²))`, over any finite set of primes.
Mathlib's `Finset.norm_prod_one_add_sub_one_le` does the induction; the content is the factorwise
bound. -/
theorem norm_prod_kpError_sub_one_le (t : Finset Nat.Primes) {s s' : ℂ} (hs : 0 ≤ s.re)
    (hs' : 0 ≤ s'.re) :
    ‖(∏ p ∈ t, kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))) - 1‖
      ≤ Real.exp (∑ p ∈ t, 16 / ((p : ℕ) : ℝ) ^ 2) - 1 := by
  have h := Finset.norm_prod_one_add_sub_one_le t fun p : Nat.Primes ↦
    kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')) - 1
  simp only [add_sub_cancel] at h
  exact h.trans (sub_le_sub_right (Real.exp_le_exp.2
    (Finset.sum_le_sum fun p _ ↦ norm_kpError_cpow_sub_one_le p hs hs')) 1)

/-- **The product of the corrections over all primes converges**, for every `s, s'` in the closed
half-plane `Re ≥ 0`. This is what licenses reading the source's `∏_{p ∤ W} K_p` as a `ζ`-quotient
times a genuine infinite product rather than as a formal manipulation. -/
theorem multipliable_kpError {s s' : ℂ} (hs : 0 ≤ s.re) (hs' : 0 ≤ s'.re) :
    Multipliable fun p : Nat.Primes ↦
      kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')) := by
  simpa using multipliable_one_add_of_summable (f := fun p : Nat.Primes ↦
    kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')) - 1)
    (Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _)
      (fun p ↦ norm_kpError_cpow_sub_one_le p hs hs') summable_sixteen_div_prime_sq)

/-- **The quantitative `1 + o(1)` of the source's `∏(1+O(1/p²))`**, over all primes and uniform in
`s, s'` on `Re ≥ 0`:

  `‖∏'_p kpError_p - 1‖ ≤ exp(∑'_p 16/p²) - 1`.

Uniformity in `s, s'` is what lets the estimate be used under the `ξ`-integral. Making the
right-hand side *small* is a separate matter: it is the tail over the primes not dividing `W`, and
that is a statement about `W(x)`, not about this bound
(`Gap212.Sieve.eventually_forall_norm_tprod_coprimeKpError_sub_one_le`). -/
theorem norm_tprod_kpError_sub_one_le {s s' : ℂ} (hs : 0 ≤ s.re) (hs' : 0 ≤ s'.re) :
    ‖(∏' p : Nat.Primes,
        kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))) - 1‖
      ≤ Real.exp (∑' p : Nat.Primes, 16 / ((p : ℕ) : ℝ) ^ 2) - 1 := by
  refine le_of_tendsto ((continuous_norm.tendsto _).comp
    ((multipliable_kpError hs hs').hasProd.sub_const 1)) (Eventually.of_forall fun t ↦ ?_)
  exact (norm_prod_kpError_sub_one_le t hs hs').trans (sub_le_sub_right (Real.exp_le_exp.2
    (summable_sixteen_div_prime_sq.sum_le_tsum t fun p _ ↦ by positivity)) 1)

end Gap212.Sieve
