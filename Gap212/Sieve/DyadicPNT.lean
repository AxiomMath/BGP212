/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.BlockCount
public import Gap212.Sieve.MertensMoebiusSq
public import PrimeGapsTheory.NumberTheory.DyadicPNT

/-!
# The prime number theorem on a dyadic block

A proof of `Gap212.Sieve.PrimeNumberTheoremDyadic`. `PrimeGapsLib` proves the dyadic prime number
theorem with an explicit error term; this module derives from it the form the density condition of
`Gap212.Defs.RhoHypotheses` asks for.

## From the dependency's statement to the block

`PNT.primeCountingIoc_self_two_mul` says

    ∃ C N₀, ∀ N ≥ N₀, |π(N, 2N) - N / log N| ≤ C * N / (log N)^2,

a statement about the *half-open* interval `(N, 2N]` at a *natural* `N`. Its own input
`PNT.primeCounting` is proved from `PrimeNumberTheoremAnd.MediumPNT`.

`Gap212.Sieve.PrimeNumberTheoremDyadic` asks instead for `o(x / log x)` on the *closed* block
`Gap212.dyadic x = Finset.Icc ⌈x⌉₊ ⌊2x⌋₊` at a *real* `x`. Three differences separate the two:

* **the error shape.** `C N / (log N)^2 = (C / log N) * (N / log N)` and `C / log N → 0`, so the
  stronger `O` form gives the weaker `o` form once `x` is past `exp (4|C|/ε)`.
* **the index sets.** `Icc ⌈x⌉₊ ⌊2x⌋₊` is not `Ioc ⌈x⌉₊ (2⌈x⌉₊)`. At the bottom the closed interval
  keeps `⌈x⌉₊` itself, which the half-open one drops; at the top `2⌈x⌉₊` overshoots `⌊2x⌋₊` by at
  most two, since `2x ≤ 2⌈x⌉₊ < 2x + 2` and `2x - 1 < ⌊2x⌋₊ ≤ 2x`. The two counts therefore differ
  by at most `2`, which is `Gap212.Sieve.abs_sum_sub_primeCountingIoc_le`. The `O(1)` discrepancy
  is absorbed into `ε x / log x` by `Gap212.Sieve.sqrt_div_two_le_div_log`.
* **the main term.** `N / log N` at `N = ⌈x⌉₊` is not `x / log x`. The difference is at most
  `2 / log x` by `Gap212.Sieve.abs_ceil_div_log_sub_le`, the `log` gap being controlled by
  `log (⌈x⌉₊ / x) ≤ ⌈x⌉₊ / x - 1 ≤ 1 / x`.

The elementary half — that the sum of `1_ℙ` over the block is a difference of `π'` — is
`Gap212.Sieve.sum_primeIndicatorReal_dyadic`, in `Gap212.Sieve.BlockCount`.

## Main results

* `Gap212.Sieve.dyadic_endpoints`: the three off-by-one facts relating `⌈x⌉₊`, `⌊2x⌋₊` and `2⌈x⌉₊`.
* `Gap212.Sieve.abs_sum_sub_primeCountingIoc_le`: the block count is the half-open count up to `2`.
* `Gap212.Sieve.abs_ceil_div_log_sub_le`: replacing `x` by `⌈x⌉₊` in the main term costs
  `2 / log x`.
* `Gap212.Sieve.primeNumberTheoremDyadic`: `Gap212.Sieve.PrimeNumberTheoremDyadic`.
-/

@[expose] public section

namespace Gap212.Sieve

open Real

/-! ## Two crude facts about the logarithm -/

/-- `log x ≥ 1` for `x ≥ 3`, since `e < 3`. -/
theorem one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- **`x / log x` grows at least like `√x / 2`.** This is what absorbs an `O(1)` discrepancy into
`ε x / log x`: an absolute constant is eventually below `(ε/2) (x / log x)` because the right-hand
side is eventually above `(ε/2) (√x / 2)`. -/
theorem sqrt_div_two_le_div_log {x : ℝ} (hx : 3 ≤ x) : Real.sqrt x / 2 ≤ x / Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have heq : x / (2 * Real.sqrt x) = Real.sqrt x / 2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    nlinarith [Real.sq_sqrt hx0.le]
  rw [← heq]
  exact div_le_div_of_nonneg_left hx0.le (by linarith [one_le_log hx]) (log_le_two_mul_sqrt hx0)

/-! ## Reconciling the index sets -/

/-- **`π'` increases by at most one per step.** Over a gap of `k` it increases by at most `k`,
which is the only thing needed to bound the primes the two intervals disagree about. -/
theorem primeCounting'_add_le_add (a k : ℕ) :
    Nat.primeCounting' (a + k) ≤ Nat.primeCounting' a + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.primeCounting', ← add_assoc, Nat.count_succ] at ih ⊢
    split_ifs <;> lia

/-- **The endpoint arithmetic.** For `x ≥ 1`: the block `Icc ⌈x⌉₊ ⌊2x⌋₊` is not mis-ordered, its
top end does not exceed `2⌈x⌉₊`, and `2⌈x⌉₊` overshoots it by at most `2`.

The overshoot is genuinely `2` and not `1`: `⌈x⌉₊ < x + 1` gives `2⌈x⌉₊ < 2x + 2`, while
`⌊2x⌋₊ > 2x - 1`, so the real bound is `2⌈x⌉₊ < ⌊2x⌋₊ + 3` and only integrality brings it to
`+2`. -/
theorem dyadic_endpoints {x : ℝ} (hx : 1 ≤ x) :
    ⌈x⌉₊ ≤ ⌊2 * x⌋₊ + 1 ∧ ⌊2 * x⌋₊ ≤ 2 * ⌈x⌉₊ ∧ 2 * ⌈x⌉₊ ≤ ⌊2 * x⌋₊ + 2 := by
  have hceil := Nat.le_ceil x
  have hceil' : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hfloor : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
  have hfloor' := Nat.lt_floor_add_one (2 * x)
  refine ⟨?_, ?_, Nat.lt_succ_iff.mp ?_⟩ <;> rify <;> linarith

/-- **The closed count and the half-open count differ by at most `2`.** Stated purely in terms of
two naturals `M` (standing for `⌊2x⌋₊`) and `N` (for `⌈x⌉₊`) satisfying the endpoint arithmetic.

`π(N, 2N) = π'(2N+1) - π'(N+1)` while the closed block gives `π'(M+1) - π'(N)`, so the discrepancy
is `(π'(M+1) - π'(2N+1)) + (π'(N+1) - π'(N))`: at most `2` lost at the top, where `2N` exceeds `M`
by at most `2`, and at most `1` gained at the bottom, where the closed interval keeps `N`
itself. -/
theorem abs_count_sub_primeCountingIoc_le {M N : ℕ} (h2 : M ≤ 2 * N) (h3 : 2 * N ≤ M + 2) :
    |((Nat.primeCounting' (M + 1) : ℝ) - (Nat.primeCounting' N : ℝ))
      - (Nat.primeCountingIoc N (2 * N) : ℝ)| ≤ 2 := by
  have hca : Nat.primeCounting' (2 * N + 1) ≤ Nat.primeCounting' (M + 1) + 2 := by
    have h := primeCounting'_add_le_add (M + 1) (2 * N - M)
    rw [show M + 1 + (2 * N - M) = 2 * N + 1 by lia] at h
    lia
  have hac : Nat.primeCounting' (M + 1) ≤ Nat.primeCounting' (2 * N + 1) :=
    Nat.monotone_primeCounting' (by lia)
  have hbd : Nat.primeCounting' N ≤ Nat.primeCounting' (N + 1) :=
    Nat.monotone_primeCounting' (by lia)
  have hdb := primeCounting'_add_le_add N 1
  rify at hca hac hbd hdb
  rw [Nat.cast_primeCountingIoc (by lia), Nat.primeCounting_eq_primeCounting'_succ,
    Nat.primeCounting_eq_primeCounting'_succ, abs_le]
  constructor <;> linarith

/-- **The block count is the half-open count of the dependency, up to `2` primes.** -/
theorem abs_sum_sub_primeCountingIoc_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ dyadic x, primeIndicatorReal n x)
      - (Nat.primeCountingIoc ⌈x⌉₊ (2 * ⌈x⌉₊) : ℝ)| ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := dyadic_endpoints hx
  rw [sum_primeIndicatorReal_dyadic h1]
  exact abs_count_sub_primeCountingIoc_le h2 h3

/-! ## Reconciling the main terms -/

/-- **Replacing `x` by `⌈x⌉₊` in the main term costs at most `2 / log x`.**

Writing `u = log x`, `v = log ⌈x⌉₊`, `n = ⌈x⌉₊`, the difference is `(n u - v x) / (v u)` with
`n u - v x = (n - x) u - x (v - u)`. The first summand is at most `u`, since `n - x ≤ 1`; the
second is between `0` and `1`, since `v - u = log (n / x) ≤ n / x - 1 ≤ 1 / x`. So the numerator is
at most `u + 1` in absolute value and the quotient at most `(u + 1) / u² ≤ 2 / u`. -/
theorem abs_ceil_div_log_sub_le {x : ℝ} (hx : 3 ≤ x) :
    |((⌈x⌉₊ : ℝ)) / Real.log (⌈x⌉₊ : ℝ) - x / Real.log x| ≤ 2 / Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hu : 1 ≤ Real.log x := one_le_log hx
  have hu0 : 0 < Real.log x := by linarith
  have hn1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hn2 : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0.le).le
  have hn0 : (0 : ℝ) < (⌈x⌉₊ : ℝ) := hx0.trans_le hn1
  have hv : Real.log x ≤ Real.log (⌈x⌉₊ : ℝ) := Real.log_le_log hx0 hn1
  have hv0 : 0 < Real.log (⌈x⌉₊ : ℝ) := hu0.trans_le hv
  have hgap : x * (Real.log (⌈x⌉₊ : ℝ) - Real.log x) ≤ 1 := by
    rw [← Real.log_div hn0.ne' hx0.ne']
    calc x * Real.log ((⌈x⌉₊ : ℝ) / x) ≤ x * ((⌈x⌉₊ : ℝ) / x - 1) := by
          gcongr; exact Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 1 := by rw [mul_sub, mul_div_cancel₀ _ hx0.ne']; linarith
  set u := Real.log x
  set v := Real.log (⌈x⌉₊ : ℝ)
  set n := ((⌈x⌉₊ : ℕ) : ℝ)
  rw [div_sub_div _ _ hv0.ne' hu0.ne', abs_div, abs_of_pos (by positivity : (0 : ℝ) < v * u)]
  have hnum : |n * u - v * x| ≤ u + 1 := by
    rw [show n * u - v * x = (n - x) * u - x * (v - u) by ring]
    exact abs_le.mpr ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hu0.le],
      by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hv)]⟩
  rw [div_le_div_iff₀ (by positivity) hu0]
  nlinarith [mul_le_mul_of_nonneg_right hnum hu0.le]

/-! ## The prime number theorem on a dyadic block -/

/-- **The prime number theorem on a dyadic block**, `Gap212.Sieve.PrimeNumberTheoremDyadic`.

Given `ε > 0`, the threshold is `max (max 3 N₀) (max (exp (4|C|/ε)) ((16/ε)^2))` for the `C` and
`N₀` of `PNT.primeCountingIoc_self_two_mul`. Above it the three reconciliations give

    |∑_{n ∈ 𝒟(x)} 1_ℙ(n) - x / log x| ≤ 2 + C ⌈x⌉₊ / (log ⌈x⌉₊)² + 2 / log x
                                     ≤ 4 + 2|C| x / (log x)²,

using `⌈x⌉₊ ≤ 2x` and `log ⌈x⌉₊ ≥ log x ≥ 1`, and the two remaining summands are each at most
`(ε/2) (x / log x)`: the constant `4` because `x / log x ≥ √x / 2 ≥ 8/ε`, and the error term
because `2|C| / log x ≤ ε/2` once `log x > 4|C|/ε`. -/
theorem primeNumberTheoremDyadic : PrimeNumberTheoremDyadic := by
  obtain ⟨C, N₀, hC⟩ := PNT.primeCountingIoc_self_two_mul
  intro ε hε
  refine ⟨max (max 3 (N₀ : ℝ)) (max (Real.exp (4 * |C| / ε)) ((16 / ε) ^ 2)), fun x hx ↦ ?_⟩
  obtain ⟨⟨hx3, hxN₀⟩, hxexp, hxsq⟩ := by simpa only [max_lt_iff] using hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL := one_le_log hx3.le
  have hL0 : 0 < Real.log x := by linarith
  -- the natural scale the dependency is stated at
  set N := ⌈x⌉₊
  have hn1 : x ≤ (N : ℝ) := Nat.le_ceil x
  have hn2 : (N : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0.le).le
  have hNv : Real.log x ≤ Real.log (N : ℝ) := Real.log_le_log hx0 hn1
  have hN₀ : N₀ ≤ N := by exact_mod_cast (hxN₀.trans_le hn1).le
  -- the dependency's error term, restated at `x`
  have hCbound : C * (N : ℝ) / Real.log (N : ℝ) ^ 2 ≤ 2 * |C| * x / Real.log x ^ 2 := by
    rw [show 2 * |C| * x = |C| * (2 * x) by ring]
    exact div_le_div₀ (by positivity)
      (mul_le_mul (le_abs_self C) (by linarith) (by positivity) (abs_nonneg C))
      (by positivity) (by gcongr)
  -- the three reconciliations: the total error is at most `4 + 2|C| x / (log x)²`
  have e₁ := abs_sum_sub_primeCountingIoc_le (x := x) (by linarith)
  have e₂ := (hC N hN₀).trans hCbound
  have e₃ := abs_ceil_div_log_sub_le hx3.le
  have hlogsmall : 2 / Real.log x ≤ 2 := by rw [div_le_iff₀ hL0]; linarith
  have t₁ := abs_sub_le (∑ n ∈ dyadic x, primeIndicatorReal n x)
    (Nat.primeCountingIoc N (2 * N) : ℝ) (x / Real.log x)
  have t₂ := abs_sub_le (Nat.primeCountingIoc N (2 * N) : ℝ) ((N : ℝ) / Real.log (N : ℝ))
    (x / Real.log x)
  -- and `4 + 2|C| x / (log x)² ≤ ε x / log x`
  have hA : (4 : ℝ) ≤ ε / 2 * (x / Real.log x) := by
    have hs : (16 / ε : ℝ) < Real.sqrt x := (Real.lt_sqrt (by positivity)).mpr hxsq
    have hsd := sqrt_div_two_le_div_log hx3.le
    calc (4 : ℝ) = ε / 2 * (16 / ε / 2) := by field_simp; norm_num
      _ ≤ ε / 2 * (x / Real.log x) := by gcongr ε / 2 * ?_; linarith
  have hB : 2 * |C| * x / Real.log x ^ 2 ≤ ε / 2 * (x / Real.log x) := by
    have h := (Real.lt_log_iff_exp_lt hx0).mpr hxexp
    rw [div_lt_iff₀ hε] at h
    rw [show 2 * |C| * x / Real.log x ^ 2 = 2 * |C| / Real.log x * (x / Real.log x) by ring]
    gcongr ?_ * _
    rw [div_le_iff₀ hL0]
    linarith
  linarith [show ε / 2 * (x / Real.log x) + ε / 2 * (x / Real.log x) = ε * x / Real.log x by ring]

end Gap212.Sieve
